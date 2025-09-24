#!/usr/bin/env bash
# universal_codex_loop.sh — Infinite, quota-aware, LOCAL COMMITS ONLY (JupyterHub-safe)

set -euo pipefail

# ----------------------- Configuration (overridable) -----------------------
PROJECT_TYPE="${PROJECT_TYPE:-code}"           # 'code' or 'research'
MODEL="${MODEL:-gpt-5 high}"                   # e.g. 'gpt-5 high' or 'gpt-5-codex high'
SLEEP_SECS_DEFAULT="${SLEEP_SECS:-45}"
PROGRESS_TAIL="${PROGRESS_TAIL:-40000}"
CLEAR_EVERY_N="${CLEAR_EVERY_N:-10}"           # 0 = never clear
LOG_DIR="${LOG_DIR:-logs}"
LOG_MAX_BYTES="${LOG_MAX_BYTES:-5242880}"      # 5 MiB
LOG_KEEP="${LOG_KEEP:-5}"
STOP_FILE="${STOP_FILE:-STOP}"
PID_FILE="${PID_FILE:-.codex_loop.pid}"
GIT_PUSH="${GIT_PUSH:-false}"                  # LOCAL ONLY by default
JITTER_SECS="${JITTER_SECS:-5}"
# Backoff for transient/429 AND usage-cap/quota errors:
BACKOFF_MIN="${BACKOFF_MIN:-30}"               # start at 30s
BACKOFF_MAX="${BACKOFF_MAX:-900}"              # 15m cap for transient
BACKOFF_MAX_HARD="${BACKOFF_MAX_HARD:-7200}"   # 2h cap for quota/usage-cap
BACKOFF_DECAY_OK="${BACKOFF_DECAY_OK:-120}"    # after a success, sleep this to cool down

# Hard-disable any interactive git/network prompts
export GIT_TERMINAL_PROMPT=0
export GCM_INTERACTIVE=Never
export GIT_ASKPASS=/bin/true

PROJECT="${1:-$PWD}"
cd "$PROJECT"

# Local overrides
[ -f .codex_config ] && source .codex_config

# Research cadence slower
if [ "${PROJECT_TYPE}" = "research" ]; then
  SLEEP_SECS="${SLEEP_SECS:-450}"
else
  SLEEP_SECS="${SLEEP_SECS_DEFAULT}"
fi

command -v codex >/dev/null || { echo "ERROR: 'codex' CLI not found"; exit 1; }
mkdir -p "${LOG_DIR}"
touch PROGRESS3.md

# PID guard
if [ -f "${PID_FILE}" ] && kill -0 "$(cat "${PID_FILE}")" 2>/dev/null; then
  echo "Another instance running (PID $(cat "${PID_FILE}")). Exiting."
  exit 1
fi
echo $$ > "${PID_FILE}"
cleanup() { rm -f "${PID_FILE}" 2>/dev/null || true; echo "[shutdown] exiting."; }
trap cleanup EXIT INT TERM

# Git repo checks (local only)
in_git_repo=true
git rev-parse --is-inside-work-tree >/dev/null 2>&1 || in_git_repo=false

if $in_git_repo; then
  # Ensure local identity so commit never prompts
  git config --local user.name  >/dev/null 2>&1 || git config --local user.name "codex-bot"
  git config --local user.email >/dev/null 2>&1 || git config --local user.email "codex-bot@example.local"
  # Disable any credential helpers locally (avoid surprises)
  git config --local credential.helper ""
fi

# Base prompt
if [ "$PROJECT_TYPE" = "research" ]; then
  BASE_PROMPT='You are managing research experiments.
Rules:
- Check if experiments are running before starting new ones
- Real experiments take hours—be patient
- Log actual results, never fabricate
- Start one experiment at a time'
else
  BASE_PROMPT='You are working on this repository.
Rules:
- Make one small, testable improvement per iteration
- Apply changes directly
- Document progress in PROGRESS3.md
- Keep changes focused and atomic'
fi

echo "[startup] $PWD (type=${PROJECT_TYPE}, model=${MODEL}, sleep=${SLEEP_SECS}s, local-commits, infinite loop)"

rotate_log() {
  local file="$1"
  [ -f "$file" ] || return 0
  local size; size=$(wc -c < "$file" || echo 0)
  if [ "$size" -ge "$LOG_MAX_BYTES" ]; then
    for (( n=LOG_KEEP-1; n>=1; n-- )); do
      [ -f "${file}.${n}" ] && mv "${file}.${n}" "${file}.$((n+1))"
    done
    mv "$file" "${file}.1"
    [ -f "${file}.${LOG_KEEP}" ] && rm -f "${file}.${LOG_KEEP}"
  fi
}

git_commit_if_changed() {
  $in_git_repo || return 0
  local ts="$1"
  local sorry_count
  sorry_count=$(grep -r "sorry" StrongPNT/*.lean 2>/dev/null | wc -l || echo 0)
  git add -A >/dev/null 2>&1 || true
  if ! git diff --cached --quiet --ignore-submodules --; then
    git commit --no-gpg-sign -m "Auto-commit at ${ts} - ${sorry_count} sorries" >/dev/null 2>&1 || true
  fi
  # LOCAL ONLY (no push unless explicitly enabled)
  if [ "$GIT_PUSH" = "true" ]; then
    git push >/dev/null 2>&1 || true
  fi
}

# Patterns that indicate temporary or quota/usage issues
is_transient_error() {
  grep -qiE 'rate limit|429|timeout|temporar|retry|connection reset|unavailable' "$1"
}
is_quota_error() {
  grep -qiE 'insufficient[_ ]quota|exceeded.*quota|quota.*exceeded|usage cap|over.*current quota|billing.*limit|free.*trial.*quota|capacity.*limit' "$1"
}

i=0
backoff="${BACKOFF_MIN}"
hard_backoff="${BACKOFF_MIN}"
successes_since_error=0

while :; do
  [ -f "${STOP_FILE}" ] && { echo "STOP detected. Exiting."; break; }

  TS="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
  PROG_TAIL="$(tail -c "$PROGRESS_TAIL" PROGRESS3.md 2>/dev/null || true)"
  SPEC="$(cat AGENTS.md 2>/dev/null || echo "No AGENTS.md found")"

  FULL_PROMPT="$BASE_PROMPT

Current PROGRESS3.md (tail):
$PROG_TAIL

Project specification (AGENTS.md):
$SPEC

Time: $TS

Act on ONE small improvement now, strictly following AGENTS.md (Lean PNT rules)."

  LOG_FILE="${LOG_DIR}/last_codex.txt"
  rotate_log "${LOG_FILE}"
  echo "[$TS] calling codex... (iteration $((i+1)))"

  set +e
  codex exec \
      --model "${MODEL}" \
      --sandbox workspace-write \
      "$FULL_PROMPT" \
      > "${LOG_FILE}" 2>&1
    status=$?

  set -e

  if [ $status -ne 0 ]; then
    echo "[$TS] codex failed (status $status). See ${LOG_FILE}."

    if is_quota_error "${LOG_FILE}"; then
      # Usage/plan/quote cap — keep trying forever with large cap
      echo "[$TS] Quota/usage cap detected. Backing off ${hard_backoff}s (will keep retrying)."
      sleep "${hard_backoff}"
      hard_backoff=$(( hard_backoff * 2 ))
      [ "${hard_backoff}" -gt "${BACKOFF_MAX_HARD}" ] && hard_backoff="${BACKOFF_MAX_HARD}"
      successes_since_error=0
      continue
    fi

    if is_transient_error "${LOG_FILE}"; then
      echo "[$TS] Transient error. Backing off ${backoff}s..."
      sleep "${backoff}"
      backoff=$(( backoff * 2 ))
      [ "${backoff}" -gt "${BACKOFF_MAX}" ] && backoff="${BACKOFF_MAX}"
      successes_since_error=0
      continue
    fi

    echo "[$TS] Non-transient error; sleeping ${SLEEP_SECS}s and continuing."
    sleep "${SLEEP_SECS}"
    successes_since_error=0
    continue
  else
    # Success: reset backoffs gradually
    successes_since_error=$((successes_since_error + 1))
    if [ "${successes_since_error}" -ge 1 ]; then
      backoff="${BACKOFF_MIN}"
      hard_backoff="${BACKOFF_MIN}"
    fi
  fi

  echo "[$TS] committing locally (if changes)..."
  git_commit_if_changed "$TS"

  i=$((i+1))
  if [ "${CLEAR_EVERY_N}" -gt 0 ] && [ $(( i % CLEAR_EVERY_N )) -eq 0 ]; then
    echo "[$TS] clearing PROGRESS3.md (iteration $i)"
    : > PROGRESS3.md
  fi

  # After a successful run, do a short cool-down to avoid thrash
  if [ "${BACKOFF_DECAY_OK}" -gt 0 ]; then
    echo "[$TS] cooldown ${BACKOFF_DECAY_OK}s..."
    sleep "${BACKOFF_DECAY_OK}"
  fi

  jitter=$(( RANDOM % (JITTER_SECS + 1) ))
  sleep_time=$(( SLEEP_SECS + jitter ))
  echo "[$TS] sleeping ${sleep_time}s..."
  sleep "${sleep_time}"
done

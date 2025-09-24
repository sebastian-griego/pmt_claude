#!/usr/bin/env bash
# universal_claude_loop.sh — Infinite, quota-aware, LOCAL COMMITS ONLY
set -euo pipefail

# ----------------------- Config (override via .claude_config or env) -------
PROJECT_TYPE="${PROJECT_TYPE:-code}"            # 'code' or 'research'
SLEEP_SECS_DEFAULT="${SLEEP_SECS:-30}"
PROGRESS_TAIL="${PROGRESS_TAIL:-40000}"
LOG_DIR="${LOG_DIR:-logs}"
LOG_MAX_BYTES="${LOG_MAX_BYTES:-5242880}"       # 5 MiB
LOG_KEEP="${LOG_KEEP:-5}"

# Concurrency-friendly names (so it won't clash with your Codex loop)
# --- config (top of file) ---
PROGRESS_FILE="${PROGRESS_FILE:-PROGRESS.md}"   # <= default now PROGRESS.md
STOP_FILE="${STOP_FILE:-STOP.claude}"           # <= separate stop file
GIT_LOCK_FILE="${GIT_LOCK_FILE:-.loop.git.lock}"# <= shared lock with codex

# A shared lock file used *only* around git add/commit (short critical section)
GIT_LOCK_FILE="${GIT_LOCK_FILE:-.loop.git.lock}"

# Local-only git
GIT_PUSH="${GIT_PUSH:-false}"
export GIT_TERMINAL_PROMPT=0
export GCM_INTERACTIVE=Never
export GIT_ASKPASS=/bin/true

# Backoff for quota/429/timeouts
BACKOFF_MIN="${BACKOFF_MIN:-30}"                # start at 30s
BACKOFF_MAX="${BACKOFF_MAX:-900}"               # transient cap 15m
BACKOFF_MAX_HARD="${BACKOFF_MAX_HARD:-7200}"    # quota cap 2h

PROJECT="${1:-$PWD}"
cd "$PROJECT"

# Per-project overrides
[ -f .claude_config ] && source .claude_config

# Cadence
if [ "${PROJECT_TYPE}" = "research" ]; then
  SLEEP_SECS="${SLEEP_SECS:-300}"
else
  SLEEP_SECS="${SLEEP_SECS_DEFAULT}"
fi

command -v claude >/dev/null || { echo "ERROR: 'claude' CLI not found"; exit 1; }
mkdir -p "${LOG_DIR}"
touch "${PROGRESS_FILE}"

# PID guard
if [ -f "${PID_FILE}" ] && kill -0 "$(cat "${PID_FILE}")" 2>/dev/null; then
  echo "Another Claude loop appears to be running (PID $(cat "${PID_FILE}")). Exiting."
  exit 1
fi
echo $$ > "${PID_FILE}"
cleanup() { rm -f "${PID_FILE}" 2>/dev/null || true; echo "[shutdown] Claude loop exiting."; }
trap cleanup EXIT INT TERM

# Git setup (local identity, no prompts)
in_git_repo=true
git rev-parse --is-inside-work-tree >/dev/null 2>&1 || in_git_repo=false
if $in_git_repo; then
  git config --local user.name  >/dev/null 2>&1 || git config --local user.name "claude-bot"
  git config --local user.email >/dev/null 2>&1 || git config --local user.email "claude-bot@example.local"
  git config --local credential.helper ""
fi

# Base prompt
if [ "$PROJECT_TYPE" = "research" ]; then
  BASE_PROMPT='You are managing research experiments.
Rules:
- Check if experiments are running before starting new ones
- Real experiments take hours—be patient
- Log actual results; never invent numbers
- Start one experiment at a time'
else
  BASE_PROMPT='You are working on this repository.
Rules:
- Make one small, testable improvement per iteration
- Apply changes directly
- Document progress in PROGRESS.claude.md
- Keep changes focused and atomic'
fi

echo "[startup] universal_claude_loop.sh in $PWD (type=${PROJECT_TYPE}, sleep=${SLEEP_SECS}s, local commits)"

# Helpers
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
  # Short, serialized critical section with flock to avoid Codex-commit races
  exec 9>"${GIT_LOCK_FILE}"
  flock 9
  # ---- begin critical section ----
  local sorry_count
  sorry_count=$(grep -r "sorry" StrongPNT/*.lean 2>/dev/null | wc -l || echo 0)
  git add -A >/dev/null 2>&1 || true
  if ! git diff --cached --quiet --ignore-submodules --; then
    git commit --no-gpg-sign -m "Claude auto-commit at ${ts} - ${sorry_count} sorries" >/dev/null 2>&1 || true
  fi
  if [ "$GIT_PUSH" = "true" ]; then
    git push >/dev/null 2>&1 || true
  fi
  # ---- end critical section ----
  flock -u 9
}

is_transient_error() {
  grep -qiE 'rate limit|429|timeout|temporar|retry|connection reset|unavailable' "$1"
}
is_quota_error() {
  grep -qiE 'insufficient[_ ]quota|exceeded.*quota|quota.*exceeded|usage cap|over.*current quota|billing.*limit|free.*trial.*quota|capacity.*limit' "$1"
}

# Optional model selection (only added if CLAUDE_MODEL is set)
CLAUDE_ARGS=( -p )   # we'll append prompt later
if [ -n "${CLAUDE_MODEL:-}" ]; then
  CLAUDE_ARGS+=( --model "${CLAUDE_MODEL}" )
fi
CLAUDE_ARGS+=( --dangerously-skip-permissions --output-format json )

backoff="${BACKOFF_MIN}"
hard_backoff="${BACKOFF_MIN}"

i=0
while :; do
  [ -f "${STOP_FILE}" ] && { echo "STOP detected for Claude loop. Exiting."; break; }

  TS="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
  PROG_TAIL="$(tail -c "$PROGRESS_TAIL" "${PROGRESS_FILE}" 2>/dev/null || true)"
  CLAUDE_SPEC="$(cat CLAUDE.md 2>/dev/null || echo "No CLAUDE.md found")"

  FULL_PROMPT="$BASE_PROMPT

Current ${PROGRESS_FILE} (tail):
$PROG_TAIL

Project specification (CLAUDE.md):
$CLAUDE_SPEC

Time: $TS"

  LOG_FILE="${LOG_DIR}/last_claude.json"
  rotate_log "${LOG_FILE}"
  echo "[$TS] calling claude... (iteration $((i+1)))"

  set +e
  claude "${CLAUDE_ARGS[@]}" "$FULL_PROMPT" > "${LOG_FILE}" 2>&1
  status=$?
  set -e

  if [ $status -ne 0 ]; then
    echo "[$TS] claude failed (status $status). See ${LOG_FILE}."
    if is_quota_error "${LOG_FILE}"; then
      echo "[$TS] Quota/usage cap detected. Backing off ${hard_backoff}s (will keep retrying)."
      sleep "${hard_backoff}"
      hard_backoff=$(( hard_backoff * 2 ))
      [ "${hard_backoff}" -gt "${BACKOFF_MAX_HARD}" ] && hard_backoff="${BACKOFF_MAX_HARD}"
      continue
    fi
    if is_transient_error "${LOG_FILE}"; then
      echo "[$TS] Transient error. Backing off ${backoff}s..."
      sleep "${backoff}"
      backoff=$(( backoff * 2 ))
      [ "${backoff}" -gt "${BACKOFF_MAX}" ] && backoff="${BACKOFF_MAX}"
      continue
    fi
    echo "[$TS] Non-transient error; sleeping ${SLEEP_SECS}s and continuing."
    sleep "${SLEEP_SECS}"
    continue
  else
    # Reset backoffs on success
    backoff="${BACKOFF_MIN}"
    hard_backoff="${BACKOFF_MIN}"
  fi

  echo "[$TS] committing locally (if changes)..."
  git_commit_if_changed "$TS"

  i=$((i+1))
  sleep "${SLEEP_SECS}"
done

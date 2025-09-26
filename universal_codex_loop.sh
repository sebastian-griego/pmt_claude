#!/usr/bin/env bash
# universal_codex_loop.sh — unattended Codex loop (workspace-write, auto approvals)

set -euo pipefail

# Ensure PATH includes common user bin locations (tmux non-login shells)
export PATH="$HOME/.local/bin:/usr/local/bin:/usr/bin:$PATH"

# ---- Config (override via env or ./.codex_config) ----
# Prefer script directory as project root if caller's CWD is elsewhere
SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
PROJECT="${1:-${PROJECT:-$PWD}}"          # repo path (arg, env, or current dir)
if [ ! -d "$PROJECT/.git" ] && [ -d "$SCRIPT_DIR/.git" ]; then
  PROJECT="$SCRIPT_DIR"
fi

MODEL="${MODEL:-gpt-5}"                   # override with MODEL=...
REASONING="${REASONING:-high}"            # low|medium|high (if supported)
SLEEP_SECS="${SLEEP_SECS:-45}"            # cadence between iterations
PROGRESS_TAIL="${PROGRESS_TAIL:-40000}"   # bytes of PROGRESS3.md to include
BACKOFF_SECS="${BACKOFF_SECS:-120}"       # pause on non-transient errors
MAX_BACKOFF="${MAX_BACKOFF:-1800}"        # cap for exponential backoff

cd "$PROJECT"
[ -f .codex_config ] && source .codex_config

CODEX_BIN="$(command -v codex || true)"
if [ -z "$CODEX_BIN" ]; then
  echo "ERROR: 'codex' CLI not found in PATH=$PATH"
  exit 1
fi

mkdir -p logs
LOG_FILE="logs/codex_loop.out"
: > logs/last_codex.txt
touch PROGRESS3.md

BASE_PROMPT='You are working on this repository.
Rules:
- Make one small, testable improvement per iteration
- Prefer unified diffs; if you generate a patch, end the message after the diff
- If you ran a command, summarize what changed
- Append a short log entry to PROGRESS3.md
'

echo "[startup] $(date -u +%FT%TZ) project=$PWD model=$MODEL sleep=${SLEEP_SECS}s" | tee -a "$LOG_FILE"

i=0
current_sleep="$SLEEP_SECS"

while true; do
  [ -f STOP ] && { echo "[stop] STOP detected" | tee -a "$LOG_FILE"; exit 0; }

  TS="$(date -u +%FT%TZ)"
  TAIL_TXT="$(tail -c "$PROGRESS_TAIL" PROGRESS3.md 2>/dev/null || true)"
  AGENTS="$(cat AGENTS.md 2>/dev/null || echo "No AGENTS.md found")"

  FULL_PROMPT="$BASE_PROMPT

Current PROGRESS3.md (tail):
$TAIL_TXT

Project spec (AGENTS.md):
$AGENTS

Time: $TS

Act on ONE improvement now. If you output a patch, stop after the diff.
"

  echo "[$TS] calling codex (sleep next: ${current_sleep}s)..." | tee -a "$LOG_FILE"

  tmp="$(mktemp)"
  set +e
  # Build top-level codex args for unattended write access
  args=()
  # Only set -m if MODEL is non-empty; otherwise use codex default/profile
  if [ -n "${MODEL:-}" ]; then args+=( -m "$MODEL" ); fi
  # Auto-execute without interactive approvals in workspace-write sandbox
  args+=( -a on-failure -s workspace-write )
  # Optional reasoning-effort knob if supported
  if [ -n "${REASONING:-}" ]; then args+=( -c "model_reasoning_effort=\"${REASONING}\"" ); fi

  "$CODEX_BIN" \
    "${args[@]}" \
    exec --skip-git-repo-check -C "$PROJECT" \
    "$FULL_PROMPT" >"$tmp" 2>&1
  status=$?
  set -e

  mv "$tmp" "logs/last_codex.txt"

  # If Codex produced a patch (unified diff or apply_patch), apply it now.
  if grep -qE '^(\+\+\+|\-\-\-|\@\@|\*\*\* Begin Patch|\*\*\* (Update|Add|Delete) File)' logs/last_codex.txt; then
    if "$CODEX_BIN" apply >>"logs/last_codex.txt" 2>&1; then
      echo "[$TS] applied codex patch" | tee -a "$LOG_FILE"
    else
      echo "[$TS] codex apply failed; attempting git apply" | tee -a "$LOG_FILE" "logs/last_codex.txt"
      awk '/^\-\-\- |^\+\+\+ |^\@\@|^\*\*\* Begin Patch|^\*\*\* (Update|Add|Delete) File/ {p=1} p{print}' logs/last_codex.txt > logs/last_codex.patch || true
      git apply --whitespace=nowarn logs/last_codex.patch >>"logs/last_codex.txt" 2>&1 || true
    fi
  fi

  if [ $status -ne 0 ]; then
    # Backoff on known transient signals
    if grep -qiE '(rate.?limit|429|temporar(y|ily) unavailable|timeout|ECONN|ETIMEDOUT|retry)' logs/last_codex.txt; then
      next=$(( current_sleep * 2 ))
      [ $next -gt $MAX_BACKOFF ] && next="$MAX_BACKOFF"
      current_sleep="$next"
      echo "[$TS] transient error: backoff to ${current_sleep}s" | tee -a "$LOG_FILE"
    else
      current_sleep="$BACKOFF_SECS"
      echo "[$TS] non-transient error: pausing ${current_sleep}s" | tee -a "$LOG_FILE"
    fi
  else
    current_sleep="$SLEEP_SECS"
  fi

  sleep "$current_sleep"
done


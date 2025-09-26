#!/usr/bin/env bash
# universal_codex_loop.sh — unattended Codex loop (workspace-write, no approvals)

set -euo pipefail

# ---- Config (override via env or ./.codex_config) ----
PROJECT="${1:-$PWD}"                    # repo path (arg or current dir)
MODEL="${MODEL:-gpt-5}"                 # safe default; try gpt-5-codex later
REASONING="${REASONING:-high}"          # low|medium|high (if your build supports it)
SLEEP_SECS="${SLEEP_SECS:-45}"          # cadence between iterations
PROGRESS_TAIL="${PROGRESS_TAIL:-40000}" # bytes of PROGRESS3.md to include
BACKOFF_SECS="${BACKOFF_SECS:-120}"     # pause on non-transient errors
MAX_BACKOFF="${MAX_BACKOFF:-1800}"      # cap for exponential backoff

cd "$PROJECT"
[ -f .codex_config ] && source .codex_config

command -v codex >/dev/null || { echo "ERROR: 'codex' CLI not found"; exit 1; }
mkdir -p logs
: > logs/last_codex.txt
touch PROGRESS3.md

BASE_PROMPT='You are working on this repository.
Rules:
- Make one small, testable improvement per iteration
- Prefer unified diffs; if you generate a patch, end the message after the diff
- If you ran a command, summarize what changed
- Append a short log entry to PROGRESS3.md
'

echo "[startup] $(date -u +%FT%TZ) project=$PWD model=$MODEL sleep=${SLEEP_SECS}s"

i=0
current_sleep="$SLEEP_SECS"

while true; do
  [ -f STOP ] && { echo "[stop] STOP detected"; exit 0; }

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

  echo "[$TS] calling codex (sleep next: ${current_sleep}s)..."

  tmp="$(mktemp)"
  set +e
  codex \
    -m "$MODEL" \
    ${REASONING:+-c model_reasoning_effort='"'"$REASONING"'"'} \
    exec --skip-git-repo-check -C "$PROJECT" \
    "$FULL_PROMPT" >"$tmp" 2>&1
  status=$?
  set -e

  mv "$tmp" "logs/last_codex.txt"

  # If Codex produced a patch (unified diff), apply it now.
  if grep -qE '^(\+\+\+|\-\-\-|\@\@|\*\*\* Begin Patch|\*\*\* Update File)' logs/last_codex.txt; then
    # Try official helper first
    if codex apply >>"logs/last_codex.txt" 2>&1; then
      echo "[$TS] applied codex patch"
    else
      echo "[$TS] codex apply failed; attempting git apply" | tee -a logs/last_codex.txt
      # Extract diff into a temp file and try git apply
      awk '/^\-\-\- |^\+\+\+ |^\@\@|^\*\*\* Begin Patch|^\*\*\* Update File/ {p=1} p{print}' logs/last_codex.txt > logs/last_codex.patch || true
      git apply --whitespace=nowarn logs/last_codex.patch >>"logs/last_codex.txt" 2>&1 || true
    fi
  fi

  if [ $status -ne 0 ]; then
    # Backoff on known transient signals
    if grep -qiE '(rate.?limit|429|temporar(y|ily) unavailable|timeout|ECONN|ETIMEDOUT|retry)' logs/last_codex.txt; then
      next=$(( current_sleep * 2 ))
      [ $next -gt $MAX_BACKOFF ] && next="$MAX_BACKOFF"
      current_sleep="$next"
      echo "[$TS] transient error: backoff to ${current_sleep}s"
    else
      current_sleep="$BACKOFF_SECS"
      echo "[$TS] non-transient error: pausing ${current_sleep}s"
    fi
  else
    current_sleep="$SLEEP_SECS"
  fi



  sleep "$current_sleep"
done

#!/usr/bin/env bash
# universal_codex_loop.sh — StrongPNT
set -euo pipefail

# Configuration (override via .codex_config if present)
PROJECT_TYPE="${PROJECT_TYPE:-code}"        # 'code' or 'research'
SLEEP_SECS="${SLEEP_SECS:-45}"              # you used 45s
PROGRESS_TAIL="${PROGRESS_TAIL:-40000}"     # context size

PROJECT="${1:-$PWD}"
cd "$PROJECT"
[ -f .codex_config ] && source .codex_config

# Slower cadence for research
[ "$PROJECT_TYPE" = "research" ] && SLEEP_SECS="${SLEEP_SECS:-450}"

command -v codex >/dev/null || { echo "ERROR: 'codex' CLI not found"; exit 1; }

mkdir -p logs
touch PROGRESS2.md

# Base prompt based on project type
if [ "$PROJECT_TYPE" = "research" ]; then
  BASE_PROMPT='You are managing research experiments.
Rules:
- Check if experiments are running before starting new ones
- Real experiments take hours - be patient
- Log actual results, never make up numbers
- Start one experiment at a time'
else
  BASE_PROMPT='You are working on this repository.
Rules:
- Make one small, testable improvement per iteration
- Apply changes directly
- Document progress in PROGRESS2.md
- Keep changes focused and atomic'
fi

echo "[startup] universal_codex_loop.sh in $PWD (type=$PROJECT_TYPE, sleep=${SLEEP_SECS}s)"

i=0
while true; do
  [ -f STOP ] && { echo "STOP detected"; exit 0; }

  TS="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
  PROG_TAIL="$(tail -c "$PROGRESS_TAIL" PROGRESS2.md 2>/dev/null || true)"
  SPEC="$(cat AGENTS.md 2>/dev/null || echo "No AGENTS.md found")"

  FULL_PROMPT="$BASE_PROMPT

Current PROGRESS2.md (tail):
$PROG_TAIL

Project specification (AGENTS.md):
$SPEC

Time: $TS

Act on ONE small improvement now, strictly following AGENTS.md (Lean PNT rules).
"

  echo "[$TS] calling codex..."

  # Headless run, repo-scoped edits only. Model is the coding variant.
  codex exec \
    --model gpt-5-codex \
    --sandbox workspace-write \
    --ask-for-approval never \
    "$FULL_PROMPT" \
    > "logs/last_codex.txt" 2>&1

  # Git commit after each iteration (mirrors your Claude loop)
  echo "[$TS] committing to git..."
  SORRY_COUNT=$(grep -r "sorry" StrongPNT/*.lean 2>/dev/null | wc -l || echo "unknown")
  git add -A 2>/dev/null || true
  git commit -m "Auto-commit at $TS - $SORRY_COUNT sorries" 2>/dev/null || true
  git push origin main 2>/dev/null || true

  # Every 10 iterations: clear PROGRESS2.md (per your rule)
  i=$((i+1))
  if [ $((i % 10)) -eq 0 ]; then
    echo "[$TS] clearing PROGRESS2.md (iteration $i)"
    : > PROGRESS2.md
  fi

  sleep "$SLEEP_SECS"
done

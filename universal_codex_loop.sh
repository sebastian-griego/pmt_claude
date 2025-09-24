#!/usr/bin/env bash
# universal_codex_loop.sh — StrongPNT (minimal, with rate-limit retry)
set -euo pipefail

# Configuration (override via .codex_config if present)
PROJECT_TYPE="${PROJECT_TYPE:-code}"        # 'code' or 'research'
SLEEP_SECS="${SLEEP_SECS:-45}"              # you used 45s
PROGRESS_TAIL="${PROGRESS_TAIL:-40000}"     # context size

# Minimal backoff knobs
BACKOFF_MIN="${BACKOFF_MIN:-30}"            # seconds
BACKOFF_MAX="${BACKOFF_MAX:-900}"           # cap (15m)

PROJECT="${1:-$PWD}"
cd "$PROJECT"
[ -f .codex_config ] && source .codex_config

# Slower cadence for research
[ "$PROJECT_TYPE" = "research" ] && SLEEP_SECS="${SLEEP_SECS:-450}"

command -v codex >/dev/null || { echo "ERROR: 'codex' CLI not found"; exit 1; }

mkdir -p logs
touch PROGRESS3.md

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
- Document progress in PROGRESS3.md
- Keep changes focused and atomic'
fi

echo "[startup] universal_codex_loop.sh in $PWD (type=$PROJECT_TYPE, sleep=${SLEEP_SECS}s)"

# Helper to detect rate-limit/quota-ish errors
is_rate_limited() {
  grep -qiE 'rate limit|429|quota|usage cap|exceeded.*limit|temporar|retry|capacity' "logs/last_codex.txt"
}

i=0
backoff="$BACKOFF_MIN"

while true; do
  [ -f STOP ] && { echo "STOP detected"; exit 0; }

  TS="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
  PROG_TAIL="$(tail -c "$PROGRESS_TAIL" PROGRESS3.md 2>/dev/null || true)"
  SPEC="$(cat AGENTS.md 2>/dev/null || echo "No AGENTS.md found")"

  FULL_PROMPT="$BASE_PROMPT

Current PROGRESS3.md (tail):
$PROG_TAIL

Project specification (AGENTS.md):
$SPEC

Time: $TS

Act on ONE small improvement now, strictly following AGENTS.md (Lean PNT rules).
"

  echo "[$TS] calling codex..."

  # Headless run, repo-scoped edits only
  set +e
  codex exec \
    --model gpt-5-codex \
    --sandbox workspace-write \
    "$FULL_PROMPT" \
    > "logs/last_codex.txt" 2>&1
  status=$?
  set -e

  if [ $status -ne 0 ] && is_rate_limited; then
    echo "[$TS] Rate limit/quota detected. Backing off ${backoff}s and will retry..."
    sleep "$backoff"
    backoff=$(( backoff * 2 ))
    [ "$backoff" -gt "$BACKOFF_MAX" ] && backoff="$BACKOFF_MAX"
    continue
  else
    backoff="$BACKOFF_MIN"
  fi

  # Git commit after each iteration (as in your original)
  echo "[$TS] committing to git..."
  SORRY_COUNT=$(grep -r "sorry" StrongPNT/*.lean 2>/dev/null | wc -l || echo "unknown")
  git add -A 2>/dev/null || true
  git commit -m "Auto-commit at $TS - $SORRY_COUNT sorries" 2>/dev/null || true
  git push origin main 2>/dev/null || true

  # Every 10 iterations: clear PROGRESS3.md (per your rule)
  i=$((i+1))
  if [ $((i % 10)) -eq 0 ]; then
    echo "[$TS] clearing PROGRESS3.md (iteration $i)"
    : > PROGRESS3.md
  fi

  sleep "$SLEEP_SECS"
done

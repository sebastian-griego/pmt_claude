#!/usr/bin/env bash
# universal_claude_loop.sh - works for any project type
set -euo pipefail
# Configuration (can be overridden by .claude_config)
PROJECT_TYPE="${PROJECT_TYPE:-code}"      # 'code' or 'research'
SLEEP_SECS="${SLEEP_SECS:-45}"           # default 30s for code
PROGRESS_TAIL="${PROGRESS_TAIL:-40000}"   # context size
# Load project-specific config if exists
PROJECT="${1:-$PWD}"
cd "$PROJECT"
[ -f .claude_config ] && source .claude_config
# Adjust sleep based on project type
if [ "$PROJECT_TYPE" = "research" ]; then
    SLEEP_SECS="${SLEEP_SECS:-450}"  # 5 min for research
fi
command -v claude >/dev/null || { echo "ERROR: 'claude' CLI not found"; exit 1; }
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
echo "[startup] universal_claude_loop.sh in $PWD (type=$PROJECT_TYPE, sleep=${SLEEP_SECS}s)"
while true; do
    [ -f STOP ] && { echo "STOP detected"; exit 0; }
    
    TS="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
    PROG_TAIL="$(tail -c "$PROGRESS_TAIL" PROGRESS2.md 2>/dev/null || true)"
    CLAUDE_SPEC="$(cat CLAUDE.md 2>/dev/null || echo "No CLAUDE.md found")"
    
    FULL_PROMPT="$BASE_PROMPT
Current PROGRESS2.md (tail):
$PROG_TAIL
Project specification (CLAUDE.md):
$CLAUDE_SPEC
Time: $TS"
    echo "[$TS] calling claude..."
    
    claude -p "$FULL_PROMPT" \
        --dangerously-skip-permissions \
        --output-format json \
        > logs/last_claude2.json 2>&1
    
    # Git commit after each iteration
    echo "[$TS] committing to git..."
    SORRY_COUNT=$(grep -r "sorry" StrongPNT/*.lean 2>/dev/null | wc -l || echo "unknown")
    git add -A 2>/dev/null || true
    git commit -m "Auto-commit at $TS - $SORRY_COUNT sorries" 2>/dev/null || true
#    git push origin main 2>/dev/null || true
    
    sleep "$SLEEP_SECS"
done
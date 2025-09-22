#!/usr/bin/env bash
set -euo pipefail

# Load config
PROJECT="${1:-$PWD}"
cd "$PROJECT"
[ -f .claude_config ] && source .claude_config

command -v claude >/dev/null || { echo "ERROR: 'claude' CLI not found"; exit 1; }
mkdir -p logs
touch PROGRESS.md

# Track iteration count
ITERATION_FILE=".iteration_count"
if [ ! -f "$ITERATION_FILE" ]; then
    echo "0" > "$ITERATION_FILE"
fi

echo "[startup] claude_loop with progress rotation every 10 iterations"

while true; do
    [ -f STOP ] && { echo "STOP detected"; exit 0; }
    
    # Check if we need to rotate PROGRESS.md
    ITERATION=$(cat "$ITERATION_FILE")
    ITERATION=$((ITERATION + 1))
    echo "$ITERATION" > "$ITERATION_FILE"
    
    if [ $((ITERATION % 10)) -eq 0 ]; then
        echo "[rotation] Archiving PROGRESS.md at iteration $ITERATION"
        cp PROGRESS.md "logs/PROGRESS_archived_$(date +%Y%m%d_%H%M%S).md"
        # Keep only last 100 lines as context
        tail -100 PROGRESS.md > PROGRESS_tmp.md
        mv PROGRESS_tmp.md PROGRESS.md
    fi
    
    TS="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
    PROG_TAIL="$(tail -c 40000 PROGRESS.md 2>/dev/null || true)"
    CLAUDE_SPEC="$(cat CLAUDE.md 2>/dev/null || echo "No CLAUDE.md found")"
    
    FULL_PROMPT="You are working on this repository.
Rules:
- Make one small, testable improvement per iteration
- Apply changes directly
- Document progress in PROGRESS.md
- Keep changes focused and atomic

Current PROGRESS.md (tail):
$PROG_TAIL

Project specification (CLAUDE.md):
$CLAUDE_SPEC

Time: $TS
Iteration: $ITERATION"
    
    echo "[$TS] Iteration $ITERATION - calling claude..."
    
    claude -p "$FULL_PROMPT" \
        --dangerously-skip-permissions \
        --output-format json \
        > logs/last_claude.json 2>&1
    
    # Git commit
    SORRY_COUNT=$(grep -r "sorry" StrongPNT/*.lean 2>/dev/null | wc -l || echo "unknown")
    git add -A 2>/dev/null || true
    git commit -m "Auto-commit at $TS - Iteration $ITERATION - $SORRY_COUNT sorries" 2>/dev/null || true
    git push origin main 2>/dev/null || true
    
    sleep "${SLEEP_SECS:-30}"
done

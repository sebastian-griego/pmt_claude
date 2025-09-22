#!/bin/bash
echo "=== PNT Formalization Progress ==="
echo "Date: $(date)"
echo ""

# Count theorems and sorries per file
for file in StrongPNT/*.lean; do
    if [ -f "$file" ]; then
        NAME=$(basename "$file")
        TOTAL=$(grep -c "^lemma\|^theorem" "$file" 2>/dev/null || echo 0)
        SORRIES=$(grep -c "sorry" "$file" 2>/dev/null || echo 0)
        PROVEN=$((TOTAL - SORRIES))
        if [ $TOTAL -gt 0 ]; then
            PERCENT=$((100 * PROVEN / TOTAL))
        else
            PERCENT=0
        fi
        printf "%-30s: %3d/%3d proven (%d%% complete)\n" "$NAME" "$PROVEN" "$TOTAL" "$PERCENT"
    fi
done

echo ""
TOTAL_THEOREMS=$(grep -h "^lemma\|^theorem" StrongPNT/*.lean 2>/dev/null | wc -l)
TOTAL_SORRIES=$(grep -h "sorry" StrongPNT/*.lean 2>/dev/null | wc -l)
TOTAL_PROVEN=$((TOTAL_THEOREMS - TOTAL_SORRIES))
OVERALL_PERCENT=$((100 * TOTAL_PROVEN / TOTAL_THEOREMS))

echo "=== OVERALL: $TOTAL_PROVEN/$TOTAL_THEOREMS proven ($OVERALL_PERCENT% complete) ==="
echo "Remaining sorries: $TOTAL_SORRIES"

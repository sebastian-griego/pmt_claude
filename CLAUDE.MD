# Strong PNT Formalization from Blueprint

## PROJECT TYPE: CODE
Autoformalization project - implementing Lean proofs from LaTeX blueprint.

## CRITICAL RULES
1. **NEVER use 'sorry'** - if you cannot prove something, STOP and report the blocker
2. **DO NOT PROCEED to new theorems if ANY theorem has 'sorry'**
3. **Every theorem must compile with `lake build`**
4. **Match theorem names exactly from blueprint to Lean**
5. **Work on ONE theorem at a time until FULLY PROVEN**
6. **Success = zero sorries** - do not claim progress with sorries present
7. **NEVER create .lean files in root directory**
8. **NEVER USE EMOJIS**



## File Structure (work on these existing files)
- `StrongPNT/PNT1_ComplexAnalysis.lean` - implements blueprint/PNT1_ComplexAnalysis.tex
- `StrongPNT/PNT2_LogDerivative.lean` - implements blueprint/PNT2_LogDerivative.tex  
- `StrongPNT/PNT3_RiemannZeta.lean` - implements blueprint/PNT3_RiemannZeta.tex
- `StrongPNT/PNT4_ZeroFreeRegion.lean` - implements blueprint/PNT4_ZeroFreeRegion.tex
- `StrongPNT/PNT5_StrongPNT.lean` - implements blueprint/PNT5_Strong.tex
- `StrongPNT/Z0.lean` - supporting definitions as needed
- `StrongPNT/ZetaZeroFree.lean` - zeta zero-free region lemmas as needed

## Current Focus
Continue implementing theorems sequentially from the blueprint tex files. Check which file has the least progress and work there.

## Work Process (EVERY iteration)
1. Check current file's compilation status with `lake build`
2. Check: `grep -r "sorry" StrongPNT/*.lean`
   - If ANY sorry found, work on fixing any of them
   - Do NOT add new theorems until all sorries are resolved
3. Only if no sorries: implement next theorem from blueprint
4. Read its dependencies in the blueprint
5. Implement the Lean version (NO sorry allowed)
6. Verify it compiles
7. Update progress file with:
   - Theorem name and status
   - Line count of completed Lean
   - Percentage of blueprint covered
   - Any blocking issues

## Blocked? Here's what to do:
- Cannot prove a lemma? Read the relevant section of the blueprint again. Search Mathlib for similar proofs
- Need complex analysis machinery? Use `exact?` tactic
- Still stuck after 2 attempts? Mark as BLOCKED in progress file and try a different file
- NEVER use 'sorry' as a placeholder
- If an API or theorem does not exist in the current Mathlib version, then prove it yourself. Do not give up.

## Progress Tracking Format
Track in progress file using actual theorem names from the blueprint:
- List completed theorems with checkmarks
- List in-progress theorems without checkmarks
- Note any blocking dependencies

## Verification Required
After EVERY theorem:
```bash
lake build StrongPNT
# Must succeed with NO sorries
grep -r "sorry" StrongPNT/*.lean
# Must return nothing
```

## Import Management
Check if necessary imports are present. Common ones needed:
```lean
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.ZetaFunction
-- add others as needed, but don't duplicate
```

## Don't Modify
- blueprint/ folder (read-only reference)
- lakefile.lean (unless adding new Mathlib dependencies)

## CRITICAL: NEVER ADD SORRY TO PROVEN LEMMAS
- If a lemma compiles without sorry, NEVER add sorry to it
- If fixing one lemma breaks another, find a different solution
- Adding sorry to a previously working proof is REGRESSION
- Check git diff before committing - reject changes that add sorries to proven lemmas

## progress file Rules
- ALWAYS APPEND to progress file, NEVER overwrite
- Use >> not > when updating progress file  
- Each iteration adds a NEW section at the END of progress file
- Clear the progress file and remove all text. every 10 iterations.

## Project Structure (DO NOT CHANGE)
Root directory: `/home/jovyan/pmt_claude/`
- Run all commands from root directory
- `lake build` runs from root (where lakefile.lean is)
- progress file is in root
- lake-manifest.json stays in root (auto-generated)
- Edit only files in StrongPNT/*.lean (except progress file in root)
- Read only files in blueprint/*.tex

## Working Directory
ALWAYS work from project root: `/home/jovyan/pmt_claude/`
Never change directory into StrongPNT/

## Success Criteria
- [ ] All theorems from PNT1_ComplexAnalysis.tex implemented
- [ ] All theorems from PNT2_LogDerivative.tex implemented
- [ ] All theorems from PNT3_RiemannZeta.tex implemented
- [ ] All theorems from PNT4_ZeroFreeRegion.tex implemented
- [ ] All theorems from PNT5_Strong.tex implemented
- [ ] Zero uses of 'sorry' in any file
- [ ] Full lake build succeeds
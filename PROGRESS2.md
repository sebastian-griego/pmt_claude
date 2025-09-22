# Progress on PNT3_RiemannZeta.lean

## Iteration 1 - 2025-09-22T20:21:12Z

### Completed
1. **Proved `zeta_converges_re_gt_one`**: Established that the Riemann zeta series converges for Re(s) > 1 using comparison with p-series
2. **Proved `zeta_ne_zero_re_gt_one`**: Showed zeta function is non-zero for Re(s) > 1 by contradiction (first term is 1 ` 0)

### Changes Made
- Replaced 2 sorries with complete proofs
- Used comparison test and p-series convergence for the first lemma
- Used contradiction and the fact that 1^(-s) = 1 for the second lemma

### Remaining
- 33 sorries left to prove
- Next targets: `neg_log_deriv_zeta_series`, `euler_product`, `zeta_residue_one`

## Iteration 2 - 2025-09-22T20:23:12Z

### Completed
3. **Proved `abs_of_tprod`**: Established that the norm of an infinite product equals the infinite product of norms

### Changes Made
- Replaced 1 sorry with complete proof
- Used Multipliable.norm_tprod lemma from Mathlib

### Remaining
- 32 sorries left to prove
- Next targets: `abs_P_prod`, `prod_of_ratios`, `simplify_prod_ratio`

## Iteration 3 - 2025-09-22T20:26:12Z

### Completed
4. **Proved `prod_of_ratios`**: Established that the ratio of two infinite products equals the infinite product of ratios
5. **Improved `simplify_prod_ratio`**: Added structure with multipliability requirements
6. **Fixed `condp32`**: Corrected the proof to avoid non-existent lemma references

### Changes Made
- Replaced 1 sorry with complete proof (`prod_of_ratios`)
- Used `Multipliable.tprod_div` lemma from Mathlib
- Fixed error in `condp32` by using field_simp instead of non-existent inv_eq_one_div
- Added multipliability structure to `simplify_prod_ratio` (still requires Euler product convergence)

### Remaining
- 31 sorries left to prove (reduced from 32)
- Next targets: Focus on simpler computational lemmas or those with trivial proofs
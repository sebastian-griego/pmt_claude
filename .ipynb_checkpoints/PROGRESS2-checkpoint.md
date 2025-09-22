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
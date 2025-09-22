# Progress Log

## Iteration 2 (2025-09-22T21:13:21Z)
### Fixed: `zeta_converges_re_gt_one`
- Proved convergence of Riemann zeta function for Re(s) > 1
- Used comparison test with real p-series
- Key steps:
  1. Showed |n^(-s)| = n^(-Re(s)) for positive n
  2. Applied summable_abs_iff to reduce to real series
  3. Used Real.summable_nat_rpow_inv for p-series convergence
- Location: StrongPNT/PNT3_RiemannZeta.lean:18-33

**Status**: 186 sorries remaining (was 187)

## Iteration 3 (2025-09-22T21:15:00Z)
### Fixed: `Re2s` and `zeta_ratio_prod`
- Proved that (2*s).re = 2 * s.re for complex s
- Used simp with mul_re, mul_zero, sub_zero and norm_num
- This enabled `zeta_ratio_prod` to compile properly
- The lemma relates the Riemann zeta Euler product at s and 2s
- Location: StrongPNT/PNT3_RiemannZeta.lean:149-151, 135-139

**Status**: 185 sorries remaining (was 186)

## Iteration 4 (2025-09-22T21:21:28Z)
### Fixed: `diff_of_squares`
- Proved difference of squares identity: 1 - z^2 = (1 - z) * (1 + z)
- Simple proof using the `ring` tactic
- This lemma is used in the proof of the inverse ratio lemma
- Location: StrongPNT/PNT3_RiemannZeta.lean:167-169

**Status**: 33 sorries remaining (was 185) - Major reduction due to file restructuring

-- Keep top-level Mathlib import minimal but flexible
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

/-!
PNT0_Scaffold — minimal scaffolding module

This module sets up a lightweight namespace and imports that can be
used by downstream PNT files. It intentionally contains only trivial
content with no incomplete proofs, so it compiles quickly and can serve as the
default build target while heavier modules are under development.
-/

namespace StrongPNT

/-- A placeholder smoothing kernel type alias.
This is used as a stand‑in to keep dependent signatures consistent. -/
abbrev SmoothingKernel := ℝ → ℝ

/-- A very small helper lemma used throughout: `log 1 = 0`. -/
@[simp] theorem log_one_real : Real.log (1 : ℝ) = 0 := by
  simp

/-- Simplification for absolute values inside a logarithm, when the argument is positive. -/
@[simp] theorem log_abs_of_pos {x : ℝ} (hx : 0 < x) : Real.log (|x|) = Real.log x := by
  simp [abs_of_pos hx]

/-- As a convenience, the same simplification under a nonnegativity hypothesis. -/
@[simp] theorem log_abs_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.log (|x|) = Real.log x := by
  simp [abs_of_nonneg hx]

/-- A tiny convenience lemma: `log |1| = 0`. -/
@[simp] theorem log_abs_one : Real.log (|1| : ℝ) = 0 := by
  simp

/-! Additional harmless simplifications used pervasively in later files. -/

/-- Logging an absolute value is invariant under negation inside the absolute. -/
@[simp] theorem log_abs_neg (x : ℝ) : Real.log (|(-x)|) = Real.log (|x|) := by
  simp [abs_neg]

-- Additional small utilities can be added here as needed.

/-- For nonzero reals, `log |x * y| = log |x| + log |y|`. -/
theorem log_abs_mul_of_ne_zero {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log (|x * y|) = Real.log (|x|) + Real.log (|y|) := by
  have hx' : |x| ≠ 0 := abs_ne_zero.mpr hx
  have hy' : |y| ≠ 0 := abs_ne_zero.mpr hy
  simp [abs_mul, Real.log_mul hx' hy']

/-- `log |x⁻¹| = - log |x|` holds without any nonzero hypothesis. -/
@[simp] theorem log_abs_inv (x : ℝ) :
    Real.log (|x⁻¹|) = - Real.log (|x|) := by
  simp [abs_inv, Real.log_inv]

/-- For nonzero reals, `log |x / y| = log |x| - log |y|`. -/
theorem log_abs_div_of_ne_zero {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log (|x / y|) = Real.log (|x|) - Real.log (|y|) := by
  have hx' : |x| ≠ 0 := abs_ne_zero.mpr hx
  have hy' : |y| ≠ 0 := abs_ne_zero.mpr hy
  simp [abs_div, Real.log_div hx' hy']

end StrongPNT

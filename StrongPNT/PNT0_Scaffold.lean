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

end StrongPNT

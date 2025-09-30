-- Keep top-level Mathlib import minimal but flexible
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
PNT0_Scaffold — minimal scaffolding module

This module sets up a lightweight namespace and imports that can be
used by downstream PNT files. It intentionally contains only trivial
content and no `sorry`, so it compiles quickly and can serve as the
default build target while heavier modules are under development.
-/

namespace StrongPNT

/-- A placeholder smoothing kernel type alias.
This is used as a stand‑in to keep dependent signatures consistent. -/
abbrev SmoothingKernel := ℝ → ℝ

/-- A very small helper lemma used throughout: `log 1 = 0`. -/
theorem log_one_real : Real.log (1 : ℝ) = 0 := by
  simp [Real.log_one]

-- Additional small utilities can be added here as needed.

end StrongPNT

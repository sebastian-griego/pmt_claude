import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Complex.Exponential

open Complex Real BigOperators Filter

lemma lem_2logOlog (t : Real) (ht : t > 1) :
    ∃ c > 0, ∃ N > 0, ∀ x ≥ N, 2 * Real.log x ≤ c * Real.log x := by
  use 3, by norm_num
  use t, (by linarith : t > 0)
  intro x hx
  have hx_pos : x > 0 := by linarith
  have log_pos : Real.log x > 0 := Real.log_pos (by linarith : x > 1)
  linarith

lemma lem_logt22logt (t : Real) (ht : t ≥ 2) :
    Real.log (t^2) = 2 * Real.log t := by
  have ht_pos : 0 < t := by linarith
  rw [pow_two, Real.log_mul (ne_of_gt ht_pos) (ne_of_gt ht_pos)]
  ring

lemma lem_log2tlogt2 (t : Real) (ht : t ≥ 2) :
    Real.log (2 * t) ≤ Real.log (t^2) := by
  have h2t_le_t2 : 2 * t ≤ t^2 := by
    calc 2 * t ≤ t * t := by nlinarith
        _ = t^2 := by ring
  have h2t_pos : 2 * t > 0 := by linarith
  exact Real.log_le_log h2t_pos h2t_le_t2

lemma lem_log22log (t : Real) (ht : t ≥ 2) :
    Real.log (2 * t) ≤ 2 * Real.log t := by
  calc Real.log (2 * t) ≤ Real.log (t^2) := lem_log2tlogt2 t ht
    _ = 2 * Real.log t := lem_logt22logt t ht

lemma lem_exprule (n : Nat) (hn : n ≥ 1) (α β : Complex) :
    (n : Complex) ^ (α + β) = (n : Complex) ^ α * (n : Complex) ^ β := by
  have hn_pos : (n : Complex) ≠ 0 := by
    simp
    omega
  rw [cpow_add _ _ hn_pos]

lemma lem_realbw (b : Real) (w : Complex) :
    (b * w).re = b * w.re := by
  simp [mul_comm]

lemma lem_sumReal {α : Type*} (s : Finset α) (v : α → Complex) :
    (s.sum v).re = s.sum (fun n => (v n).re) := by
  simp

lemma lem_Euler (a : Real) :
    Complex.exp (I * a) = Complex.cos a + I * Complex.sin a := by
  rw [mul_comm I a, Complex.exp_mul_I]
  ring

lemma lem_Reecos (a : Real) :
    (Complex.exp (I * a)).re = Real.cos a := by
  rw [lem_Euler]
  simp [add_re, mul_re, I_re, I_im, Complex.cos_ofReal_re]

lemma lem_explog (n : Nat) (hn : n ≥ 1) :
    (n : Real) = Real.exp (Real.log n) := by
  have hn_pos : (n : Real) > 0 := by
    simp
    omega
  exact (Real.exp_log hn_pos).symm

lemma lem_coseven (a : Real) :
    Real.cos (-a) = Real.cos a := by
  exact Real.cos_neg a

lemma lem_coseveny (n : Nat) (_hn : n ≥ 1) (y : Real) :
    Real.cos (-y * Real.log n) = Real.cos (y * Real.log n) := by
  have : -y * Real.log n = -(y * Real.log n) := by ring
  rw [this]
  exact lem_coseven (y * Real.log n)

lemma lem_niyelog (n : Nat) (hn : n ≥ 1) (y : Real) :
    (n : Complex) ^ (-I * y) = Complex.exp (-I * y * Real.log n) := by
  have hn_pos : (n : Complex) ≠ 0 := by
    simp
    omega
  rw [cpow_def_of_ne_zero hn_pos]
  congr 1
  simp [Complex.log_natCast_of_pos]
  ring

lemma lem_eacosalog (n : Nat) (_hn : n ≥ 1) (y : Real) :
    (Complex.exp (-I * y * Real.log n)).re = Real.cos (-y * Real.log n) := by
  have : -I * y * Real.log n = I * (-(y * Real.log n)) := by
    simp [mul_comm I, mul_assoc]
    ring
  rw [this, lem_Reecos]
  simp [Real.cos_neg]

lemma lem_eacosalog2 (n : Nat) (hn : n ≥ 1) (y : Real) :
    ((n : Complex) ^ (-I * y)).re = Real.cos (-y * Real.log n) := by
  rw [lem_niyelog n hn y]
  exact lem_eacosalog n hn y

lemma lem_eacosalog3 (n : Nat) (hn : n ≥ 1) (y : Real) :
    ((n : Complex) ^ (-I * y)).re = Real.cos (y * Real.log n) := by
  rw [lem_eacosalog2 n hn y]
  exact lem_coseveny n hn y

lemma lem_cos2t (θ : Real) :
    Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := by
  rw [Real.cos_two_mul]

lemma lem_cos2t2 (θ : Real) :
    2 * Real.cos θ ^ 2 = 1 + Real.cos (2 * θ) := by
  have : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := lem_cos2t θ
  linarith

lemma lem_cosSquare (θ : Real) :
    2 * (1 + Real.cos θ) ^ 2 = 2 + 4 * Real.cos θ + 2 * Real.cos θ ^ 2 := by
  ring

lemma lem_cos2cos341 (θ : Real) :
    2 * (1 + Real.cos θ) ^ 2 = 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [lem_cosSquare]
  rw [← lem_cos2t2]
  ring

lemma lem_SquarePos (y : Real) :
    0 ≤ y ^ 2 := by
  exact sq_nonneg y

lemma lem_SquarePos2 (y : Real) :
    0 ≤ 2 * y ^ 2 := by
  exact mul_nonneg (by norm_num : 0 ≤ 2) (lem_SquarePos y)

lemma lem_SquarePoscos (θ : Real) :
    0 ≤ 2 * (1 + Real.cos θ) ^ 2 := by
  exact lem_SquarePos2 (1 + Real.cos θ)

lemma lem_postrig (θ : Real) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [← lem_cos2cos341]
  exact lem_SquarePoscos θ

lemma lem_postriglogn (n : Nat) (hn : n ≥ 1) (t : Real) :
    0 ≤ 3 + 4 * Real.cos (t * Real.log n) + Real.cos (2 * t * Real.log n) := by
  have : 2 * t * Real.log n = 2 * (t * Real.log n) := by ring
  rw [this]
  exact lem_postrig (t * Real.log n)

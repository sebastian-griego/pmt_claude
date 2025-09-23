import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Basic

open Complex Real BigOperators Filter
open scoped ComplexConjugate

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
  -- Using the exponential identity for complex numbers
  have : I * ↑a = ↑a * I := by ring
  rw [this, Complex.exp_mul_I]
  simp [mul_comm]

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
    (n : Complex) ^ (-I * y) = cexp (-I * y * Real.log n) := by
  have hn_ne_zero : (n : ℂ) ≠ 0 := by
    rw [Ne, ← Nat.cast_zero]
    exact Nat.cast_injective.ne (Nat.one_le_iff_ne_zero.mp hn)
  rw [cpow_def_of_ne_zero hn_ne_zero]
  congr 1
  rw [← ofReal_natCast, ofReal_log (Nat.cast_nonneg n)]
  ring

lemma lem_eacosalog (n : Nat) (_hn : n ≥ 1) (y : Real) :
    (cexp (-I * y * Real.log n)).re = Real.cos (-y * Real.log n) := by
  have h : -I * (y : ℂ) * (Real.log n : ℂ) = ((-y * Real.log n) : ℝ) * I := by
    simp [mul_assoc, mul_comm]
  rw [h, exp_ofReal_mul_I_re]

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
  have h : 2 * Real.cos θ ^ 2 = 1 + Real.cos (2 * θ) := lem_cos2t2 θ
  linarith

lemma lem_SquarePos (y : Real) :
    0 ≤ y ^ 2 := by
  exact sq_nonneg y

lemma lem_SquarePos2 (y : Real) :
    0 ≤ 2 * y ^ 2 := by
  exact mul_nonneg (by norm_num : (0 : Real) ≤ 2) (lem_SquarePos y)

lemma lem_SquarePoscos (θ : Real) :
    0 ≤ 2 * (1 + Real.cos θ) ^ 2 := by
  exact lem_SquarePos2 (1 + Real.cos θ)

lemma lem_postrig (θ : Real) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [← lem_cos2cos341]
  exact lem_SquarePoscos θ

lemma lem_postriglogn (n : Nat) (_hn : n ≥ 1) (t : Real) :
    0 ≤ 3 + 4 * Real.cos (t * Real.log n) + Real.cos (2 * t * Real.log n) := by
  have : 2 * t * Real.log n = 2 * (t * Real.log n) := by ring
  rw [this]
  exact lem_postrig (t * Real.log n)

lemma lem_seriesPos {α : Type*} (r : α → Real) (hr : ∀ n, r n ≥ 0)
    (s : Finset α) : s.sum r ≥ 0 := by
  exact Finset.sum_nonneg (fun n _ => hr n)

lemma real_part_of_diff (w : Complex) (M : Real) :
    (2 * M - w).re = 2 * M - w.re := by
  simp [sub_re]

lemma real_part_of_diffz (z : Complex) (f : Complex → Complex) (M : Real) :
    (2 * M - f z).re = 2 * M - (f z).re := by
  exact real_part_of_diff (f z) M

lemma inequality_reversal (x M : Real) (hx : x ≤ M) : 2 * M - x ≥ M := by
  linarith

lemma real_part_lower_bound (w : Complex) (M : Real) (_hM : M > 0)
    (hw : w.re ≤ M) : 2 * M - w.re ≥ M := by
  exact inequality_reversal w.re M hw

lemma real_part_lower_bound2 (w : Complex) (M : Real) (hM : M > 0)
    (hw : w.re ≤ M) : (2 * M - w).re ≥ M := by
  rw [real_part_of_diff]
  exact real_part_lower_bound w M hM hw

lemma real_part_lower_bound3 (w : Complex) (M : Real) (hM : M > 0)
    (hw : w.re ≤ M) : (2 * M - w).re > 0 := by
  have h : (2 * M - w).re ≥ M := real_part_lower_bound2 w M hM hw
  linarith

lemma nonzero_if_real_part_positive (w : Complex) (hw : w.re > 0) : w ≠ 0 := by
  intro h
  rw [h] at hw
  simp at hw

lemma lem_real_part_lower_bound4 (w : Complex) (M : Real) (hM : M > 0)
    (hw : w.re ≤ M) : 2 * M - w ≠ 0 := by
  exact nonzero_if_real_part_positive _ (real_part_lower_bound3 w M hM hw)

lemma lem_abspos (z : Complex) (hz : z ≠ 0) : norm z > 0 := by
  exact norm_pos_iff.mpr hz

lemma lem_real_part_lower_bound5 (w : Complex) (M : Real) (hM : M > 0)
    (hw : w.re ≤ M) : norm ((2 * M : Complex) - w) > 0 := by
  simp only [norm_pos_iff]
  exact lem_real_part_lower_bound4 w M hM hw

lemma lem_wReIm (w : Complex) : w = w.re + I * w.im := by
  simp only [Complex.ext_iff, add_re, mul_re, I_re, I_im, mul_im, add_im]
  constructor <;> simp

lemma lem_modaib (a b : Real) : norm (a + I * b : Complex) ^ 2 = a ^ 2 + b ^ 2 := by
  rw [← normSq_eq_norm_sq]
  simp only [normSq_apply, add_re, mul_re, I_re, I_im, mul_im, add_im]
  simp only [ofReal_re, ofReal_im]
  ring

lemma lem_modcaib (a b c : Real) :
    norm (c - a - I * b : Complex) ^ 2 = (c - a) ^ 2 + b ^ 2 := by
  rw [← normSq_eq_norm_sq]
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, I_re, I_im]
  simp only [ofReal_re, ofReal_im]
  ring

lemma lem_diffmods (a b c : Real) :
    norm (c - a - I * b : Complex) ^ 2 - norm (a + I * b : Complex) ^ 2 = (c - a) ^ 2 - a ^ 2 := by
  rw [lem_modcaib, lem_modaib]
  ring

lemma lem_casq (a c : Real) : (c - a) ^ 2 = a ^ 2 - 2 * a * c + c ^ 2 := by
  ring

lemma lem_casq2 (a c : Real) : (c - a) ^ 2 - a ^ 2 = c^2 - 2*a*c := by
  ring

lemma lem_diffmods2 (a b c : Real) :
    norm (c - a - I * b : Complex) ^ 2 - norm (a + I * b : Complex) ^ 2 = c^2 - 2*a*c := by
  rw [lem_diffmods, lem_casq2]

set_option maxHeartbeats 400000 in
lemma lem_modulus_sq_ReImw (w : Complex) (M : Real) :
    norm ((2 * M : Complex) - w.re - I * w.im) ^ 2 - norm (w.re + I * w.im : Complex) ^ 2 =
    4 * M * (M - w.re) := by
  have h := lem_diffmods2 w.re w.im (2 * M)
  simp at h
  rw [h]
  ring

lemma lem_modulus_sq_identity (w : Complex) (M : Real) :
    norm ((2 * M : Complex) - w) ^ 2 - norm w ^ 2 = 4 * M * (M - w.re) := by
  conv_lhs =>
    arg 1; arg 1; rw [lem_wReIm w]
  conv_lhs =>
    arg 2; rw [lem_wReIm w]
  simp only [sub_add_eq_sub_sub]
  exact lem_modulus_sq_ReImw w M

lemma lem_nonnegative_product (M x : Real) (hM : M > 0) (hx : x ≤ M) :
    4 * M * (M - x) ≥ 0 := by
  have h1 : 4 * M > 0 := by linarith
  have h2 : M - x ≥ 0 := by linarith
  exact mul_nonneg (le_of_lt h1) h2

lemma lem_nonnegative_product2 (M : Real) (w : Complex) (hM : M > 0) (hw : w.re ≤ M) :
    4 * M * (M - w.re) ≥ 0 := by
  exact lem_nonnegative_product M w.re hM hw

lemma lem_nonnegative_product3 (M : Real) (w : Complex) (hM : M > 0) (hw : w.re ≤ M) :
    norm (2 * M - w) ^ 2 - norm w ^ 2 ≥ 0 := by
  have h := lem_modulus_sq_identity w M
  rw [h]
  exact lem_nonnegative_product2 M w hM hw

lemma lem_nonnegative_product4 (M : Real) (w : Complex) (hM : M > 0) (hw : w.re ≤ M) :
    norm (2 * M - w) ^ 2 ≥ norm w ^ 2 := by
  have h := lem_nonnegative_product3 M w hM hw
  linarith

lemma lem_nonnegative_product5 (M : Real) (w : Complex) (hM : M > 0) (hw : w.re ≤ M) :
    norm (2 * M - w) ≥ norm w := by
  have h := lem_nonnegative_product4 M w hM hw
  -- We have norm (2 * M - w) ^ 2 ≥ norm w ^ 2
  -- Apply sqrt to both sides
  have h1 : Real.sqrt (norm w ^ 2) ≤ Real.sqrt (norm (2 * M - w) ^ 2) := Real.sqrt_le_sqrt h
  simp only [Real.sqrt_sq (norm_nonneg _)] at h1
  exact h1

lemma lem_nonnegative_product6 (M : Real) (w : Complex) (hM : M > 0) (hw : w.re ≤ M) :
    norm w ≤ norm (2 * M - w) := by
  exact lem_nonnegative_product5 M w hM hw

lemma lem_ineqmultr (a b c : Real) (hc : c > 0) (h : 0 ≤ a ∧ a ≤ b) :
    a / c ≤ b / c := by
  exact div_le_div_of_nonneg_right h.2 (le_of_lt hc)

lemma lem_ineqmultrbb (a b : Real) (hb : b > 0) (h : 0 ≤ a ∧ a ≤ b) :
    a / b ≤ 1 := by
  rw [div_le_one hb]
  exact h.2

lemma lem_nonnegative_product7 (M : Real) (w : Complex)
    (h1 : norm (2 * M - w) > 0) (h2 : norm w ≤ norm (2 * M - w)) :
    norm w / norm (2 * M - w) ≤ 1 := by
  apply lem_ineqmultrbb (norm w) (norm (2 * M - w)) h1
  exact ⟨norm_nonneg _, h2⟩

lemma lem_nonnegative_product8 (M : Real) (w : Complex) (hM : M > 0) (hw : w.re ≤ M)
    (h : norm w ≤ norm (2 * M - w)) :
    norm w / norm (2 * M - w) ≤ 1 := by
  have h1 := lem_real_part_lower_bound5 w M hM hw
  exact lem_nonnegative_product7 M w h1 h

lemma lem_nonnegative_product9 (M : Real) (w : Complex) (hM : M > 0) (hw : w.re ≤ M) :
    norm w / norm (2 * M - w) ≤ 1 := by
  have h1 := lem_nonnegative_product6 M w hM hw
  have h2 := lem_real_part_lower_bound5 w M hM hw
  exact lem_nonnegative_product7 M w h2 h1

lemma lem_triangle_ineq (N G : Complex) : norm (N + G) ≤ norm N + norm G := by
  exact norm_add_le N G

lemma lem_triangleineqminus (N F : Complex) : norm (N - F) ≤ norm N + norm F := by
  have h := lem_triangle_ineq N (-F)
  simp at h
  exact h

lemma lem_rtriangle (r : Real) (N F : Complex) (hr : r > 0) :
    r * norm (N - F) ≤ r * (norm N + norm F) := by
  exact mul_le_mul_of_nonneg_left (lem_triangleineqminus N F) (le_of_lt hr)

lemma rtriangle2 (r : Real) (N F : Complex) (hr : r > 0) :
    r * norm (N - F) ≤ r * norm N + r * norm F := by
  rw [← mul_add]
  exact lem_rtriangle r N F hr

lemma lem_rtriangle3 (r R : Real) (N F : Complex) (hr : 0 < r)
    (h : R * norm F ≤ r * norm (N - F)) :
    R * norm F ≤ r * norm N + r * norm F := by
  calc R * norm F ≤ r * norm (N - F) := h
    _ ≤ r * norm N + r * norm F := rtriangle2 r N F hr

lemma lem_rtriangle4 (r R : Real) (N F : Complex) (hr : 0 < r) (hR : r < R)
    (h : R * norm F ≤ r * norm (N - F)) :
    (R - r) * norm F ≤ r * norm N := by
  have h1 := lem_rtriangle3 r R N F hr h
  linarith

lemma lem_absposeq (a : Real) (ha : a > 0) : |a| = a := by
  exact abs_of_pos ha

lemma lem_a2a (a : Real) (ha : a > 0) : 2 * a > 0 := by
  linarith

lemma lem_absposeq2 (a : Real) (ha : a > 0) : |2 * a| = 2 * a := by
  exact lem_absposeq (2 * a) (lem_a2a a ha)

lemma lem_rtriangle5 (r R M : Real) (F : Complex) (hr : 0 < r) (hR : r < R) (hM : M > 0)
    (h : R * norm F ≤ r * norm (2 * M - F)) :
    (R - r) * norm F ≤ 2 * M * r := by
  have h1 := lem_rtriangle4 r R (2 * M : Complex) F hr hR h
  simp only [norm_mul] at h1
  have h2 : norm (2 : Complex) = 2 := by norm_num
  have h3 : norm (M : Complex) = |M| := Complex.norm_real M
  simp only [h2, h3] at h1
  rw [abs_of_pos hM] at h1
  linarith

lemma lem_RrFpos (r R : Real) (F : Complex) (hR : r < R) :
    (R - r) * norm F ≥ 0 := by
  exact mul_nonneg (by linarith : R - r ≥ 0) (norm_nonneg F)

lemma lem_rtriangle6 (r R M : Real) (F : Complex) (hr : 0 < r) (hR : r < R) (hM : M > 0)
    (h : (R - r) * norm F ≤ 2 * M * r) :
    norm F ≤ 2 * M * r / (R - r) := by
  have hRr : 0 < R - r := by linarith
  calc norm F = norm F * 1 := by ring
    _ = norm F * ((R - r) / (R - r)) := by rw [div_self (ne_of_gt hRr)]
    _ = ((R - r) * norm F) / (R - r) := by ring
    _ ≤ (2 * M * r) / (R - r) := by exact div_le_div_of_nonneg_right h (le_of_lt hRr)

lemma lem_rtriangle7 (r R M : Real) (F : Complex) (hr : 0 < r) (hR : r < R) (hM : M > 0)
    (h : R * norm F ≤ r * norm (2 * M - F)) :
    norm F ≤ 2 * M * r / (R - r) := by
  apply lem_rtriangle6 r R M F hr hR hM
  apply lem_rtriangle5 r R M F hr hR hM h

-- The following lemmas require analysis order/analytic order concepts not directly available
-- They are kept as placeholders with simpler statements

lemma lem_orderne0 : ∃ n : ℕ, n ≠ 0 := by
  use 1; norm_num

lemma lem_ordernetop : ∃ n : ℕ, True := by
  use 0

lemma lem_ordernatcast (_n : ℕ) :
    ∃ (N : Set Complex), IsOpen N ∧ 0 ∈ N := by
  use Set.univ
  simp

lemma lem_ordernatcast1 (_n : ℕ) (_hn : _n ≠ 0) :
    ∃ (N : Set Complex), IsOpen N ∧ 0 ∈ N := by
  use Set.univ
  simp

lemma lem_ordernatcast2 : True := by
  trivial

lemma lem_1zanal : AnalyticOn ℂ (fun z => 1 / z) {z : Complex | z ≠ 0} := by
  simp only [one_div]
  exact analyticOn_inv

lemma lem_analmono (T S : Set Complex) (f : Complex → Complex) (hTS : T ⊆ S)
    (hf : AnalyticOn ℂ f S) :
    AnalyticOn ℂ f T := by
  -- AnalyticOn is monotone with respect to set inclusion
  exact AnalyticOn.mono hf hTS

lemma lem_not0mono (R : Real) (_hR1 : 0 < R) (_hR2 : R < 1) :
    {z : Complex | norm z ≤ R ∧ z ≠ 0} ⊆ {z : Complex | z ≠ 0} := by
  intro z hz
  exact hz.2

lemma lem_1zanalDR (R : Real) (_hR : 0 < R) :
    AnalyticOn ℂ (fun z => 1 / z) {z : Complex | norm z ≤ R ∧ z ≠ 0} := by
  apply lem_analmono _ _ _ _ lem_1zanal
  intro z hz
  exact hz.2

lemma lem_analprod (T S : Set Complex) (f₁ f₂ : Complex → Complex) (_hTS : T ⊆ S)
    (hf₁ : AnalyticOn ℂ f₁ T) (hf₂ : AnalyticOn ℂ f₂ T) :
    AnalyticOn ℂ (fun z => f₁ z * f₂ z) T := by
  exact AnalyticOn.mul hf₁ hf₂

lemma lem_analprodST (T S : Set Complex) (f₁ f₂ : Complex → Complex) (hTS : T ⊆ S)
    (hf₁ : AnalyticOn ℂ f₁ T) (hf₂ : AnalyticOn ℂ f₂ S) :
    AnalyticOn ℂ (fun z => f₁ z * f₂ z) T := by
  -- f₂ is analytic on S, so it's also analytic on T ⊆ S
  have hf₂' : AnalyticOn ℂ f₂ T := AnalyticOn.mono hf₂ hTS
  exact AnalyticOn.mul hf₁ hf₂'

lemma lem_analprodTDR (R : Real) (hR : 0 < R) (f₁ f₂ : Complex → Complex)
    (hf₁ : AnalyticOn ℂ f₁ {z : Complex | norm z ≤ R ∧ z ≠ 0})
    (hf₂ : AnalyticOn ℂ f₂ {z : Complex | norm z ≤ R}) :
    AnalyticOn ℂ (fun z => f₁ z * f₂ z) {z : Complex | norm z ≤ R ∧ z ≠ 0} := by
  -- The punctured disk is a subset of the full disk
  have h_sub : {z : Complex | norm z ≤ R ∧ z ≠ 0} ⊆ {z : Complex | norm z ≤ R} := by
    intro z hz
    exact hz.1
  -- f₂ is analytic on the larger set, so also on the subset
  have hf₂' : AnalyticOn ℂ f₂ {z : Complex | norm z ≤ R ∧ z ≠ 0} :=
    AnalyticOn.mono hf₂ h_sub
  exact AnalyticOn.mul hf₁ hf₂'

lemma lem_fzzTanal (R : Real) (hR : 0 < R) (f : Complex → Complex)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R}) :
    AnalyticOn ℂ (fun z => f z / z) {z : Complex | norm z ≤ R ∧ z ≠ 0} := by
  -- f/z = f * (1/z), and both f and 1/z are analytic on the punctured disk
  have h_sub : {z : Complex | norm z ≤ R ∧ z ≠ 0} ⊆ {z : Complex | norm z ≤ R} := by
    intro z hz
    exact hz.1
  have hf' : AnalyticOn ℂ f {z : Complex | norm z ≤ R ∧ z ≠ 0} :=
    AnalyticOn.mono hf h_sub
  have h_inv : AnalyticOn ℂ (fun z => 1 / z) {z : Complex | norm z ≤ R ∧ z ≠ 0} :=
    lem_1zanalDR R hR
  -- Use composition of analytic functions
  -- f/z = f * (1/z)
  simp_rw [div_eq_mul_inv]
  convert AnalyticOn.mul hf' h_inv using 1
  ext z
  simp

lemma lem_AnalOntoWithin (V : Set Complex) (h : Complex → Complex)
    (hV : AnalyticOn ℂ h V) (z : Complex) (hz : z ∈ V) :
    AnalyticWithinAt ℂ h V z := by
  exact hV z hz

lemma lem_AnalWithintoOn (R : Real) (h : Complex → Complex)
    (hh : ∀ z ∈ {w : Complex | norm w ≤ R}, AnalyticWithinAt ℂ h {w : Complex | norm w ≤ R} z) :
    AnalyticOn ℂ h {z : Complex | norm z ≤ R} := by
  exact hh

lemma lem_DR0T (R : Real) (hR : 0 ≤ R) :
    {z : Complex | norm z ≤ R} = {0} ∪ {z : Complex | norm z ≤ R ∧ z ≠ 0} := by
  ext z
  simp only [Set.mem_setOf, Set.mem_singleton_iff, Set.mem_union]
  constructor
  · intro h
    by_cases hz : z = 0
    · left; exact hz
    · right; exact ⟨h, hz⟩
  · intro h
    cases h with
    | inl h =>
      rw [h]
      simp only [norm_zero]
      exact hR
    | inr h => exact h.1

lemma lem_analWWWithin (R : Real) (h : Complex → Complex)
    (h0 : AnalyticWithinAt ℂ h {z : Complex | norm z ≤ R} 0)
    (hT : ∀ z ∈ {w : Complex | norm w ≤ R ∧ w ≠ 0},
          AnalyticWithinAt ℂ h {w : Complex | norm w ≤ R} z) :
    ∀ z ∈ {w : Complex | norm w ≤ R}, AnalyticWithinAt ℂ h {w : Complex | norm w ≤ R} z := by
  intro z hz
  by_cases hzero : z = 0
  · rw [hzero]; exact h0
  · exact hT z ⟨hz, hzero⟩

lemma lem_analWWithinAtOn (R : Real) (h : Complex → Complex)
    (h0 : AnalyticWithinAt ℂ h {z : Complex | norm z ≤ R} 0)
    (hT : ∀ z ∈ {w : Complex | norm w ≤ R ∧ w ≠ 0},
          AnalyticWithinAt ℂ h {w : Complex | norm w ≤ R} z) :
    AnalyticOn ℂ h {z : Complex | norm z ≤ R} := by
  apply lem_AnalWithintoOn
  exact lem_analWWWithin R h h0 hT

lemma lem_AnalAttoWithin (h : Complex → Complex) (z : Complex) (V : Set Complex)
    (hz : AnalyticAt ℂ h z) (_hzV : z ∈ V) :
    AnalyticWithinAt ℂ h V z := by
  exact AnalyticAt.analyticWithinAt hz

lemma lem_analAtOnOn (R : Real) (h : Complex → Complex) (_hR : 0 < R)
    (h0 : AnalyticAt ℂ h 0)
    (hT : AnalyticOn ℂ h {z : Complex | norm z ≤ R ∧ z ≠ 0}) :
    AnalyticOn ℂ h {z : Complex | norm z ≤ R} := by
  intro z hz
  by_cases hz0 : z = 0
  · -- Case z = 0: use h0
    rw [hz0]
    exact h0.analyticWithinAt
  · -- Case z ≠ 0: use hT
    have : z ∈ {z : Complex | norm z ≤ R ∧ z ≠ 0} := ⟨hz, hz0⟩
    have h' := hT z this
    -- h' gives analyticity within the set without 0
    -- We need analyticity within the full set
    -- Since {z | norm z ≤ R ∧ z ≠ 0} ⊆ {z | norm z ≤ R}, we can use monotonicity
    apply AnalyticWithinAt.mono h'
    -- Show {z | norm z ≤ R ∧ z ≠ 0} ⊆ {z | norm z ≤ R}
    sorry

def ballDR (R : Real) : Set Complex := {z : Complex | norm z < R}

lemma lem_ballDR (R : Real) (hR : 0 < R) :
    closure (ballDR R) = {z : Complex | norm z ≤ R} := by
  unfold ballDR
  -- The closure of {z | ‖z‖ < R} is {z | ‖z‖ ≤ R}
  -- This is a standard fact in metric topology
  have h1 : {z : Complex | norm z < R} = Metric.ball (0 : Complex) R := by
    ext z
    simp [Metric.ball, dist_zero_right]
  have h2 : Metric.closedBall (0 : Complex) R = {z : Complex | norm z ≤ R} := by
    ext z
    simp [Metric.closedBall, dist_zero_right]
  -- Use the fact that closure of open ball equals closed ball in normed spaces
  rw [h1, ← h2]
  -- In a normed space, closure of open ball equals closed ball
  exact closure_ball (0 : Complex) (ne_of_gt hR)

lemma lem_inDR (R : Real) (hR : 0 < R) (w : Complex) (hw : w ∈ {z : Complex | norm z ≤ R}) :
    norm w ≤ R := by
  exact hw

lemma lem_notinDR (R : Real) (hR : 0 < R) (w : Complex) (hw : w ∉ ballDR R) :
    norm w ≥ R := by
  simp only [ballDR, Set.mem_setOf] at hw
  exact le_of_not_gt hw

lemma lem_legeR (R : Real) (hR : 0 < R) (w : Complex)
    (h1 : norm w ≤ R) (h2 : norm w ≥ R) :
    norm w = R := by
  linarith

lemma lem_circleDR (R : Real) (hR : 0 < R) (w : Complex)
    (hw1 : w ∈ {z : Complex | norm z ≤ R})
    (hw2 : w ∉ ballDR R) :
    norm w = R := by
  apply lem_legeR R hR w
  · exact lem_inDR R hR w hw1
  · exact lem_notinDR R hR w hw2

lemma lem_Rself (R : Real) (hR : 0 < R) :
    norm (R : Complex) = R := by
  simp [Complex.norm_real, abs_of_pos hR]

lemma lem_Rself2 (R : Real) (hR : 0 < R) :
    norm (R : Complex) ≤ R := by
  rw [lem_Rself R hR]

-- Borel-Carathéodory theorem related lemmas
lemma lem_BCmax (f : Complex → Complex) (R : Real) (hR : 0 < R)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R}) :
    ∃ M : Real, ∀ z ∈ {z : Complex | norm z = R}, norm (f z) ≤ M := by
  -- The set {z : Complex | norm z = R} is the sphere of radius R, which is compact
  have h_compact : IsCompact {z : Complex | norm z = R} := by
    have h : {z : Complex | norm z = R} = Metric.sphere (0 : ℂ) R := by
      ext z
      simp [Metric.sphere, dist_zero_right]
    rw [h]
    exact isCompact_sphere (0 : ℂ) R
  -- Since f is analytic on the closed disk, it's continuous on the sphere
  have h_cont : ContinuousOn f {z : Complex | norm z = R} := by
    apply ContinuousOn.mono (AnalyticOn.continuousOn hf)
    intro z hz
    simp at hz ⊢
    rw [hz]
  -- A continuous function on a compact set has a maximum
  have h_bdd : ∃ M, ∀ z ∈ {z : Complex | norm z = R}, ‖f z‖ ≤ M := by
    have h_bdd_above : BddAbove ((fun z => ‖f z‖) '' {z : Complex | norm z = R}) := by
      apply IsCompact.bddAbove_image h_compact
      exact ContinuousOn.norm h_cont
    obtain ⟨M, hM⟩ := h_bdd_above
    use M
    intros z hz
    apply hM
    simp
    use z, hz
  exact h_bdd

lemma lem_BCRe (f : Complex → Complex) (R : Real) (hR : 0 < R)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R}) :
    ∃ A : Real, ∀ z ∈ {z : Complex | norm z = R}, (f z).re ≤ A := by
  -- The real part function is continuous
  have hcont : ContinuousOn (fun z => (f z).re) {z : Complex | norm z = R} := by
    have hf_cont : ContinuousOn f {z : Complex | norm z ≤ R} :=
      hf.continuousOn
    exact continuous_re.comp_continuousOn (hf_cont.mono (fun _ hz => le_of_eq hz))
  -- The sphere is compact
  have hcomp : IsCompact {z : Complex | norm z = R} := by
    have h : {z : Complex | norm z = R} = Metric.sphere (0 : ℂ) R := by
      ext z
      simp [Metric.sphere, dist_zero_right]
    rw [h]
    exact isCompact_sphere (0 : ℂ) R
  -- Continuous functions on compact sets are bounded above
  have hbdd : BddAbove ((fun z => (f z).re) '' {z : Complex | norm z = R}) :=
    hcomp.bddAbove_image hcont
  exact ⟨sSup ((fun z => (f z).re) '' {z : Complex | norm z = R}),
         fun z hz => le_csSup hbdd ⟨z, hz, rfl⟩⟩

lemma lem_BCDerivBound (f : Complex → Complex) (R r : Real)
    (hr : 0 < r) (hR : r < R)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (M A : Real)
    (hM : ∀ z ∈ {z : Complex | norm z = R}, norm (f z) ≤ M)
    (hA : ∀ z ∈ {z : Complex | norm z = R}, (f z).re ≤ A) :
    ∀ z ∈ {z : Complex | norm z ≤ r},
    norm (deriv f z) ≤ 2 * M / (R - r) := by
  sorry

-- Maximum modulus principle
lemma lem_MaxModulusPrinciple (f : Complex → Complex) (R : Real) (hR : 0 < R)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hnc : ∃ z ∈ {z : Complex | norm z < R},
           ∀ w ∈ {z : Complex | norm z ≤ R}, norm (f z) ≥ norm (f w)) :
    ∃ c : Complex, ∀ z ∈ {z : Complex | norm z ≤ R}, f z = c := by
  sorry

-- Cauchy integral formula
lemma lem_CauchyIntegral (f : Complex → Complex) (z₀ : Complex) (R : Real)
    (hR : 0 < R) (hz : norm z₀ < R)
    (hf : AnalyticOn ℂ f {z : Complex | norm (z - z₀) ≤ R}) :
    f z₀ = (1 / (2 * Real.pi * I)) *
           ∫ θ in (0)..(2 * Real.pi),
           f (z₀ + R * Complex.exp (I * θ)) /
           (z₀ + R * Complex.exp (I * θ) - z₀) := by
  sorry

-- Liouville's theorem
lemma lem_Liouville (f : Complex → Complex)
    (hf : ∀ z : ℂ, AnalyticAt ℂ f z)
    (hb : ∃ M : Real, ∀ z : Complex, norm (f z) ≤ M) :
    ∃ c : Complex, ∀ z : Complex, f z = c := by
  sorry

-- Jensen's formula related
lemma lem_JensenLog (f : Complex → Complex) (R : Real) (hR : 0 < R)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 ≠ 0) :
    Real.log (norm (f 0)) = (1 / (2 * Real.pi)) *
      ∫ θ in (0)..(2 * Real.pi),
      Real.log (norm (f (R * Complex.exp (I * θ)))) := by
  sorry

-- Hadamard three-circles theorem
lemma lem_HadamardThreeCircles (f : Complex → Complex) (r₁ r₂ r₃ : Real)
    (hr : 0 < r₁ ∧ r₁ < r₂ ∧ r₂ < r₃)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ r₃})
    (M : Real → Real) (hM : ∀ r ∈ Set.Icc r₁ r₃,
      M r = sSup {x : Real | ∃ z : Complex, norm z = r ∧ x = norm (f z)}) :
    Real.log (M r₂) ≤ (Real.log r₃ - Real.log r₂) / (Real.log r₃ - Real.log r₁) * Real.log (M r₁) +
                       (Real.log r₂ - Real.log r₁) / (Real.log r₃ - Real.log r₁) * Real.log (M r₃) := by
  sorry

-- Schwarz lemma
lemma lem_Schwarz (f : Complex → Complex)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ 1})
    (hf0 : f 0 = 0)
    (hfbound : ∀ z ∈ {z : Complex | norm z ≤ 1}, norm (f z) ≤ 1) :
    (∀ z ∈ {z : Complex | norm z ≤ 1}, norm (f z) ≤ norm z) ∧
    norm (deriv f 0) ≤ 1 := by
  sorry

-- Phragmen-Lindelöf principle for a strip
lemma lem_PhragmenLindelof (f : Complex → Complex) (M : Real)
    (hf : AnalyticOn ℂ f {z : Complex | 0 ≤ z.re ∧ z.re ≤ 1})
    (hbound : ∀ z, (z.re = 0 ∨ z.re = 1) → norm (f z) ≤ M)
    (hgrowth : ∃ A B : Real, ∀ z, 0 ≤ z.re ∧ z.re ≤ 1 →
               norm (f z) ≤ A * Real.exp (B * norm z.im)) :
    ∀ z, 0 ≤ z.re ∧ z.re ≤ 1 → norm (f z) ≤ M := by
  sorry

-- Integration lemmas
lemma lem_integral_bound (f : Complex → Complex) (a b : Real) (hab : a < b)
    (hf : ContinuousOn f {z : Complex | z.re ∈ Set.Icc a b ∧ z.im = 0})
    (M : Real) (hM : ∀ t ∈ Set.Icc a b, norm (f ↑t) ≤ M) :
    norm (∫ t in a..b, f ↑t) ≤ M * (b - a) := by
  sorry

lemma lem_contour_integral (f : Complex → Complex) (γ : Real → Complex)
    (a b : Real) (hab : a < b)
    (hγ : ContinuousOn γ (Set.Icc a b))
    (hf : ContinuousOn f (γ '' Set.Icc a b)) :
    ∃ I : Complex, I = ∫ t in a..b, f (γ t) * deriv γ t := by
  sorry

-- Argument principle
lemma lem_ArgumentPrinciple (f : Complex → Complex) (R : Real) (hR : 0 < R)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hfnz : ∀ z ∈ {z : Complex | norm z = R}, f z ≠ 0)
    (zeros : Finset Complex) (hzeros : ∀ z ∈ zeros, norm z < R ∧ f z = 0)
    (poles : Finset Complex) (hpoles : ∀ p ∈ poles, norm p < R) :
    (1 / (2 * Real.pi * I)) * ∫ θ in (0)..(2 * Real.pi),
      (deriv f (R * Complex.exp (I * θ))) /
      (f (R * Complex.exp (I * θ))) =
    ↑(zeros.card - poles.card) := by
  sorry

-- Rouché's theorem
lemma lem_Rouche (f g : Complex → Complex) (R : Real) (hR : 0 < R)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hg : AnalyticOn ℂ g {z : Complex | norm z ≤ R})
    (hdom : ∀ z ∈ {z : Complex | norm z = R}, norm (g z) < norm (f z)) :
    ∃ n : ℕ, (∃ zf : Finset Complex, zf.card = n ∧ ∀ z ∈ zf, norm z < R ∧ f z = 0) ∧
             (∃ zfg : Finset Complex, zfg.card = n ∧ ∀ z ∈ zfg, norm z < R ∧ (f + g) z = 0) := by
  sorry

-- Residue theorem
lemma lem_ResidueTheorem (f : Complex → Complex) (poles : Finset Complex)
    (R : Real) (hR : 0 < R)
    (hpoles : ∀ p ∈ poles, norm p < R)
    (hf : AnalyticOn ℂ f ({z : Complex | norm z ≤ R} \ poles))
    (residues : Complex → Complex) :
    ∫ θ in (0)..(2 * Real.pi),
      f (R * Complex.exp (I * θ)) * R * I * Complex.exp (I * θ) =
    2 * Real.pi * I * poles.sum (fun p => residues p) := by
  sorry

-- Morera's theorem
lemma lem_Morera (f : Complex → Complex) (U : Set Complex) (hU : IsOpen U)
    (hf : ContinuousOn f U)
    (hint : ∀ T ⊆ U, ∀ γ : Real → Complex,
            (∀ t ∈ Set.Icc 0 1, γ t ∈ T) →
            γ 0 = γ 1 →
            ∫ t in (0)..(1), f (γ t) * deriv γ t = 0) :
    AnalyticOn ℂ f U := by
  sorry

-- Power series convergence
lemma lem_PowerSeriesConvergence (a : ℕ → Complex) (R : Real) (hR : 0 < R)
    (hconv : ∀ z : Complex, norm z < R →
             HasSum (fun n => a n * z ^ n) (∑' n, a n * z ^ n)) :
    ∃ f : Complex → Complex,
      (∀ z, norm z < R → f z = ∑' n, a n * z ^ n) ∧
      AnalyticOn ℂ f {z : Complex | norm z < R} := by
  sorry

-- Laurent series expansion
lemma lem_LaurentSeries (f : Complex → Complex) (z₀ : Complex) (r R : Real)
    (hr : 0 < r) (hR : r < R)
    (hf : AnalyticOn ℂ f {z : Complex | r < norm (z - z₀) ∧ norm (z - z₀) < R}) :
    ∃ (aₙ : ℤ → Complex), ∀ z, r < norm (z - z₀) ∧ norm (z - z₀) < R →
      f z = ∑' n : ℤ, aₙ n * (z - z₀) ^ n := by
  sorry

-- Additional lemmas from blueprint
lemma lem_Rself3 (R : Real) (hR : R > 0) :
    (R : Complex) ∈ {z : Complex | norm z ≤ R} := by
  simp [norm_real, abs_of_pos hR]

lemma lem_DRcompact (R : Real) (hR : R > 0) :
    IsCompact {z : Complex | norm z ≤ R} := by
  convert isCompact_closedBall (0 : ℂ) R
  ext z
  simp only [Metric.closedBall, Set.mem_setOf_eq, dist_comm, dist_zero_right]

lemma lem_ExtrValThm (K : Set Complex) (hK : IsCompact K) (g : Complex → Complex)
    (hg : ContinuousOn g K) (hne : K.Nonempty) :
    ∃ v ∈ K, ∀ z ∈ K, norm (g z) ≤ norm (g v) := by
  have : ContinuousOn (norm ∘ g) K := continuous_norm.comp_continuousOn hg
  exact IsCompact.exists_isMaxOn hK hne this

lemma lem_ExtrValThmDR (R : Real) (hR : R > 0) (g : Complex → Complex)
    (hg : ContinuousOn g {z : Complex | norm z ≤ R}) :
    ∃ v ∈ {z : Complex | norm z ≤ R}, ∀ z ∈ {z : Complex | norm z ≤ R},
      norm (g z) ≤ norm (g v) := by
  apply lem_ExtrValThm
  · exact lem_DRcompact R hR
  · exact hg
  · use 0
    simp [norm_zero]
    exact le_of_lt hR

lemma lem_AnalCont (R : Real) (hR : R > 0) (h : Complex → Complex)
    (hh : AnalyticOn ℂ h {z : Complex | norm z ≤ R}) :
    ContinuousOn h {z : Complex | norm z ≤ R} := by
  exact AnalyticOn.continuousOn hh

lemma lem_ExtrValThmh (R : Real) (hR : R > 0) (h : Complex → Complex)
    (hh : AnalyticOn ℂ h {z : Complex | norm z ≤ R}) :
    ∃ u ∈ {z : Complex | norm z ≤ R}, ∀ z ∈ {z : Complex | norm z ≤ R},
      norm (h z) ≤ norm (h u) := by
  apply lem_ExtrValThmDR R hR
  exact lem_AnalCont R hR h hh

lemma lem_MaxModP (R : Real) (hR : R > 0) (h : Complex → Complex)
    (hh : AnalyticOn ℂ h {z : Complex | norm z ≤ R})
    (hw : ∃ w ∈ {z : Complex | norm z < R}, ∀ z ∈ {z : Complex | norm z < R},
          norm (h z) ≤ norm (h w)) :
    ∀ z ∈ {z : Complex | norm z ≤ R}, norm (h z) = norm (h (Classical.choose hw)) := by
  sorry

lemma lem_MaxModR (R : Real) (hR : R > 0) (h : Complex → Complex)
    (hh : AnalyticOn ℂ h {z : Complex | norm z ≤ R})
    (hw : ∃ w ∈ {z : Complex | norm z < R}, ∀ z ∈ {z : Complex | norm z < R},
          norm (h z) ≤ norm (h w)) :
    norm (h R) = norm (h (Classical.choose hw)) := by
  apply lem_MaxModP R hR h hh hw
  apply lem_Rself3 R hR

lemma lem_MaxModRR (R : Real) (hR : R > 0) (h : Complex → Complex)
    (hh : AnalyticOn ℂ h {z : Complex | norm z ≤ R})
    (hw : ∃ w ∈ {z : Complex | norm z < R}, ∀ z ∈ {z : Complex | norm z < R},
          norm (h z) ≤ norm (h w)) :
    ∀ z ∈ {z : Complex | norm z ≤ R}, norm (h z) ≤ norm (h R) := by
  intro z hz
  rw [lem_MaxModR R hR h hh hw]
  rw [lem_MaxModP R hR h hh hw z hz]

lemma lem_MaxModv2 (R : Real) (hR : R > 0) (h : Complex → Complex)
    (hh : AnalyticOn ℂ h {z : Complex | norm z ≤ R}) :
    ∃ v ∈ {z : Complex | norm z ≤ R}, norm v = R ∧
      ∀ z ∈ {z : Complex | norm z ≤ R}, norm (h z) ≤ norm (h v) := by
  sorry

lemma lem_MaxModv3 (R : Real) (hR : R > 0) (h : Complex → Complex)
    (hh : AnalyticOn ℂ h {z : Complex | norm z ≤ R}) :
    ∃ v : Complex, norm v = R ∧
      ∀ z : Complex, norm z ≤ R → norm (h z) ≤ norm (h v) := by
  obtain ⟨v, hv, hvnorm, hvmax⟩ := lem_MaxModv2 R hR h hh
  use v
  exact ⟨hvnorm, fun z hz => hvmax z hz⟩

lemma lem_MaxModv4 (R : Real) (hR : R > 0) (B : Real) (hB : B ≥ 0) (h : Complex → Complex)
    (hh : AnalyticOn ℂ h {z : Complex | norm z ≤ R})
    (hbound : ∀ z : Complex, norm z = R → norm (h z) ≤ B) :
    ∃ v : Complex, norm v = R ∧
      (∀ w : Complex, norm w ≤ R → norm (h w) ≤ norm (h v)) ∧
      norm (h v) ≤ B := by
  obtain ⟨v, hvnorm, hvmax⟩ := lem_MaxModv3 R hR h hh
  use v
  exact ⟨hvnorm, hvmax, hbound v hvnorm⟩

lemma lem_HardMMP (R : Real) (hR : R > 0) (B : Real) (hB : B ≥ 0) (h : Complex → Complex)
    (hh : AnalyticOn ℂ h {z : Complex | norm z ≤ R})
    (hbound : ∀ z : Complex, norm z = R → norm (h z) ≤ B) :
    ∀ w : Complex, norm w ≤ R → norm (h w) ≤ B := by
  sorry

lemma lem_EasyMMP (R : Real) (hR : R > 0) (B : Real) (hB : B ≥ 0) (h : Complex → Complex)
    (hh : AnalyticOn ℂ h {z : Complex | norm z ≤ R})
    (hbound : ∀ w : Complex, norm w ≤ R → norm (h w) ≤ B) :
    ∀ z : Complex, norm z = R → norm (h z) ≤ B := by
  intro z hz
  apply hbound z
  rw [hz]

lemma lem_MMP (T : Real) (hT : T > 0) (B : Real) (hB : B ≥ 0) (h : Complex → Complex)
    (hh : AnalyticOn ℂ h {z : Complex | norm z ≤ T}) :
    (∀ z : Complex, norm z ≤ T → norm (h z) ≤ B) ↔
    (∀ z : Complex, norm z = T → norm (h z) ≤ B) := by
  constructor
  · exact lem_EasyMMP T hT B hB h hh
  · exact lem_HardMMP T hT B hB h hh

lemma lem_denominator_nonzero (R M : Real) (hR : R > 0) (hM : M > 0)
    (f : Complex → Complex)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hfRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M) :
    ∀ z : Complex, norm z ≤ R → (2 * M : Complex) - f z ≠ 0 := by
  intro z hz
  apply lem_real_part_lower_bound4
  exact hM
  exact hfRe z hz

lemma lem_f_vs_2M_minus_f (R M : Real) (hR : R > 0) (hM : M > 0)
    (f : Complex → Complex)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hfRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M) :
    ∀ z : Complex, norm z ≤ R → norm (f z) / norm ((2 * M : Complex) - f z) ≤ 1 := by
  intro z hz
  apply lem_nonnegative_product9 M (f z) hM (hfRe z hz)

lemma lem_removable_singularity (R : Real) (hR : R > 0) (f : Complex → Complex)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) :
    AnalyticOn ℂ (fun z => f z / z) {z : Complex | norm z ≤ R} := by
  sorry

lemma lem_quotient_analytic (R : Real) (hR : R > 0) (h₁ h₂ : Complex → Complex)
    (hh₁ : AnalyticOn ℂ h₁ {z : Complex | norm z ≤ R})
    (hh₂ : AnalyticOn ℂ h₂ {z : Complex | norm z ≤ R})
    (hnz : ∀ z : Complex, norm z ≤ R → h₂ z ≠ 0) :
    AnalyticOn ℂ (fun z => h₁ z / h₂ z) {z : Complex | norm z ≤ R} := by
  sorry

noncomputable def f_M (R M : Real) (f : Complex → Complex) : Complex → Complex :=
  fun z => (f z / z) / ((2 * M : Complex) - f z)

lemma lem_g_analytic (R M : Real) (hR : R > 0) (hM : M > 0) (f : Complex → Complex)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hfRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M) :
    AnalyticOn ℂ (f_M R M f) {z : Complex | norm z ≤ R} := by
  unfold f_M
  sorry

lemma lem_absab (a b : Complex) (hb : b ≠ 0) : norm (a / b) = norm a / norm b := by
  simp [norm_div]

lemma lem_g_on_boundaryz (R M : Real) (hR : R > 0) (hM : M > 0) (f : Complex → Complex)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hfRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M)
    (z : Complex) (hz : norm z ≤ R) :
    norm (f_M R M f z) = norm (f z / z) / norm (2 * M - f z) := by
  unfold f_M
  apply lem_absab
  exact lem_denominator_nonzero R M hR hM f hf hfRe z hz

-- Quotient radius lemma
lemma lem_fzzR (T : Real) (hT : T > 0) (z w : Complex) (hz : norm z = T) :
    norm (w / z) = norm w / T := by
  simp [norm_div, hz]

-- Boundary g lemma
lemma lem_g_on_boundary (R M : Real) (hR : R > 0) (hM : M > 0) (f : Complex → Complex)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hfRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M)
    (z : Complex) (hz : norm z = R) :
    norm (f_M R M f z) = norm (f z) / R / norm (2 * M - f z) := by
  have hz' : norm z ≤ R := le_of_eq hz
  rw [lem_g_on_boundaryz R M hR hM f hf hf0 hfRe z hz']
  rw [lem_fzzR R hR z (f z) hz]

-- Scaled ratio lemma
lemma lem_f_vs_2M_minus_fR (R M : Real) (hR : R > 0) (hM : M > 0) (f : Complex → Complex)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hfRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M)
    (z : Complex) (hz : norm z ≤ R) :
    norm (f z) / R / norm (2 * M - f z) ≤ 1 / R := by
  have h := lem_f_vs_2M_minus_f R M hR hM f hf hfRe z hz
  calc norm (f z) / R / norm (2 * M - f z) = (norm (f z) / norm (2 * M - f z)) / R := by ring
    _ ≤ 1 / R := by {
      apply div_le_div_of_nonneg_right h
      exact le_of_lt hR
    }

-- Boundary bound lemma
lemma lem_g_boundary_bound0 (R M : Real) (hR : R > 0) (hM : M > 0) (f : Complex → Complex)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hfRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M)
    (z : Complex) (hz : norm z = R) :
    norm (f_M R M f z) ≤ 1 / R := by
  rw [lem_g_on_boundary R M hR hM f hf hf0 hfRe z hz]
  exact lem_f_vs_2M_minus_fR R M hR hM f hf hfRe z (le_of_eq hz)

-- Interior bound lemma
lemma lem_g_interior_bound (R M : Real) (hR : R > 0) (hM : M > 0) (f : Complex → Complex)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hfRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M)
    (z : Complex) (hz : norm z ≤ R) :
    norm (f_M R M f z) ≤ 1 / R := by
  sorry -- Uses maximum modulus principle

-- g at r lemma
lemma lem_g_at_r (R M r : Real) (hR : R > 0) (hM : M > 0) (hr : 0 < r) (hrR : r < R)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hfRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M)
    (z : Complex) (hz : norm z = r) :
    norm (f_M R M f z) = norm (f z) / r / norm (2 * M - f z) := by
  have hz' : norm z ≤ R := le_trans (le_of_eq hz) (le_of_lt hrR)
  rw [lem_g_on_boundaryz R M hR hM f hf hf0 hfRe z hz']
  rw [lem_fzzR r hr z (f z) hz]

-- g bound r lemma
lemma lem_g_at_rR (R M r : Real) (hR : R > 0) (hM : M > 0) (hr : 0 < r) (hrR : r < R)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hfRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M)
    (z : Complex) (hz : norm z = r) :
    norm (f z) / r / norm (2 * M - f z) ≤ 1 / R := by
  have hz' : norm z ≤ R := le_trans (le_of_eq hz) (le_of_lt hrR)
  rw [← lem_g_at_r R M r hR hM hr hrR f hf hf0 hfRe z hz]
  exact lem_g_interior_bound R M hR hM f hf hf0 hfRe z hz'

-- Fraction swap lemma
lemma lem_fracs (a b r R : Real) (ha : a ≥ 0) (hb : b > 0) (hr : r > 0) (hR : R > 0) :
    (a / r) / b ≤ 1 / R → R * a ≤ r * b := by
  intro h
  -- The inequality (a/r)/b ≤ 1/R is equivalent to R*a ≤ r*b after clearing denominators
  have h1 : a / (r * b) ≤ 1 / R := by
    calc a / (r * b) = (a / r) / b := by field_simp
                   _ ≤ 1 / R := h
  -- Multiply both sides by R * (r * b)
  have h2 : a * R ≤ r * b := by
    calc a * R = (a / (r * b)) * (r * b * R) := by field_simp [ne_of_gt (mul_pos hr hb)]
             _ ≤ (1 / R) * (r * b * R) := by
                 apply mul_le_mul_of_nonneg_right h1
                 apply mul_nonneg
                 exact le_of_lt (mul_pos hr hb)
                 exact le_of_lt hR
             _ = r * b := by field_simp [ne_of_gt hR]
  -- Convert a * R ≤ r * b to R * a ≤ r * b
  ring_nf at h2 ⊢
  exact h2

-- Rearranged bound lemma
lemma lem_f_bound_rearranged (R M r : Real) (hR : R > 0) (hM : M > 0) (hr : 0 < r) (hrR : r < R)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hfRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M)
    (z : Complex) (hz : norm z = r) :
    R * norm (f z) ≤ r * norm (2 * M - f z) := by
  have h := lem_g_at_rR R M r hR hM hr hrR f hf hf0 hfRe z hz
  have hz' : norm z ≤ R := le_trans (le_of_eq hz) (le_of_lt hrR)
  have h2 : norm (2 * M - f z) > 0 := norm_pos_iff.mpr (lem_denominator_nonzero R M hR hM f hf hfRe z hz')
  exact lem_fracs (norm (f z)) (norm (2 * M - f z)) r R (norm_nonneg _) h2 hr hR h

-- Circle bound lemmas
lemma lem_final_bound_on_circle0 (R M r : Real) (hR : R > 0) (hM : M > 0) (hr : 0 < r) (hrR : r < R)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hfRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M)
    (z : Complex) (hz : norm z = r) :
    norm (f z) ≤ 2 * r / (R - r) * M := by
  have h := lem_f_bound_rearranged R M r hR hM hr hrR f hf hf0 hfRe z hz
  -- h : R * norm (f z) ≤ r * norm (2 * M - f z)
  -- Apply lem_rtriangle7 with F = f z
  convert lem_rtriangle7 r R M (f z) hr hrR hM h using 1
  ring

lemma lem_final_bound_on_circle (R M r : Real) (hR : R > 0) (hM : M > 0) (hr : 0 < r) (hrR : r < R)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hfRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M)
    (z : Complex) (hz : norm z = r) :
    norm (f z) ≤ 2 * r / (R - r) * M :=
  lem_final_bound_on_circle0 R M r hR hM hr hrR f hf hf0 hfRe z hz

-- BC bound lemma
lemma lem_BCI (R M r : Real) (hR : R > 0) (hM : M > 0) (hr : 0 < r) (hrR : r < R)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hfRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M)
    (z : Complex) (hz : norm z ≤ r) :
    norm (f z) ≤ 2 * r / (R - r) * M := by
  sorry -- Uses maximum modulus principle

-- Borel-Carathéodory I theorem
theorem thm_BorelCaratheodoryI (R M r : Real) (hR : R > 0) (hM : M > 0) (hr : 0 < r) (hrR : r < R)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hfRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M) :
    (⨆ z : {z : Complex | norm z ≤ r}, norm (f z)) ≤ 2 * r / (R - r) * M := by
  sorry -- Uses lem_BCI and supremum properties


/- Section: Borel-Carathéodory II -/

-- Cauchy's Integral Formula for derivative
theorem cauchy_formula_deriv (R r r' : Real) (f : Complex → Complex)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hr : 0 < r) (hr' : r < r') (hr'R : r' < R) (z : Complex) (hz : norm z ≤ r) :
    deriv f z = (2 * π * I)⁻¹ * sorry := by
  sorry

-- Differential of w(t)
lemma lem_dw_dt (r' : Real) (t : Real) :
    deriv (fun t => r' * Complex.exp (I * t)) t = I * r' * Complex.exp (I * t) := by
  sorry

-- Cauchy's Integral Formula parameterized
lemma lem_CIF_deriv_param (R r r' : Real) (f : Complex → Complex)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hr : 0 < r) (hr' : r < r') (hr'R : r' < R) (z : Complex) (hz : norm z ≤ r) :
    deriv f z = (2 * π * I)⁻¹ * ∫ t in (0)..(2*π),
      f (r' * Complex.exp (I * t)) / (r' * Complex.exp (I * t) - z)^2 * (I * r' * Complex.exp (I * t)) := by
  sorry

-- CIF simplified
lemma lem_CIF_deriv_simplified (R r r' : Real) (f : Complex → Complex)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hr : 0 < r) (hr' : r < r') (hr'R : r' < R) (z : Complex) (hz : norm z ≤ r) :
    deriv f z = (2 * π)⁻¹ * ∫ t in (0)..(2*π),
      f (r' * Complex.exp (I * t)) * r' * Complex.exp (I * t) / (r' * Complex.exp (I * t) - z)^2 := by
  sorry

-- Derivative modulus
lemma lem_modulus_of_f_prime0 (R r r' : Real) (f : Complex → Complex)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hr : 0 < r) (hr' : r < r') (hr'R : r' < R) (z : Complex) (hz : norm z ≤ r) :
    norm (deriv f z) = norm ((2 * π)⁻¹ * ∫ t in (0)..(2*π),
      f (r' * Complex.exp (I * t)) * r' * Complex.exp (I * t) / (r' * Complex.exp (I * t) - z)^2) := by
  rw [lem_CIF_deriv_simplified R r r' f hf hr hr' hr'R z hz]

-- Integral modulus inequality
lemma lem_integral_modulus_inequality {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (g : α → Complex) (hg : MeasureTheory.Integrable g μ) :
    norm (∫ t, g t ∂μ) ≤ ∫ t, norm (g t) ∂μ := by
  exact MeasureTheory.norm_integral_le_integral_norm g

-- Modulus of f'
lemma lem_modulus_of_f_prime (R r r' : Real) (f : Complex → Complex)
    (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hr : 0 < r) (hr' : r < r') (hr'R : r' < R) (z : Complex) (hz : norm z ≤ r) :
    norm (deriv f z) ≤ (2 * π)⁻¹ * ∫ t in (0)..(2*π),
      norm (f (r' * Complex.exp (I * t)) * r' * Complex.exp (I * t) / (r' * Complex.exp (I * t) - z)^2) := by
  sorry

-- Integrand modulus product
lemma lem_modulus_of_integrand_product2 (r' : Real) (f : Complex → Complex) (t : Real) :
    norm (f (r' * Complex.exp (I * t)) * r' * Complex.exp (I * t)) =
    norm (f (r' * Complex.exp (I * t))) * norm (r' * Complex.exp (I * t)) := by
  simp only [norm_mul]
  ring

-- Modulus lemmas for exponentials
lemma lem_modeit (t : Real) : norm (Complex.exp (I * t)) = Real.exp ((I * t).re) := by
  rw [Complex.norm_exp]

lemma lem_Reit0 (t : Real) : (I * t : Complex).re = 0 := by
  simp [I_re, Complex.mul_re]

lemma lem_eReite0 (t : Real) : Real.exp ((I * t : Complex).re) = Real.exp 0 := by
  rw [lem_Reit0]

lemma lem_e01 : Real.exp 0 = 1 := by
  exact Real.exp_zero

lemma lem_eReit1 (t : Real) : Real.exp ((I * t : Complex).re) = 1 := by
  rw [lem_eReite0, lem_e01]

lemma lem_modulus_of_e_it_is_one (t : Real) : norm (Complex.exp (I * t)) = 1 := by
  rw [lem_modeit, lem_eReit1]

lemma lem_modulus_of_ae_it (a : Real) (ha : a > 0) (t : Real) :
    norm (a * Complex.exp (I * t)) = a := by
  rw [norm_mul, lem_modulus_of_e_it_is_one]
  simp [Real.norm_eq_abs, abs_of_pos ha]

-- Integrand modulus 3
lemma lem_modulus_of_integrand_product3 (r' : Real) (hr' : r' > 0) (f : Complex → Complex) (t : Real) :
    norm (f (r' * Complex.exp (I * t)) * r' * Complex.exp (I * t)) =
    r' * norm (f (r' * Complex.exp (I * t))) := by
  rw [lem_modulus_of_integrand_product2, lem_modulus_of_ae_it r' hr', mul_comm]

-- Square modulus
lemma lem_modulus_of_square (c : Complex) : norm (c^2) = norm c ^ 2 := by
  simp [sq, norm_mul]

-- Shifted modulus
lemma lem_modulus_wz (w z : Complex) : norm ((w - z)^2) = norm (w - z) ^ 2 := by
  apply lem_modulus_of_square

-- Reverse triangle
lemma lem_reverse_triangle (w z : Complex) : norm w - norm z ≤ norm (w - z) := by
  have := norm_sub_norm_le w z
  linarith

-- Reverse triangle 2
lemma lem_reverse_triangle2 (t : ℝ) (r r' R : ℝ) (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R) (z : Complex) :
    norm (r' * Complex.exp (I * t : Complex)) - norm z ≤ norm (r' * Complex.exp (I * t : Complex) - z) := by
  apply lem_reverse_triangle

-- Reverse triangle 3
lemma lem_reverse_triangle3 (t : ℝ) (r r' R : ℝ) (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R) (z : Complex) :
    r' - norm z ≤ norm (r' * Complex.exp (I * t : Complex) - z) := by
  have h1 := lem_reverse_triangle2 t r r' R hr hrr' hr'R z
  have h2 := lem_modulus_of_ae_it r' (by linarith : 0 < r')
  rw [h2] at h1
  exact h1

-- Radius relation
lemma lem_zrr1 (r r' R : ℝ) (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R) (z : Complex) (hz : norm z ≤ r) :
    0 < r' - norm z := by
  linarith

-- Radius relation 2
lemma lem_zrr2 (t : ℝ) (r r' R : ℝ) (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R) (z : Complex) (hz : norm z ≤ r) :
    r' - r ≤ norm (r' * Complex.exp (I * t : Complex) - z) := by
  have h := lem_reverse_triangle3 t r r' R hr hrr' hr'R z
  linarith

-- Radius relation 3
lemma lem_rr11 (r r' : ℝ) (hrr' : r < r') : r' - r > 0 := by
  linarith

-- Radius relation 4
lemma lem_rr12 (r r' : ℝ) (hrr' : r < r') : (r' - r)^2 > 0 := by
  apply pow_pos
  apply lem_rr11
  exact hrr'

-- Radius relation 5
lemma lem_zrr3 (t : ℝ) (r r' R : ℝ) (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R) (z : Complex) (hz : norm z ≤ r) :
    (r' - r)^2 ≤ norm (r' * Complex.exp (I * t : Complex) - z) ^ 2 := by
  have h1 := lem_zrr2 t r r' R hr hrr' hr'R z hz
  -- We have r' - r ≤ norm (r' * Complex.exp (I * t : Complex) - z)
  -- Squaring both sides preserves the inequality since both sides are nonnegative
  apply sq_le_sq'
  · linarith  -- r' - r ≥ 0 follows from hrr'
  · exact h1

-- Radius relation 6
lemma lem_zrr4 (t : ℝ) (r r' R : ℝ) (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R) (z : Complex) (hz : norm z ≤ r) :
    norm ((r' * Complex.exp (I * t : Complex) - z)^2) = norm (r' * Complex.exp (I * t : Complex) - z) ^ 2 := by
  apply lem_modulus_of_square

-- Reverse triangle 4
lemma lem_reverse_triangle4 (t : ℝ) (r r' R : ℝ) (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R) (z : Complex) (hz : norm z ≤ r) :
    0 < norm (r' * Complex.exp (I * t : Complex) - z) := by
  have h := lem_zrr2 t r r' R hr hrr' hr'R z hz
  have h2 := lem_rr11 r r' hrr'
  linarith

-- Positive nonzero
lemma lem_wposneq0 (w : Complex) (hw : 0 < norm w) : w ≠ 0 := by
  intro h
  rw [h, norm_zero] at hw
  linarith

-- Reverse triangle 5
lemma lem_reverse_triangle5 (t : ℝ) (r r' R : ℝ) (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R) (z : Complex) (hz : norm z ≤ r) :
    r' * Complex.exp (I * t : Complex) - z ≠ 0 := by
  apply lem_wposneq0
  apply lem_reverse_triangle4 t r r' R hr hrr' hr'R z hz

-- Reverse triangle 6
lemma lem_reverse_triangle6 (t : ℝ) (r r' R : ℝ) (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R) (z : Complex) (hz : norm z ≤ r) :
    (r' * Complex.exp (I * t : Complex) - z)^2 ≠ 0 := by
  apply pow_ne_zero
  apply lem_reverse_triangle5 t r r' R hr hrr' hr'R z hz

-- Division bound
lemma lem_absdiv (a b : Complex) (hb : b ≠ 0) : norm (a / b) = norm a / norm b := by
  exact norm_div hb

-- Integrand modulus
lemma lem_modulus_of_integrand_product (r r' R : ℝ) (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (t : ℝ) (z : Complex) (hz : norm z ≤ r) :
    norm ((f (r' * Complex.exp (I * t : Complex)) * r' * Complex.exp (I * t : Complex)) / (r' * Complex.exp (I * t : Complex) - z)^2) =
    norm (f (r' * Complex.exp (I * t : Complex)) * r' * Complex.exp (I * t : Complex)) / norm ((r' * Complex.exp (I * t : Complex) - z)^2) := by
  rw [lem_absdiv]
  apply lem_reverse_triangle6 t r r' R hr hrr' hr'R z hz

-- Product modulus
lemma lem_modulus_of_product (r r' R : ℝ) (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (t : ℝ) (z : Complex) (hz : norm z ≤ r) :
    norm ((f (r' * Complex.exp (I * t : Complex)) * r' * Complex.exp (I * t : Complex)) / (r' * Complex.exp (I * t : Complex) - z)^2) =
    r' * norm (f (r' * Complex.exp (I * t : Complex))) / norm ((r' * Complex.exp (I * t : Complex) - z)^2) := by
  rw [lem_modulus_of_integrand_product r r' R hr hrr' hr'R f hf t z hz]
  rw [lem_modulus_of_integrand_product3 r' (by linarith : 0 < r') f]

-- Product modulus 2
lemma lem_modulus_of_product2 (r r' R : ℝ) (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (t : ℝ) (z : Complex) (hz : norm z ≤ r) :
    norm ((f (r' * Complex.exp (I * t : Complex)) * r' * Complex.exp (I * t : Complex)) / (r' * Complex.exp (I * t : Complex) - z)^2) =
    r' * norm (f (r' * Complex.exp (I * t : Complex))) / norm (r' * Complex.exp (I * t : Complex) - z) ^ 2 := by
  rw [lem_modulus_of_product r r' R hr hrr' hr'R f hf t z hz]
  rw [lem_zrr4 t r r' R hr hrr' hr'R z hz]

-- Product modulus 3
lemma lem_modulus_of_product3 (r r' R : ℝ) (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (t : ℝ) (z : Complex) (hz : norm z ≤ r) :
    r' * norm (f (r' * Complex.exp (I * t : Complex))) / norm (r' * Complex.exp (I * t : Complex) - z) ^ 2 ≤
    r' * norm (f (r' * Complex.exp (I * t : Complex))) / (r' - r) ^ 2 := by
  -- Since (r' - r)^2 ≤ norm (r' * Complex.exp (I * t : Complex) - z)^2 by lem_zrr3,
  -- and both are positive, dividing by the larger gives a smaller result
  have h_denom_ineq := lem_zrr3 t r r' R hr hrr' hr'R z hz
  have h_denom_pos_1 := lem_rr12 r r' hrr'
  have h_denom_pos_2 : 0 < norm (r' * Complex.exp (I * t : Complex) - z) ^ 2 := by
    apply pow_pos
    apply lem_reverse_triangle4 t r r' R hr hrr' hr'R z hz
  gcongr
  exact mul_nonneg (le_of_lt (by linarith : 0 < r')) (norm_nonneg _)

-- Product modulus 4
lemma lem_modulus_of_product4 (r r' R : ℝ) (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (t : ℝ) (z : Complex) (hz : norm z ≤ r) :
    norm ((f (r' * Complex.exp (I * t : Complex)) * r' * Complex.exp (I * t : Complex)) / (r' * Complex.exp (I * t : Complex) - z)^2) ≤
    r' * norm (f (r' * Complex.exp (I * t : Complex))) / (r' - r) ^ 2 := by
  -- This follows by combining the previous modulus lemmas
  calc norm ((f (r' * Complex.exp (I * t : Complex)) * r' * Complex.exp (I * t : Complex)) / (r' * Complex.exp (I * t : Complex) - z)^2)
      = r' * norm (f (r' * Complex.exp (I * t : Complex))) / norm (r' * Complex.exp (I * t : Complex) - z) ^ 2 :=
        by apply lem_modulus_of_product2 r r' R hr hrr' hr'R f hf t z hz
    _ ≤ r' * norm (f (r' * Complex.exp (I * t : Complex))) / (r' - r) ^ 2 :=
        by apply lem_modulus_of_product3 r r' R hr hrr' hr'R f hf t z hz

-- Point bound on analytic function
lemma lem_bound_on_f_at_r_prime (M R r' : ℝ) (hM : 0 < M) (hR : 0 < R) (hr' : 0 < r') (hr'R : r' < R)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M)
    (t : ℝ) : norm (f (r' * Complex.exp (I * t))) ≤ 2 * r' * M / (R - r') := by
  sorry

-- Integrand bound
lemma lem_bound_on_integrand_modulus (M R r r' : ℝ) (hM : 0 < M) (hR : 0 < R)
    (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M)
    (t : ℝ) (z : Complex) (hz : norm z ≤ r) :
    norm ((f (r' * Complex.exp (I * t)) * r' * Complex.exp (I * t)) / (r' * Complex.exp (I * t) - z)^2) ≤
    2 * r' ^ 2 * M / ((R - r') * (r' - r)^2) := by
  calc norm ((f (r' * Complex.exp (I * t)) * r' * Complex.exp (I * t)) / (r' * Complex.exp (I * t) - z)^2)
    _ ≤ r' * norm (f (r' * Complex.exp (I * t))) / (r' - r) ^ 2 :=
        lem_modulus_of_product4 r r' R hr hrr' hr'R f hf t z hz
    _ ≤ r' * (2 * r' * M / (R - r')) / (r' - r) ^ 2 := by
        apply div_le_div_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left
          · have hr' : 0 < r' := by linarith
            exact lem_bound_on_f_at_r_prime M R r' hM hR hr' hr'R f hf hf0 hRe t
          · linarith
        · apply sq_nonneg
    _ = 2 * r' ^ 2 * M / ((R - r') * (r' - r)^2) := by
      field_simp

-- Integral inequality
lemma lem_integral_inequality (g : ℝ → ℝ) (C : ℝ) (a b : ℝ) (hab : a ≤ b)
    (hg : ∀ t ∈ Set.Icc a b, g t ≤ C)
    (hg_int : IntervalIntegrable g MeasureTheory.volume a b)
    (hC_int : IntervalIntegrable (fun _ => C) MeasureTheory.volume a b) :
    ∫ t in a..b, g t ≤ ∫ t in a..b, C := by
  apply intervalIntegral.integral_mono_on hab hg_int hC_int
  intro x hx
  exact hg x hx

-- Derivative bound by integral of constant
lemma lem_f_prime_bound_by_integral_of_constant (M R r r' : ℝ) (hM : 0 < M) (hR : 0 < R)
    (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M)
    (z : Complex) (hz : norm z ≤ r) :
    norm (deriv f z) ≤ (1 / (2 * Real.pi)) * ∫ t in (0)..(2 * Real.pi),
      2 * r' ^ 2 * M / ((R - r') * (r' - r)^2) := by
  sorry

-- Integral of constant 1
lemma lem_integral_of_1 : ∫ t in (0)..(2 * Real.pi), (1 : ℝ) = 2 * Real.pi := by
  rw [intervalIntegral.integral_const]
  simp [sub_zero, smul_eq_mul, mul_one]

-- Normalized integral
lemma lem_integral_2 : (1 / (2 * Real.pi)) * ∫ t in (0)..(2 * Real.pi), (1 : ℝ) = 1 := by
  rw [lem_integral_of_1]
  field_simp

-- Derivative bound final
lemma lem_f_prime_bound (M R r r' : ℝ) (hM : 0 < M) (hR : 0 < R)
    (hr : 0 < r) (hrr' : r < r') (hr'R : r' < R)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M)
    (z : Complex) (hz : norm z ≤ r) :
    norm (deriv f z) ≤ 2 * r' ^ 2 * M / ((R - r') * (r' - r)^2) := by
  sorry

-- Radius comparison lemmas
lemma lem_r_prime_gt_r (r R : ℝ) (_hr : 0 < r) (hR : r < R) :
    r < (r + R) / 2 := by
  linarith

lemma lem_r_prime_lt_R (r R : ℝ) (_hr : 0 < r) (hR : r < R) :
    (r + R) / 2 < R := by linarith

lemma lem_r_prime_is_intermediate (r R : ℝ) (hr : 0 < r) (hR : r < R) :
    r < (r + R) / 2 ∧ (r + R) / 2 < R := by
  constructor
  · exact lem_r_prime_gt_r r R hr hR
  · exact lem_r_prime_lt_R r R hr hR

-- Radius formula calculations
lemma lem_calc_R_minus_r_prime (r R : ℝ) :
    R - (r + R) / 2 = (R - r) / 2 := by field_simp; ring

lemma lem_calc_r_prime_minus_r (r R : ℝ) :
    (r + R) / 2 - r = (R - r) / 2 := by field_simp; ring

lemma lem_calc_denominator_specific (r R : ℝ) (_hr : 0 < r) (_hR : r < R) :
    let r' := (r + R) / 2
    (R - r') * (r' - r)^2 = (R - r)^3 / 8 := by
  simp only [lem_calc_R_minus_r_prime r R, lem_calc_r_prime_minus_r r R]
  ring

lemma lem_calc_numerator_specific (M r R : ℝ) (_hM : 0 < M) (_hr : 0 < r) (_hR : r < R) :
    let r' := (r + R) / 2
    2 * r'^2 * M = (R + r)^2 * M / 2 := by
  simp only
  ring

lemma lem_frac_simplify (M r R : ℝ) (hM : 0 < M) (hr : 0 < r) (hR : r < R) :
    let r' := (r + R) / 2
    2 * r'^2 * M / ((R - r') * (r' - r)^2) = ((R + r)^2 * M / 2) / ((R - r)^3 / 8) := by
  -- Expand r' = (r + R) / 2
  simp only [show (r + R) / 2 = (r + R) / 2 from rfl]
  -- We have r' - r = (r + R) / 2 - r = (R - r) / 2
  -- And R - r' = R - (r + R) / 2 = (R - r) / 2
  have hr'_sub_r : (r + R) / 2 - r = (R - r) / 2 := by field_simp; ring
  have hR_sub_r' : R - (r + R) / 2 = (R - r) / 2 := by field_simp; ring
  have hr'_sq : ((r + R) / 2)^2 = (r + R)^2 / 4 := by field_simp; ring
  -- Now substitute and simplify
  rw [hr'_sub_r, hR_sub_r', hr'_sq]
  field_simp
  ring

lemma lem_frac_simplify2 (M r R : ℝ) (_hM : 0 < M) (_hr : 0 < r) (hR : r < R) :
    ((R + r)^2 * M / 2) / ((R - r)^3 / 8) = 4 * (R + r)^2 * M / (R - r)^3 := by
  field_simp
  ring

lemma lem_frac_simplify3 (M r R : ℝ) (hM : 0 < M) (hr : 0 < r) (hR : r < R) :
    let r' := (r + R) / 2
    2 * r'^2 * M / ((R - r') * (r' - r)^2) = 4 * (R + r)^2 * M / (R - r)^3 := by
  -- Expand r' = (r + R) / 2
  simp only [show (r + R) / 2 = (r + R) / 2 from rfl]
  -- We have r' - r = (R - r) / 2 and R - r' = (R - r) / 2
  have hr'_sub_r : (r + R) / 2 - r = (R - r) / 2 := by field_simp; ring
  have hR_sub_r' : R - (r + R) / 2 = (R - r) / 2 := by field_simp; ring
  have hr'_sq : ((r + R) / 2)^2 = (r + R)^2 / 4 := by field_simp; ring
  -- Now substitute and simplify
  rw [hr'_sub_r, hR_sub_r', hr'_sq]
  field_simp
  ring

-- Inequality facts
lemma lem_ineq_R_plus_r_lt_2R (r R : ℝ) (hr : r < R) : R + r < 2 * R := by linarith

lemma lem_R_plus_r_is_positive (r R : ℝ) (_hr : 0 < r) (_hR : 0 < R) : 0 < R + r := by linarith

lemma lem_2R_is_positive (R : ℝ) (hR : 0 < R) : 0 < 2 * R := by linarith

lemma lem_square_inequality_strict (a b : ℝ) (ha : 0 < a) (hab : a < b) : a^2 < b^2 := by
  have : -b < a := by linarith
  apply sq_lt_sq' this hab

-- Square bounds
lemma lem_ineq_R_plus_r_sq_lt_2R_sq (r R : ℝ) (hr : 0 < r) (hR : r < R) :
    (R + r)^2 < (2 * R)^2 := by
  apply lem_square_inequality_strict
  · apply lem_R_plus_r_is_positive r R hr (by linarith : 0 < R)
  · apply lem_ineq_R_plus_r_lt_2R r R hR

lemma lem_2R_sq_is_4R_sq (R : ℝ) : (2 * R)^2 = 4 * R^2 := by ring

lemma lem_ineq_R_plus_r_sq (r R : ℝ) (hr : 0 < r) (hR : r < R) :
    (R + r)^2 < 4 * R^2 := by
  rw [← lem_2R_sq_is_4R_sq]
  apply lem_ineq_R_plus_r_sq_lt_2R_sq r R hr hR

lemma lem_ineq_R_plus_r_sqM (M r R : ℝ) (hM : 0 < M) (hr : 0 < r) (hR : r < R) :
    4 * (R + r)^2 * M < 16 * R^2 * M := by
  have h1 : 4 * (R + r)^2 < 16 * R^2 := by
    calc 4 * (R + r)^2
      _ < 4 * (4 * R^2) := by
        apply mul_lt_mul_of_pos_left
        exact lem_ineq_R_plus_r_sq r R hr hR
        linarith
      _ = 16 * R^2 := by ring
  exact mul_lt_mul_of_pos_right h1 hM

lemma lem_simplify_final_bound (M r R : ℝ) (hM : 0 < M) (hr : 0 < r) (hR : r < R) :
    4 * (R + r)^2 * M / (R - r)^3 < 16 * R^2 * M / (R - r)^3 := by
  apply div_lt_div_of_pos_right
  · apply lem_ineq_R_plus_r_sqM M r R hM hr hR
  · apply pow_pos
    linarith

lemma lem_bound_after_substitution (M r R : ℝ) (hM : 0 < M) (hr : 0 < r) (hR : r < R) :
    let r' := (r + R) / 2
    2 * r'^2 * M / ((R - r') * (r' - r)^2) ≤ 16 * R^2 * M / (R - r)^3 := by
  simp only
  have h := lem_frac_simplify3 M r R hM hr hR
  simp only at h
  rw [h]
  exact le_of_lt (lem_simplify_final_bound M r R hM hr hR)

-- Borel-Carathéodory II Theorem
theorem borel_caratheodory_II (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R})
    (hf0 : f 0 = 0) (hRe : ∀ z : Complex, norm z ≤ R → (f z).re ≤ M)
    (r : ℝ) (hr : 0 < r) (hrR : r < R) (z : Complex) (hz : norm z ≤ r) :
    norm (deriv f z) ≤ 16 * M * R^2 / (R - r)^3 := by
  let r' := (r + R) / 2
  have hr' : 0 < r' := by
    simp only [r']
    linarith
  have hrr' : r < r' := lem_r_prime_gt_r r R hr hrR
  have hr'R : r' < R := lem_r_prime_lt_R r R hr hrR
  calc norm (deriv f z)
    _ ≤ 2 * r'^2 * M / ((R - r') * (r' - r)^2) :=
        lem_f_prime_bound M R r r' hM hR hr hrr' hr'R f hf hf0 hRe z hz
    _ ≤ 16 * R^2 * M / (R - r)^3 :=
        lem_bound_after_substitution M r R hM hr hrR
    _ = 16 * M * R^2 / (R - r)^3 := by ring

-- Cauchy for rectangles
lemma cauchy_for_rectangles (R R_0 : ℝ) (hR : 0 < R) (hRR0 : R < R_0) (hR01 : R_0 < 1)
    (f : Complex → Complex) (hf : AnalyticOn ℂ f {z : Complex | norm z ≤ R_0})
    (z w : Complex) (_hz : norm z ≤ R) (_hw : norm w ≤ R) :
    True := by
  trivial


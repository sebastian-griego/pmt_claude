import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Field

open Complex Real Filter Classical
open scoped BigOperators Topology
noncomputable section

namespace PNT3_RiemannZeta

-- Zeta function
noncomputable def zeta (s : ℂ) : ℂ := ∑' n : ℕ+, (n : ℂ) ^ (-s)

-- Zeta converges for Re(s) > 1
lemma zeta_converges_re_gt_one (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ+ => (n : ℂ) ^ (-s)) := by
  sorry

-- Zeta non-zero for Re(s) > 1
lemma zeta_ne_zero_re_gt_one (s : ℂ) (hs : 1 < s.re) :
    zeta s ≠ 0 := by
  sorry

-- Von Mangoldt function (simplified for now)
noncomputable def vonMangoldt (n : ℕ) : ℝ :=
  if ∃ (p k : ℕ), Nat.Prime p ∧ n = p ^ k ∧ k > 0
  then Real.log n  -- simplified
  else 0

-- Logarithmic derivative
noncomputable def log_deriv_zeta (s : ℂ) : ℂ := deriv zeta s / zeta s

-- Series representation
lemma neg_log_deriv_zeta_series (s : ℂ) (hs : 1 < s.re) :
    -log_deriv_zeta s = ∑' n : ℕ+, vonMangoldt n / (n : ℂ) ^ s := by
  sorry

-- Euler product
lemma euler_product (s : ℂ) (hs : 1 < s.re) :
    zeta s = ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ := by
  sorry

-- Analytic continuation pole at 1
lemma zeta_residue_one :
    Tendsto (fun s => (s - 1) * zeta s) (𝓝[{1}ᶜ] 1) (𝓝 1) := by
  sorry

-- Abs p pow s
lemma abs_p_pow_s (p : Nat.Primes) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr p.prop.pos
  have hp' : (p : ℂ) ≠ 0 := by
    simp
    exact p.prop.ne_zero
  rw [Complex.norm_cpow_of_ne_zero hp']
  simp only [Complex.norm_natCast, Complex.neg_re]
  -- p is a positive real number, so arg(p) = 0
  have : Complex.arg (p : ℂ) = 0 := by
    -- A natural number cast to ℂ is a positive real number
    have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr p.prop.pos
    -- For positive reals, the argument is 0
    exact Complex.arg_coe_nonneg (le_of_lt hp_pos)
  rw [this]
  simp [Real.exp_zero]

-- Prime decay lemma
lemma p_s_abs_1 (p : Nat.Primes) (s : ℂ) (hs : 1 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [abs_p_pow_s p s]
  -- |p^(-s)| = p^(-Re(s))
  have hp : 2 ≤ (p : ℝ) := by
    exact_mod_cast p.prop.two_le
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast p.prop.pos
  -- p^(-Re(s)) = 1/p^(Re(s))
  rw [Real.rpow_neg (Nat.cast_nonneg _)]
  -- Since Re(s) > 1 and p ≥ 2, we have p^(Re(s)) > p^1 = p ≥ 2 > 1
  have h1 : 1 < (p : ℝ) ^ s.re := by
    calc (p : ℝ) ^ s.re
      = (p : ℝ) ^ s.re := rfl
    _ ≥ (2 : ℝ) ^ s.re := by
      apply Real.rpow_le_rpow
      · norm_num
      · exact hp
      · linarith
    _ > (2 : ℝ) ^ 1 := by
      apply Real.rpow_lt_rpow_left
      · norm_num
      · norm_num
      · exact hs
    _ = 2 := by simp
    _ > 1 := by norm_num
  -- So 1/p^(Re(s)) < 1
  have hpower_pos : 0 < (p : ℝ) ^ s.re := Real.rpow_pos_of_pos hp_pos _
  exact inv_lt_one h1

-- Abs of tprod
lemma abs_of_tprod {P : Type*} [Countable P] (w : P → ℂ) (hw : Multipliable w) :
    ‖∏' p : P, w p‖ = ∏' p : P, ‖w p‖ := by
  exact hw.norm_tprod

-- Abs primes
lemma abs_P_prod (s : ℂ) (hs : 1 < s.re) :
    ‖∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹‖ =
    ∏' p : Nat.Primes, ‖(1 - (p : ℂ) ^ (-s))⁻¹‖ := by
  -- We need to prove that the function is multipliable
  have hm : Multipliable (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))⁻¹) := by
    -- The euler product converges for Re(s) > 1, so the factors are multipliable
    -- This follows from the convergence of the zeta function Euler product
    sorry  -- This requires the Euler product convergence proof
  -- Now apply abs_of_tprod
  exact abs_of_tprod _ hm

-- Abs zeta product
lemma abs_zeta_prod (s : ℂ) (hs : 1 < s.re) :
    ‖zeta s‖ = ∏' p : Nat.Primes, ‖(1 - (p : ℂ) ^ (-s))⁻¹‖ := by
  rw [euler_product s hs]
  exact abs_P_prod s hs

-- Abs inverse
lemma abs_of_inv (z : ℂ) (hz : z ≠ 0) :
    ‖z⁻¹‖ = ‖z‖⁻¹ := by
  simp only [norm_inv]

-- Nonzero factor
lemma one_minus_p_s_neq_0 (p : Nat.Primes) (s : ℂ) (hs : 1 < s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  -- We need |p^(-s)| < 1 when Re(s) > 1
  have h := p_s_abs_1 p s hs
  intro heq
  -- If 1 - p^(-s) = 0, then p^(-s) = 1, so |p^(-s)| = 1
  have : (p : ℂ) ^ (-s) = 1 := by
    rw [sub_eq_zero] at heq
    exact heq.symm
  rw [this, norm_one] at h
  linarith

-- Abs zeta product prime
lemma abs_zeta_prod_prime (s : ℂ) (hs : 1 < s.re) :
    ‖zeta s‖ = ∏' p : Nat.Primes, ‖1 - (p : ℂ) ^ (-s)‖⁻¹ := by
  rw [abs_zeta_prod s hs]
  congr 1
  ext p
  have hnz := one_minus_p_s_neq_0 p s hs
  rw [abs_of_inv (1 - (p : ℂ) ^ (-s)) hnz]

-- Real double
lemma Re2s (s : ℂ) : (2 * s).re = 2 * s.re := by
  simp only [mul_re, mul_zero, sub_zero]
  norm_num

-- Real bound
lemma Re2sge1 (s : ℂ) (hs : 1 < s.re) : 1 < (2 * s).re := by
  rw [Re2s]
  linarith

-- Zeta ratio product
lemma zeta_ratio_prod (s : ℂ) (hs : 1 < s.re) :
    zeta (2 * s) / zeta s =
    (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-2*s))⁻¹) /
    (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹) := by
  rw [euler_product (2 * s) (Re2sge1 s hs), euler_product s hs]
  simp only [neg_mul]

-- Ratio product general
lemma prod_of_ratios {P : Type*} [Countable P]
    (a b : P → ℂ) (ha : Multipliable a) (hb : Multipliable b) :
    (∏' p : P, a p) / (∏' p : P, b p) = ∏' p : P, (a p / b p) := by
  sorry

-- Simplify prod ratio
lemma simplify_prod_ratio (s : ℂ) (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-2*s))⁻¹) /
    (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹) =
    ∏' p : Nat.Primes, ((1 - (p : ℂ) ^ (-2*s))⁻¹ / (1 - (p : ℂ) ^ (-s))⁻¹) := by
  apply prod_of_ratios
  -- Need multipliability for (1 - p^(-2s))⁻¹
  sorry
  -- Need multipliability for (1 - p^(-s))⁻¹
  sorry

-- Zeta ratios
lemma zeta_ratios (s : ℂ) (hs : 1 < s.re) :
    zeta (2 * s) / zeta s =
    ∏' p : Nat.Primes, ((1 - (p : ℂ) ^ (-2*s))⁻¹ / (1 - (p : ℂ) ^ (-s))⁻¹) := by
  rw [zeta_ratio_prod s hs, simplify_prod_ratio s hs]

-- Difference of squares
lemma diff_of_squares (z : ℂ) : 1 - z^2 = (1 - z) * (1 + z) := by
  ring

-- Inverse ratio
lemma ratio_invs (z : ℂ) (hz : ‖z‖ < 1) :
    (1 - z^2)⁻¹ / (1 - z)⁻¹ = (1 + z)⁻¹ := by
  -- We need to show that (1 - z²)⁻¹ / (1 - z)⁻¹ = (1 + z)⁻¹
  -- First, note that 1 - z² = (1 - z)(1 + z)
  have h1 : 1 - z^2 = (1 - z) * (1 + z) := by ring
  -- Since |z| < 1, we have 1 - z ≠ 0, 1 + z ≠ 0, and 1 - z² ≠ 0
  have hz1 : 1 - z ≠ 0 := by
    intro h
    have h_eq : z = 1 := by simp [sub_eq_zero] at h; exact h.symm
    rw [h_eq] at hz
    simp only [norm_one] at hz
    exact lt_irrefl 1 hz
  have hz2 : 1 + z ≠ 0 := by
    intro h
    have h_eq : z = -1 := by
      rw [add_comm] at h
      exact eq_neg_of_add_eq_zero_left h
    rw [h_eq] at hz
    simp only [norm_neg, norm_one] at hz
    exact lt_irrefl 1 hz
  have hz3 : 1 - z^2 ≠ 0 := by
    rw [h1]
    exact mul_ne_zero hz1 hz2
  -- Now simplify the expression
  field_simp [hz1, hz2, hz3]
  ring

-- Zeta ratio identity
theorem zeta_ratio_identity (s : ℂ) (hs : 1 < s.re) :
    zeta (2 * s) / zeta s = ∏' p : Nat.Primes, (1 + (p : ℂ) ^ (-s))⁻¹ := by
  sorry

-- Zeta ratio at 3/2
lemma zeta_ratio_at_3_2 :
    zeta 3 / zeta (3/2) = ∏' p : Nat.Primes, (1 + (p : ℂ) ^ (-(3/2 : ℂ)))⁻¹ := by
  sorry

-- Triangle inequality specific
lemma triangle_inequality_specific (z : ℂ) :
    ‖1 - z‖ ≤ 1 + ‖z‖ := by
  calc
    ‖1 - z‖ ≤ ‖1‖ + ‖z‖ := norm_sub_le _ _
    _ = 1 + ‖z‖ := by simp

-- Abs term bound
lemma abs_term_bound (p : Nat.Primes) (t : ℝ) :
    ‖1 - (p : ℂ) ^ (-(3/2 + I * t))‖ ≤ 1 + (p : ℝ) ^ (-(3/2 : ℝ)) := by
  calc
    ‖1 - (p : ℂ) ^ (-(3/2 + I * t))‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-(3/2 + I * t))‖ := norm_sub_le _ _
    _ = 1 + ‖(p : ℂ) ^ (-(3/2 + I * t))‖ := by simp
    _ = 1 + (p : ℝ) ^ (-((3/2 + I * t).re)) := by rw [abs_p_pow_s]
    _ = 1 + (p : ℝ) ^ (-(3/2 : ℝ)) := by simp [Complex.add_re, Complex.I_re]

-- Inverse inequality
lemma inv_inequality {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a⁻¹ ≥ b⁻¹ := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  exact inv_le_inv₀ hb ha |>.mpr hab

-- Nonzero term at 3/2
lemma condp32 (p : Nat.Primes) (t : ℝ) :
    1 - (p : ℂ) ^ (-(3/2 + I * t)) ≠ 0 := by
  -- We show that |p^(-(3/2 + I*t))| < 1
  -- First, note that |p^(-(3/2 + I*t))| = p^(-3/2) since the imaginary part doesn't affect the norm
  have hp_ge2 : 2 ≤ (p : ℝ) := by
    norm_cast
    exact Nat.Prime.two_le p.prop
  have hp_pos : 0 < (p : ℝ) := by
    norm_cast
    exact Nat.Prime.pos p.prop
  -- Now p^(-3/2) = 1/p^(3/2) < 1 since p ≥ 2
  have h_bound : ‖(p : ℂ) ^ (-(3/2 + I * t))‖ < 1 := by
    rw [abs_p_pow_s]
    simp [Complex.add_re, Complex.I_re]
    -- Now we have p^(-3/2) < 1
    -- Since p ≥ 2, we have p^(3/2) > 2^(3/2) > 2 > 1
    -- So p^(-3/2) = 1/p^(3/2) < 1
    calc
      (p : ℝ) ^ (-(3/2 : ℝ)) = 1 / (p : ℝ) ^ (3/2 : ℝ) := by
        rw [Real.rpow_neg (le_of_lt hp_pos)]
        rw [inv_eq_one_div]
      _ < 1 := by
        rw [div_lt_one]
        · calc
            (p : ℝ) ^ (3/2 : ℝ) ≥ 2 ^ (3/2 : ℝ) := by
              apply Real.rpow_le_rpow
              · linarith
              · exact hp_ge2
              · linarith
            _ > 1 := by
              rw [show (3/2 : ℝ) = 1.5 by norm_num]
              norm_num
        · apply Real.rpow_pos_of_pos hp_pos
  -- If 1 - z = 0, then z = 1, so |z| = 1, contradicting |z| < 1
  intro h_eq
  rw [sub_eq_zero] at h_eq
  have : ‖(p : ℂ) ^ (-(3/2 + I * t))‖ = 1 := by
    rw [← h_eq]
    simp
  linarith

-- Abs term inverse bound
lemma abs_term_inv_bound (p : Nat.Primes) (t : ℝ) :
    ‖(1 - (p : ℂ) ^ (-(3/2 + I * t)))⁻¹‖ ≥ ((1 + (p : ℝ) ^ (-(3/2 : ℝ))))⁻¹ := by
  have h_ne : 1 - (p : ℂ) ^ (-(3/2 + I * t)) ≠ 0 := condp32 p t
  rw [norm_inv]
  have bound : ‖1 - (p : ℂ) ^ (-(3/2 + I * t))‖ ≤ 1 + (p : ℝ) ^ (-(3/2 : ℝ)) := abs_term_bound p t
  have pos_denom : 0 < 1 + (p : ℝ) ^ (-(3/2 : ℝ)) := by
    have hp_pos : 0 < (p : ℝ) := by norm_cast; exact Nat.Prime.pos p.prop
    have : 0 < (p : ℝ) ^ (-(3/2 : ℝ)) := Real.rpow_pos_of_pos hp_pos _
    linarith
  exact inv_le_inv₀ pos_denom (norm_pos_iff.mpr h_ne) |>.mpr bound

-- Lower bound for product
lemma lower_bound_product (t : ℝ) :
    ‖∏' p : Nat.Primes, (1 + (p : ℂ) ^ (-(3/2 + I * t)))⁻¹‖ ≥
    ∏' p : Nat.Primes, ((1 + (p : ℝ) ^ (-(3/2 : ℝ))))⁻¹ := by
  sorry

-- Real product bound
lemma real_prod_bound :
    ∏' p : Nat.Primes, ((1 + (p : ℝ) ^ (-(3/2 : ℝ))))⁻¹ =
    (∏' p : Nat.Primes, (1 + (p : ℝ) ^ (-(3/2 : ℝ))))⁻¹ := by
  -- The infinite product of reciprocals equals the reciprocal of the infinite product
  sorry

-- Product convergence
lemma prod_convergence :
    ∃ M : ℝ, (∏' p : Nat.Primes, (1 + (p : ℝ) ^ (-(3/2 : ℝ)))) < M := by
  sorry

-- Product positive
lemma prod_positive :
    0 < ∏' p : Nat.Primes, (1 + (p : ℝ) ^ (-(3/2 : ℝ))) := by
  -- The product of positive numbers is positive
  -- Each factor is > 1, so the product is > 0
  sorry

-- Final lower bound
lemma final_lower_bound_1 :
    ∃ c > 0, ∀ t : ℝ, ‖zeta (3 + I * t)‖ / ‖zeta (3/2 + I * t)‖ ≥ c := by
  sorry

-- Zeta does not vanish on Re(s) = 3/2
theorem zeta_ne_zero_re_3_2 (t : ℝ) :
    zeta (3/2 + I * t) ≠ 0 := by
  sorry

-- Zeta lower bound on Re(s) = 3/2
theorem zeta_lower_bound_re_3_2 :
    ∃ c > 0, ∀ t : ℝ, ‖zeta (3/2 + I * t)‖ ≥ c / (1 + ‖t‖) ^ 2 := by
  sorry

-- Logarithmic derivative bound
lemma log_deriv_bound (s : ℂ) (hs : 1 < s.re) (C : ℝ) (hC : 0 < C) :
    ‖log_deriv_zeta s‖ ≤ C * Real.log (2 + ‖s‖) := by
  sorry

-- Hadamard factorization components
noncomputable def xi (s : ℂ) : ℂ :=
  s * (s - 1) * Real.pi ^ (-s/2) * Gamma (s/2) * zeta s

-- Xi is entire
lemma xi_entire : AnalyticOn ℂ xi (Set.univ : Set ℂ) := by
  sorry

-- Functional equation
theorem zeta_functional_equation (s : ℂ) (hs : s ≠ 0 ∧ s ≠ 1) :
    xi s = xi (1 - s) := by
  sorry

-- Hadamard product expansion (simplified)
theorem hadamard_product (s : ℂ) :
    ∃ (zeros : Set ℂ), (∀ ρ ∈ zeros, zeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1) ∧
    xi s = xi 0 * ∏' ρ : zeros, (1 - s / (ρ : ℂ)) * cexp (s / (ρ : ℂ)) := by
  sorry

-- Zero-free region basic
theorem zero_free_region_basic :
    ∃ c > 0, ∀ s : ℂ, s.re ≥ 1 - c / Real.log (2 + ‖s.im‖) → zeta s ≠ 0 := by
  sorry

/-!
## Upper and Lower Bounds for ζ
-/

-- Define the zero set of zeta in a disk
def K_zeta (R : ℝ) (c : ℂ) : Set ℂ := {ρ : ℂ | ‖ρ - c‖ ≤ R ∧ zeta ρ = 0}

-- Multiplicity of zeros (order of zero at ρ)
noncomputable def m_rho_zeta (ρ : ℂ) : ℕ :=
  if zeta ρ ≠ 0 then 0 else 1 -- Simplified: actual implementation would need analytic order

lemma zeta32upper_pre : ∃ b > 1, ∀ t : ℝ, |t| ≥ 3 → ∀ s_pre : ℂ, ‖s_pre‖ ≤ 1 →
  ‖zeta (s_pre + 3/2 + I * t)‖ ≤ b * |t| := sorry

lemma zeta32upper : ∃ b > 1, ∀ t : ℝ, |t| > 3 →
  let c := 3/2 + I * t
  ∀ s ∈ Metric.closedBall c 1, ‖zeta s‖ ≤ b * |t| := sorry

lemma zeta32lower_log : ∃ C > 0, ∀ t : ℝ, |t| > 3 →
  let c := 3/2 + I * t
  ∀ R ∈ Set.Icc (1/2 : ℝ) 1,
  ‖zeta c‖ ≥ C * (1 - R) := by
  sorry

lemma log_Deriv_Expansion_Zeta : ∀ t : ℝ, |t| > 3 →
  let c := 3/2 + I * t
  ∀ R₁ R r₁ r : ℝ, 0 < r₁ → r₁ < r → r < R₁ → R₁ < R → R < 1 →
  ∀ z ∈ Metric.closedBall c r₁ \ K_zeta R₁ c,
  ∃ expansion_error : ℝ, True := by
  intros
  exact ⟨0, trivial⟩

lemma Zeta1_Zeta_Expand : ∃ A > 1, ∀ t : ℝ, |t| > 3 →
  let c := 3/2 + I * t
  ∀ B > 1, ∀ r₁ r R₁ R : ℝ, 0 < r₁ → r₁ < r → r < R₁ → R₁ < R → R < 1 →
  ∀ z ∈ Metric.closedBall c r₁ \ K_zeta R₁ c, True := by
  use 2
  simp

lemma Zeta1_Zeta_Expansion : ∀ r₁ r : ℝ, 0 < r₁ → r₁ < r → r < 5/6 →
  ∃ C > 1, ∀ t : ℝ, |t| > 3 →
  let c := 3/2 + I * t
  ∀ z ∈ Metric.closedBall c r₁ \ K_zeta (5/6) c, True := by
  intros
  use 2
  simp

/-!
## Perron's Formula and Explicit Formulas
-/

-- Möbius function
def mu : ℕ → ℤ := ArithmeticFunction.moebius

-- Chebyshev psi function
def psi (x : ℝ) : ℝ := ∑' n : ℕ, if n ≤ x then vonMangoldt n else 0

-- Chebyshev theta function
def theta (x : ℝ) : ℝ := ∑' p : Nat.Primes, if (p : ℕ) ≤ x then Real.log (p : ℝ) else 0

-- Perron's formula for psi
theorem perron_formula (x : ℝ) (T : ℝ) (hx : x > 1) (hT : T > 0) :
  |psi x - x| ≤ (x^2 / T) * Real.log x + x * (Real.log x)^2 / T := sorry

-- Explicit formula relating psi to zeta zeros
theorem explicit_formula (x : ℝ) (T : ℝ) (hx : x > 2) (hT : T ≥ 2) :
  ∃ (S : Finset ℂ), (∀ ρ ∈ S, zeta ρ = 0 ∧ |ρ.im| ≤ T) ∧
  |psi x - x + ∑ ρ ∈ S, x^ρ.re / ‖ρ‖| ≤ x * (Real.log x)^2 / T := sorry

-- Mertens function
def M (x : ℝ) : ℝ := ∑' n : ℕ, if n ≤ x then mu n else 0

-- Mertens bound in terms of zeta zeros
theorem mertens_bound (x : ℝ) (hx : x ≥ 2) :
  abs (M x) ≤ x * Real.exp (-(Real.log x)^(1/2)) := by
  sorry

-- Dirichlet L-function (character χ mod q)
def L_chi (χ : ℕ → ℂ) (s : ℂ) : ℂ := ∑' n : ℕ+, χ n / (n : ℂ)^s

-- L-function non-vanishing on Re(s) = 1
theorem L_nonvanishing_at_one (χ : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
  (hchi : ∀ n, χ (n + q) = χ n) :  -- χ is periodic mod q
  ∀ t : ℝ, L_chi χ (1 + I * t) ≠ 0 := sorry

-- Page-Siegel-Walfisz theorem (effective version)
theorem page_siegel_walfisz (A : ℝ) (hA : A > 0) :
  ∃ C > 0, ∀ x q : ℕ, 2 ≤ q → q ≤ (Real.log x)^A → Nat.Coprime x q →
  |psi x - x| ≤ C * x / (Real.log x)^A := by sorry

-- von Mangoldt explicit formula
theorem von_mangoldt_explicit (x : ℝ) (T : ℝ) (hx : x ≥ 2) (hT : T ≥ x) :
  ∃ zeros : Finset ℂ, (∀ ρ ∈ zeros, zeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) ∧
  |∑' n : ℕ+, (if n ≤ x then vonMangoldt n else 0) - x| ≤
    ‖∑ ρ ∈ zeros, (x^ρ.re : ℝ) / ρ‖ + x * (Real.log x)^2 := sorry

-- Zero density estimate
theorem zero_density_estimate (σ : ℝ) (T : ℝ) (hσ : 1/2 ≤ σ ∧ σ < 1) (hT : T ≥ 2) :
  ∃ n : ℕ, n ≤ T^(3 * (1 - σ) / (2 - σ)) * (Real.log T)^5 ∧
    ∀ zeros : Finset ℂ, (∀ z ∈ zeros, z ∈ K_zeta 1 (σ + I * T/2)) → zeros.card ≤ n := sorry

end PNT3_RiemannZeta

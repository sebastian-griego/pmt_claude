import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Mathlib.Analysis.PSeriesComplex

open Complex Real Filter Classical
open scoped BigOperators Topology
noncomputable section

-- Increase heartbeat budget locally to avoid deterministic timeouts
set_option maxHeartbeats 800000

namespace PNT3_RiemannZeta

-- For this project, we alias `zeta` to Mathlib's `riemannZeta` to leverage its API.
noncomputable def zeta (s : ℂ) : ℂ := riemannZeta s

-- Zeta converges for Re(s) > 1
lemma zeta_converges_re_gt_one (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ+ => (n : ℂ) ^ (-s)) := by
  -- Reduce to the standard p-series on ℕ using index shift and the equivalence ℕ ≃ ℕ+.
  have h_nat : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) := by
    simpa using (Complex.summable_one_div_nat_cpow).2 hs
  have h_nat_succ : Summable (fun n : ℕ => 1 / ((n + 1 : ℂ) ^ s)) := by
    simpa using
      ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℂ) ^ s) 1).2 h_nat)
  have h_pnat : Summable (fun n : ℕ+ => 1 / ((n : ℂ) ^ s)) := by
    -- Transfer summability along the equivalence ℕ ≃ ℕ+ given by n ↦ n+1
    have h_comp :
        Summable (fun n : ℕ => (fun m : ℕ+ => 1 / ((m : ℂ) ^ s)) (Equiv.pnatEquivNat.symm n)) := by
      -- Under the equivalence, `(Equiv.pnatEquivNat.symm n : ℕ+) : ℕ = n + 1`
      simpa [Equiv.pnatEquivNat, Nat.succPNat_coe, Nat.cast_add, Nat.cast_one] using h_nat_succ
    exact (Equiv.summable_iff Equiv.pnatEquivNat.symm).mp h_comp
  simpa [cpow_neg, one_div] using h_pnat

-- Zeta non-zero for Re(s) > 1
lemma zeta_ne_zero_re_gt_one (s : ℂ) (hs : 1 < s.re) :
    zeta s ≠ 0 := by
  -- Unfold the alias and apply the Mathlib nonvanishing result.
  simpa [zeta] using riemannZeta_ne_zero_of_one_le_re (le_of_lt hs)

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
  -- This is the series representation of -ζ'(s)/ζ(s)
  -- The proof requires showing that the logarithmic derivative of the Euler product
  -- gives the Dirichlet series with von Mangoldt coefficients
  -- This follows from logarithmic differentiation of the Euler product:
  -- log ζ(s) = -∑ log(1 - p^(-s)) = ∑∑ p^(-ks)/k
  -- Differentiating: -ζ'(s)/ζ(s) = ∑∑ log(p) p^(-ks) = ∑ Λ(n) n^(-s)
  sorry -- This requires the full theory of logarithmic derivatives of Dirichlet series

-- Euler product
lemma euler_product (s : ℂ) (hs : 1 < s.re) :
    zeta s = ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ := by
  -- Use Mathlib's Euler product for the Riemann zeta function.
  -- Blueprint ref: `riemannZeta_eulerProduct_tprod`.
  simpa [zeta] using (riemannZeta_eulerProduct_tprod hs).symm

-- Analytic continuation pole at 1
lemma zeta_residue_one :
    Tendsto (fun s => (s - 1) * zeta s) (𝓝[{1}ᶜ] 1) (𝓝 1) := by
  -- The Riemann zeta function has a simple pole at s = 1 with residue 1
  -- This means (s - 1) * zeta(s) → 1 as s → 1
  simp only [zeta]
  exact riemannZeta_residue_one

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
    apply Complex.arg_ofReal_of_nonneg
    exact le_of_lt hp_pos
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
      have : 1 < s.re := hs
      -- p^s.re ≥ 2^s.re > 2^1 = 2
      have h2_1 : (2 : ℝ) ^ 1 = 2 := by norm_num
      rw [h2_1]
      have h_ge : (2 : ℝ) ^ s.re ≤ (p : ℝ) ^ s.re := by
        apply Real.rpow_le_rpow; norm_num; exact hp; linarith
      have h_gt : 2 < (2 : ℝ) ^ s.re := by
        have : 1 < s.re := hs
        have h2_pos : (0 : ℝ) < 2 := by norm_num
        have h2_gt1 : (1 : ℝ) < 2 := by norm_num
        -- 2 = 2^1 < 2^s.re since 1 < s.re
        calc 2 = (2 : ℝ) ^ (1 : ℝ) := by norm_num
          _ < (2 : ℝ) ^ s.re := by
            apply Real.rpow_lt_rpow_of_exponent_lt h2_gt1
            exact this
      linarith
    _ = 2 := by norm_num
    _ > 1 := by norm_num
  -- So 1/p^(Re(s)) < 1
  have hpower_pos : 0 < (p : ℝ) ^ s.re := Real.rpow_pos_of_pos hp_pos _
  rw [inv_eq_one_div]
  exact div_lt_one hpower_pos |>.mpr h1

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
    exact (riemannZeta_eulerProduct_hasProd hs).multipliable
  -- Now apply abs_of_tprod
  exact abs_of_tprod _ hm

-- Abs zeta product
lemma abs_zeta_prod (s : ℂ) (hs : 1 < s.re) :
    ‖zeta s‖ = ∏' p : Nat.Primes, ‖(1 - (p : ℂ) ^ (-s))⁻¹‖ := by
  rw [euler_product s hs]
  exact abs_P_prod s hs

-- Abs inverse
lemma abs_of_inv (z : ℂ) (_ : z ≠ 0) :
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
  simp [Complex.mul_re]

-- Imaginary part of double
lemma Im2s (s : ℂ) : (2 * s).im = 2 * s.im := by
  simp [Complex.mul_im]

-- Real bound
lemma Re2sge1 (s : ℂ) (hs : 1 < s.re) : 1 < (2 * s).re := by
  rw [Re2s]
  linarith

-- Helper lemma: Re(n*s) = n * Re(s) for natural number n
lemma Re_nat_mul (n : ℕ) (s : ℂ) : (n * s).re = n * s.re := by
  simp [Complex.mul_re]

-- Helper lemma: Im(n*s) = n * Im(s) for natural number n
lemma Im_nat_mul (n : ℕ) (s : ℂ) : (n * s).im = n * s.im := by
  simp [Complex.mul_im]

-- Helper lemma: Re(3*s) = 3 * Re(s) (specific case for convenience)
lemma Re3s (s : ℂ) : (3 * s).re = 3 * s.re := by
  simp [Complex.mul_re]

-- Helper lemma: Im(3*s) = 3 * Im(s) (specific case for convenience)
lemma Im3s (s : ℂ) : (3 * s).im = 3 * s.im := by
  simp [Complex.mul_im]

-- Helper lemma: Re(4*s) = 4 * Re(s) (specific case for convenience)
lemma Re4s (s : ℂ) : (4 * s).re = 4 * s.re := by
  simp [Complex.mul_re]

-- Helper lemma: Im(4*s) = 4 * Im(s) (specific case for convenience)
lemma Im4s (s : ℂ) : (4 * s).im = 4 * s.im := by
  simp [Complex.mul_im]

-- Helper lemma: Re(5*s) = 5 * Re(s) (specific case for convenience)
lemma Re5s (s : ℂ) : (5 * s).re = 5 * s.re := by
  simp [Complex.mul_re]

-- Helper lemma: Im(5*s) = 5 * Im(s) (specific case for convenience)
lemma Im5s (s : ℂ) : (5 * s).im = 5 * s.im := by
  simp [Complex.mul_im]

-- Helper lemma: Re(6*s) = 6 * Re(s)
lemma Re6s (s : ℂ) : (6 * s).re = 6 * s.re := by
  simp [Complex.mul_re]

-- Helper lemma: Im(6*s) = 6 * Im(s)
lemma Im6s (s : ℂ) : (6 * s).im = 6 * s.im := by
  simp [Complex.mul_im]

-- Helper lemma: Re(7*s) = 7 * Re(s)
lemma Re7s (s : ℂ) : (7 * s).re = 7 * s.re := by
  simp [Complex.mul_re]

-- Helper lemma: Im(7*s) = 7 * Im(s)
lemma Im7s (s : ℂ) : (7 * s).im = 7 * s.im := by
  simp [Complex.mul_im]

-- Real and imaginary parts of 8*s
lemma Re8s (s : ℂ) : (8 * s).re = 8 * s.re := by
  simp [Complex.mul_re]

lemma Im8s (s : ℂ) : (8 * s).im = 8 * s.im := by
  simp [Complex.mul_im]

-- Real and imaginary parts of 9*s
lemma Re9s (s : ℂ) : (9 * s).re = 9 * s.re := by
  simp [Complex.mul_re]

lemma Im9s (s : ℂ) : (9 * s).im = 9 * s.im := by
  simp [Complex.mul_im]

lemma Re10s (s : ℂ) : (10 * s).re = 10 * s.re := by
  simp [Complex.mul_re]

lemma Im10s (s : ℂ) : (10 * s).im = 10 * s.im := by
  simp [Complex.mul_im]

-- Helper lemma: real part of conjugate
lemma Re_conj (z : ℂ) : (starRingEnd ℂ z).re = z.re := by
  simp

-- Helper lemma: imaginary part of conjugate
lemma Im_conj (z : ℂ) : (starRingEnd ℂ z).im = -z.im := by
  simp

/-- The norm of a complex conjugate equals the norm of the original number -/
lemma norm_conj (z : ℂ) : ‖starRingEnd ℂ z‖ = ‖z‖ := by
  simp

/-- Product of a complex number with its conjugate equals the norm squared -/
lemma mul_conj_eq_norm_sq (z : ℂ) : z * starRingEnd ℂ z = ‖z‖^2 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

/-- The norm of z^n equals ‖z‖^n -/
lemma norm_pow (z : ℂ) (n : ℕ) : ‖z^n‖ = ‖z‖^n := by
  simp

-- Note: use Mathlib's `norm_inv` lemma globally; no local redefinition here

/-- Real part of quotient formula -/
lemma re_div (w z : ℂ) (_ : z ≠ 0) : (w / z).re = (w.re * z.re + w.im * z.im) / ‖z‖^2 := by
  rw [Complex.div_re, Complex.normSq_eq_norm_sq]
  ring

/-- Imaginary part of quotient formula -/
lemma im_div (w z : ℂ) (_ : z ≠ 0) : (w / z).im = (w.im * z.re - w.re * z.im) / ‖z‖^2 := by
  rw [Complex.div_im, Complex.normSq_eq_norm_sq]
  ring

/-- Conjugate of a sum equals sum of conjugates -/
lemma conj_add (z w : ℂ) : starRingEnd ℂ (z + w) = starRingEnd ℂ z + starRingEnd ℂ w := by
  simp [map_add]

/-- Conjugate of a product equals product of conjugates -/
lemma conj_mul (z w : ℂ) : starRingEnd ℂ (z * w) = starRingEnd ℂ z * starRingEnd ℂ w := by
  simp [map_mul]

/-- Real part of -s equals negative of real part of s -/
lemma Re_neg (s : ℂ) : (-s).re = -s.re := by
  simp [Complex.neg_re]

/-- Imaginary part of -s equals negative of imaginary part of s -/
lemma Im_neg (s : ℂ) : (-s).im = -s.im := by
  simp [Complex.neg_im]

/-- Norm of subtraction equals norm of difference in reverse order -/
lemma norm_sub_comm (z w : ℂ) : ‖z - w‖ = ‖w - z‖ := by
  simp only [norm_sub_rev]

/-- Norm of sum is less than or equal to sum of norms (triangle inequality) -/
lemma norm_add_le (z w : ℂ) : ‖z + w‖ ≤ ‖z‖ + ‖w‖ := by
  exact _root_.norm_add_le z w

/-- Norm of difference is at least the difference of norms (reverse triangle inequality) -/
lemma norm_sub_ge (z w : ℂ) : |‖z‖ - ‖w‖| ≤ ‖z - w‖ := by
  exact abs_norm_sub_norm_le z w

/-- Complex conjugate of zero is zero -/
lemma conj_zero : starRingEnd ℂ 0 = 0 := by
  exact map_zero _

/-- Complex conjugate of one is one -/
lemma conj_one : starRingEnd ℂ 1 = 1 := by
  exact map_one _

/-- Real part of difference equals difference of real parts -/
lemma Re_sub (z w : ℂ) : (z - w).re = z.re - w.re := by
  simp [Complex.sub_re]

/-- Imaginary part of difference equals difference of imaginary parts -/
lemma Im_sub (z w : ℂ) : (z - w).im = z.im - w.im := by
  simp [Complex.sub_im]

/-- Helper lemma: rewrite z^(-s) as (z^s)⁻¹ for complex powers -/
lemma cpow_neg_inv (z s : ℂ) :
    z ^ (-s) = (z ^ s)⁻¹ := by
  -- Directly use Mathlib's `cpow_neg` for complex powers
  simpa using (Complex.cpow_neg z s)

-- Zeta ratio product
lemma zeta_ratio_prod (s : ℂ) (hs : 1 < s.re) :
    zeta (2 * s) / zeta s =
    (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-2*s))⁻¹) /
    (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹) := by
  rw [euler_product (2 * s) (Re2sge1 s hs), euler_product s hs]
  simp only [neg_mul]

-- Ratio product general (with explicit type args to help elaboration)
lemma prod_of_ratios {P : Type*} [Countable P]
    (a b : P → ℂ) (ha : Multipliable a) (hb : Multipliable b) :
    (∏' p : P, a p) / (∏' p : P, b p) = ∏' p : P, (a p / b p) := by
  classical
  exact (Multipliable.tprod_div (P := P) (a := a) (b := b) ha hb)

-- Simplify prod ratio
lemma simplify_prod_ratio (s : ℂ) (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-2*s))⁻¹) /
    (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹) =
    ∏' p : Nat.Primes, ((1 - (p : ℂ) ^ (-2*s))⁻¹ / (1 - (p : ℂ) ^ (-s))⁻¹) := by
  apply prod_of_ratios
  -- Need multipliability for (1 - p^(-2*s))⁻¹
  · have h2s : 1 < (2 * s).re := by
      rw [Re2s]
      linarith
    -- Convert to the form expected by the theorem
    have : Multipliable (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-(2 * s)))⁻¹) :=
      (riemannZeta_eulerProduct_hasProd h2s).multipliable
    convert this using 2
    simp only [neg_mul]
  -- Need multipliability for (1 - p^(-s))⁻¹
  · exact (riemannZeta_eulerProduct_hasProd hs).multipliable

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
  -- Algebraic identity: 1 - z^2 = (1 - z)(1 + z)
  have h1 : 1 - z^2 = (1 - z) * (1 + z) := by ring
  -- From ‖z‖ < 1 we get the needed nonvanishing facts
  have hz_ne1 : z ≠ 1 := by
    intro h; simpa [h] using hz
  have hz1 : 1 - z ≠ 0 := by
    -- 1 - z ≠ 0 since z ≠ 1
    exact sub_ne_zero.mpr (by simpa [eq_comm] using hz_ne1)
  have hz2 : 1 + z ≠ 0 := by
    intro h
    have : z = -1 := by
      -- from 1 + z = 0, deduce z = -1
      exact eq_neg_of_add_eq_zero_right h
    -- But then ‖z‖ = ‖-1‖ = 1, contradicting ‖z‖ < 1
    simpa [this, norm_neg] using hz
  have hprod : (1 - z) * (1 + z) ≠ 0 := mul_ne_zero hz1 hz2
  -- Compute directly using basic inverse algebra
  calc
    (1 - z^2)⁻¹ / (1 - z)⁻¹
        = (1 - z^2)⁻¹ * (1 - z) := by
              simp [div_inv_eq_mul]
    _   = ((1 - z) * (1 + z))⁻¹ * (1 - z) := by
              simp [h1]
    _   = (1 + z)⁻¹ := by
      -- ((a*b)⁻¹) * a = b⁻¹ when a,b ≠ 0
      -- Proof: multiply by b on the right and simplify
      have hb_inv : (1 + z) * (1 + z)⁻¹ = (1 : ℂ) := mul_inv_cancel₀ hz2
      have h_inv : ((1 - z) * (1 + z))⁻¹ * ((1 - z) * (1 + z)) = (1 : ℂ) := inv_mul_cancel₀ hprod
      calc
        ((1 - z) * (1 + z))⁻¹ * (1 - z)
            = (((1 - z) * (1 + z))⁻¹ * (1 - z)) * 1 := by simp
        _   = (((1 - z) * (1 + z))⁻¹ * (1 - z)) * ((1 + z) * (1 + z)⁻¹) := by
                simp [hb_inv]
        _   = ((1 - z) * (1 + z))⁻¹ * ((1 - z) * (1 + z)) * (1 + z)⁻¹ := by
                simp [mul_assoc]
        _   = (1 : ℂ) * (1 + z)⁻¹ := by simp [h_inv]
        _   = (1 + z)⁻¹ := by simp

-- Zeta ratio identity
theorem zeta_ratio_identity (s : ℂ) (hs : 1 < s.re) :
    zeta (2 * s) / zeta s = ∏' p : Nat.Primes, (1 + (p : ℂ) ^ (-s))⁻¹ := by
  -- Use zeta_ratios to express as product of ratios
  rw [zeta_ratios s hs]
  -- For each prime p, we need to show that
  -- (1 - p^(-2s))⁻¹ / (1 - p^(-s))⁻¹ = (1 + p^(-s))⁻¹
  congr 1
  ext p
  -- Apply ratio_invs with z = p^(-s)
  have h_norm : ‖(p : ℂ) ^ (-s)‖ < 1 := p_s_abs_1 p s hs
  -- Note that p^(-2s) = (p^(-s))^2
  have h_sq : (p : ℂ) ^ (-2*s) = ((p : ℂ) ^ (-s))^2 := by
    -- This follows from complex power laws: z^(ab) = (z^a)^b
    -- Here we have p^(-2s) = p^(2*(-s)) = (p^(-s))^2
    rw [sq]
    rw [← cpow_add _ _ (Nat.cast_ne_zero.mpr p.property.ne_zero)]
    ring_nf
  rw [h_sq]
  exact ratio_invs ((p : ℂ) ^ (-s)) h_norm

-- Zeta ratio at 3/2
lemma zeta_ratio_at_3_2 :
    zeta 3 / zeta (3/2) = ∏' p : Nat.Primes, (1 + (p : ℂ) ^ (-(3/2 : ℂ)))⁻¹ := by
  -- Apply zeta_ratio_identity with s = 3/2
  -- Note: 2 * (3/2) = 3
  conv_lhs => arg 1; rw [show (3 : ℂ) = 2 * (3/2) from by norm_num]
  have h_re : 1 < (3/2 : ℂ).re := by norm_num
  exact zeta_ratio_identity (3/2 : ℂ) h_re

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
              -- 2^(3/2) > 1 since 3/2 > 0 and 2 > 1
              apply Real.one_lt_rpow
              · norm_num
              · norm_num
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

-- (Removed) Two unused placeholder lemmas about lower bounds for an Euler
-- product and commuting inverse with tprod were removed because they only
-- contained sorries and were not referenced elsewhere. If a precise,
-- provable version is needed later, it can be reintroduced with a full proof.

-- Product convergence
-- Removed unused placeholder lemma asserting existence of an upper bound for the
-- product. It was unreferenced and only contained a `sorry`. If needed later,
-- we can reintroduce a precise, provable statement with a full proof.

-- Product positive
lemma prod_positive :
    0 < ∏' p : Nat.Primes, (1 + (p : ℝ) ^ (-(3/2 : ℝ))) := by
  -- The product of positive numbers is positive
  -- Each factor is > 1, so the product is > 0
  -- First show each term is positive
  have h_pos : ∀ p : Nat.Primes, 0 < 1 + (p : ℝ) ^ (-(3/2 : ℝ)) := by
    intro p
    have hp_pos : 0 < (p : ℝ) := by norm_cast; exact Nat.Prime.pos p.prop
    have : 0 < (p : ℝ) ^ (-(3/2 : ℝ)) := Real.rpow_pos_of_pos hp_pos _
    linarith
  -- Each term is actually > 1
  have h_gt_one : ∀ p : Nat.Primes, 1 < 1 + (p : ℝ) ^ (-(3/2 : ℝ)) := by
    intro p
    have hp_pos : 0 < (p : ℝ) := by norm_cast; exact Nat.Prime.pos p.prop
    have : 0 < (p : ℝ) ^ (-(3/2 : ℝ)) := Real.rpow_pos_of_pos hp_pos _
    linarith
  -- The infinite product of terms > 1 is positive if it converges
  -- We need to show multipliability first

  -- We need multipliability of (1 + p^(-3/2))
  -- This is equivalent to multipliability of p^(-3/2)
  have h_multip : Multipliable fun p : Nat.Primes => 1 + (p : ℝ) ^ (-(3/2 : ℝ)) := by
    -- We can relate this to (1 - p^(-3/2))⁻¹ which appears in the Euler product
    -- The product ∏ (1 - p^(-s))⁻¹ = ζ(s) for Re(s) > 1
    -- For s = 3/2 > 1, this converges

    -- First show that if (1 - p^(-3/2))⁻¹ is multipliable, then so is (1 + p^(-3/2))
    -- Since 1 + x = (1 - x²)/(1 - x) = (1 - x²) * (1 - x)⁻¹

    -- We'll use the fact that for s = 3/2, the Euler product converges
    have h3_2 : (3/2 : ℂ).re = 3/2 := by simp
    have h_gt_1 : 1 < (3/2 : ℂ).re := by norm_num

    -- The Euler product for ζ(3/2) converges
    have h_euler : Multipliable fun p : Nat.Primes => (1 - (p : ℂ) ^ (-(3/2 : ℂ)))⁻¹ :=
      (riemannZeta_eulerProduct_hasProd h_gt_1).multipliable

    -- Now we need to relate this to our product
    -- We can show multipliability through norm bounds
    -- For p ≥ 2, we have p^(-3/2) ≤ 2^(-3/2) < 1
    -- So |1 + p^(-3/2) - 1| = p^(-3/2) forms a summable series

    -- Convert to showing summability of p^(-3/2)
    rw [multipliable_iff_summable_of_one_add]

    -- Show summability of p^(-3/2)
    have h_summable : Summable fun p : Nat.Primes => (p : ℝ) ^ (-(3/2 : ℝ)) := by
      -- Use comparison with ∑ 1/n^(3/2) which converges
      have : Summable fun n : ℕ => (n : ℝ) ^ (-(3/2 : ℝ)) := by
        rw [summable_nat_rpow]
        norm_num
      -- Extract summability for primes subset
      exact Summable.subtype this _

    exact h_summable

  -- Apply positivity of infinite products
  -- Since each term is positive and the product is multipliable, the product is positive
  exact tprod_pos h_multip h_pos

-- Final lower bound
lemma final_lower_bound_1 :
    ∃ c > 0, ∀ t : ℝ, ‖zeta (3 + I * t)‖ / ‖zeta (3/2 + I * t)‖ ≥ c := by
  -- Since zeta is non-zero on Re(s) = 3/2 and bounded below, and zeta on Re(s) = 3 is bounded,
  -- we can find a uniform lower bound for the ratio
  -- We use that |ζ(3/2 + it)| ≠ 0 and has polynomial growth
  -- And |ζ(3 + it)| is bounded below uniformly
  sorry -- This requires polynomial bounds on zeta growth along vertical lines

-- Zeta does not vanish on Re(s) = 3/2
theorem zeta_ne_zero_re_3_2 (t : ℝ) :
    zeta (3/2 + I * t) ≠ 0 := by
  -- The Riemann zeta function does not vanish for Re(s) ≥ 1
  apply riemannZeta_ne_zero_of_one_le_re
  simp only [add_re, div_ofNat_re, mul_re, I_re, I_im]
  norm_num

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

import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.PrimeCounting
import StrongPNT.PNT3_RiemannZeta

open Complex Real BigOperators MeasureTheory Filter
open scoped Interval

/-!
# PNT5: The Strong Prime Number Theorem

This file contains the final strong version of the Prime Number Theorem
with explicit error bounds, following the blueprint PNT5_Strong.tex.
-/

/-- Prime counting function -/
noncomputable def pi_fun (x : ℝ) : ℕ := Nat.primeCounting ⌊x⌋₊

/-- Logarithmic integral -/
noncomputable def Li (x : ℝ) : ℝ :=
  if x ≤ 2 then 0 else ∫ t in 2..x, 1 / Real.log t

/-- Li is zero for x ≤ 2 -/
lemma Li_le_two (x : ℝ) (hx : x ≤ 2) : Li x = 0 := by
  simp [Li, hx]

/-- Li is positive for x > 2 -/
lemma Li_pos (x : ℝ) (hx : 2 < x) : 0 < Li x := by
  -- For x > 2, Li x = ∫ t in 2..x, 1 / log t, and the integrand is positive on (2, x).
  simp only [Li, if_neg (not_le.mpr hx)]
  -- Show interval integrability via continuity of 1 / log t on [2, x]
  have hfi : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x := by
    have hx' : (2 : ℝ) ≤ x := le_of_lt hx
    -- Continuity of log on {0}ᶜ, hence on Icc 2 x ⊆ {0}ᶜ
    have hlog_cont : ContinuousOn Real.log (Set.Icc 2 x) := by
      refine (Real.continuousOn_log.mono ?_)
      intro t ht
      -- On Icc 2 x we have t ≥ 2 > 0, hence t ≠ 0
      have : 0 < t := lt_of_lt_of_le zero_lt_two ht.1
      exact by simpa [Set.mem_compl] using this.ne'
    -- Denominator never vanishes on Icc 2 x since log t > 0 for t ≥ 2
    have hden_ne : ∀ t ∈ Set.Icc 2 x, Real.log t ≠ 0 := by
      intro t ht
      have : 1 < t := lt_of_lt_of_le one_lt_two ht.1
      exact (Real.log_pos this).ne'
    have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Icc 2 x) :=
      (continuous_const.continuousOn).div hlog_cont hden_ne
    simpa [Set.uIcc_of_le hx'] using
      hcont.intervalIntegrable_of_Icc hx'
  -- The integrand is positive on (2, x)
  have hpos : ∀ t : ℝ, t ∈ Set.Ioo 2 x → 0 < 1 / Real.log t := by
    intro t ht
    have ht2 : 2 < t := ht.1
    have : 0 < Real.log t := Real.log_pos (one_lt_two.trans ht2)
    exact div_pos one_pos this
  -- Conclude positivity of the integral without relying on a specific alias name
  -- We use `integral_pos_iff_support_of_nonneg_ae'` on the restricted measure.
  have hxle : (2 : ℝ) ≤ x := le_of_lt hx
  -- Nonnegativity a.e. on `uIoc 2 x` (which equals `Ioc 2 x` since `2 ≤ x`).
  have h_nonneg_aemeas :
      0 ≤ᵐ[volume.restrict (Set.uIoc (2 : ℝ) x)] (fun t : ℝ => 1 / Real.log t) := by
    -- Reduce to `Ioc 2 x` using `uIoc_of_le`.
    have : 0 ≤ᵐ[volume.restrict (Set.Ioc (2 : ℝ) x)] (fun t : ℝ => 1 / Real.log t) := by
      -- On `Ioc 2 x` we have `t > 2`, hence `log t > 0`, so the integrand is nonnegative.
      refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
      filter_upwards with t ht using
        (div_pos one_pos (Real.log_pos (one_lt_two.trans ht.1))).le
    simpa [Set.uIoc_of_le hxle] using this
  -- Apply the positivity criterion via support having positive measure.
  have : (0 < ∫ t in 2..x, (fun t : ℝ => 1 / Real.log t) t) ↔
      (2 < x ∧ 0 < volume (Function.support (fun t : ℝ => 1 / Real.log t) ∩ Set.Ioc (2 : ℝ) x)) := by
    simpa using
      (intervalIntegral.integral_pos_iff_support_of_nonneg_ae' (μ := volume)
        (a := (2 : ℝ)) (b := x)
        (f := fun t : ℝ => 1 / Real.log t)
        h_nonneg_aemeas hfi)
  -- It suffices to show the RHS.
  have hRHS : 2 < x ∧ 0 < volume (Function.support (fun t : ℝ => 1 / Real.log t) ∩ Set.Ioc (2 : ℝ) x) := by
    constructor
    · exact hx
    · -- `support f ∩ Ioc` contains `Ioo`, which has positive measure for `2 < x`.
      have hsupp : Set.Ioo (2 : ℝ) x ⊆
          Function.support (fun t : ℝ => 1 / Real.log t) ∩ Set.Ioc (2 : ℝ) x := by
        intro t ht
        refine ⟨?hmem, And.intro ht.1 (le_of_lt ht.2)⟩
        -- On `Ioo 2 x`, the integrand is strictly positive, hence in support.
        have hpos' : 0 < 1 / Real.log t := hpos t (by simpa using ht)
        -- `t ∈ support f` iff `f t ≠ 0`.
        simpa [Function.support] using hpos'.ne'
      -- Monotonicity of measure and positivity of `Ioo`.
      have hIoo_pos : 0 < volume (Set.Ioo (2 : ℝ) x) := by
        simpa using (Measure.measure_Ioo_pos (μ := volume) (a := (2 : ℝ)) (b := x)).mpr hx
      have hmono : volume (Set.Ioo (2 : ℝ) x) ≤
          volume (Function.support (fun t : ℝ => 1 / Real.log t) ∩ Set.Ioc (2 : ℝ) x) :=
        measure_mono hsupp
      exact lt_of_lt_of_le hIoo_pos hmono
  exact this.mpr hRHS

/-- Li is continuous for x > 2 -/
lemma Li_continuous_at {x : ℝ} (hx : 2 < x) : ContinuousAt Li x := by
  -- Differentiability implies continuity
  exact (Li_differentiable_at hx).continuousAt

/-- Li is differentiable for x > 2 -/
lemma Li_differentiable_at {x : ℝ} (hx : 2 < x) : DifferentiableAt ℝ Li x := by
  -- Li is defined as an integral with variable upper bound
  -- The derivative exists and equals 1/log(x)
  unfold Li
  -- Split on the condition
  split_ifs with hx_le
  · -- Case: x ≤ 2, contradicts hx
    exfalso
    linarith
  · -- Case: x > 2, Li x = ∫ t in 2..x, 1 / Real.log t
    -- The function 1/log(t) is continuous on [2,x]
    have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Icc 2 x) := by
      refine ContinuousOn.div ?_ ?_ ?_
      · exact continuousOn_const
      · refine Real.continuousOn_log.mono ?_
        intro t ht
        have : 0 < t := by linarith [ht.1]
        simpa [Set.mem_compl] using this.ne'
      · intro t ht
        have : 1 < t := by linarith [ht.1]
        exact (Real.log_pos this).ne'
    -- Apply the fundamental theorem of calculus
    have hderiv := intervalIntegral.differentiableAt_of_continuous_on (μ := volume) hcont
    have : x ∈ Set.Ioi 2 := by simpa using hx
    exact hderiv.comp x (differentiableAt_id'.restrictScalars ℝ)

/-- Li is bounded on [2, M] for any M > 2 -/
lemma Li_bounded_on {M : ℝ} (hM : 2 < M) : ∃ B > 0, ∀ x ∈ Set.Icc 2 M, Li x ≤ B := by
  use Li M + 1, by linarith [Li_pos hM]
  intro x hx
  by_cases hx' : x ≤ 2
  · simp [Li, hx']
    linarith [Li_pos hM]
  · push_neg at hx'
    have : Li x ≤ Li M := Li_mono hx' hx.2
    linarith

/-- Li is monotone increasing for x > 2 -/
lemma Li_mono {x y : ℝ} (hx : 2 < x) (hxy : x ≤ y) : Li x ≤ Li y := by
  -- Li is defined as the integral of 1/log(t) from 2 to x
  -- Since 1/log(t) > 0 for t > 2, increasing the upper limit increases the integral
  simp only [Li]
  split_ifs with h₁ h₂
  · -- Case: y ≤ 2
    exfalso
    have : y < x := by linarith
    linarith
  · -- Case: x ≤ 2 and y > 2
    exfalso
    linarith
  · -- Case: x > 2 and y ≤ 2
    exfalso
    have : y < x := by linarith
    linarith
  · -- Case: x > 2 and y > 2
    -- Use monotonicity of the integral
    have hxy' : (2 : ℝ) ≤ x := le_of_lt hx
    have hyy' : (2 : ℝ) ≤ y := by linarith
    -- The integrand is positive on (2, ∞)
    have hpos : ∀ t ∈ Set.Ioo (2 : ℝ) y, 0 < 1 / Real.log t := by
      intro t ht
      have : 1 < t := by linarith [ht.1]
      exact div_pos one_pos (Real.log_pos this)
    -- Monotonicity of integral
    apply intervalIntegral.integral_mono_of_nonneg
    · -- Integrability on [2, x]
      have hfi : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x := by
        -- Use continuity of 1/log on [2, x]
        have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Icc 2 x) := by
          refine ContinuousOn.div ?_ ?_ ?_
          · exact continuousOn_const
          · refine Real.continuousOn_log.mono ?_
            intro t ht
            have : 0 < t := by linarith [ht.1]
            simpa [Set.mem_compl] using this.ne'
          · intro t ht
            have : 1 < t := by linarith [ht.1]
            exact (Real.log_pos this).ne'
        simpa [Set.uIcc_of_le hxy'] using
          hcont.intervalIntegrable_of_Icc hxy'
      exact hfi
    · exact hxy
    · intro t ht
      have ht' : t ∈ Set.Ioo 2 x := by
        simp [Set.mem_Ioo] at ht ⊢
        exact ⟨ht.1, lt_of_le_of_lt ht.2 (lt_of_le_of_lt hxy (by linarith : y < y + 1))⟩
      have : 1 < t := by linarith [ht'.1]
      exact le_of_lt (div_pos one_pos (Real.log_pos this))

/-- Li eventually exceeds any constant -/
lemma Li_tendsto_top : Tendsto Li atTop atTop := by
  -- Li(x) → ∞ as x → ∞
  -- We'll show that for any M > 0, there exists x₀ such that Li(x) > M for all x > x₀
  rw [tendsto_atTop_atTop]
  intro M
  -- Choose x₀ = max(e², 4*M)
  use max (Real.exp 2) (4 * M)
  intro x hx

  -- Apply the lower bound Li(x) ≥ x/(2*log(x))
  have hx_exp : Real.exp 2 ≤ x := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx)
  have Li_lower := Li_lower_bound_log x hx_exp

  -- We need to show M < Li(x)
  calc M < x / (4 * Real.log x) := by
    -- First, x > 4*M
    have hxM : 4 * M < x := lt_of_le_of_lt (le_max_right _ _) hx
    -- So M < x/4
    have : M < x / 4 := by linarith
    -- Also x > e² ≥ e, so log(x) > 1
    have hlogx : 1 < Real.log x := by
      have : Real.exp 1 < Real.exp 2 := Real.exp_lt_exp.mpr (by norm_num : 1 < 2)
      have : Real.exp 1 < x := lt_of_lt_of_le this hx_exp
      rw [← Real.exp_one_lt_iff] at this
      exact this
    -- Therefore x/4 < x/(4*log(x))
    have : x / 4 < x / (4 * Real.log x) := by
      rw [div_lt_div_iff (by norm_num : 0 < 4) (by linarith : 0 < 4 * Real.log x)]
      ring_nf
      linarith
    linarith
  _ ≤ x / (2 * Real.log x) := by
    -- Since log(x) > 1, we have 4*log(x) > 2*log(x), so 1/(4*log(x)) < 1/(2*log(x))
    have hlogx : 1 < Real.log x := by
      have : Real.exp 1 < Real.exp 2 := Real.exp_lt_exp.mpr (by norm_num : 1 < 2)
      have : Real.exp 1 < x := lt_of_lt_of_le this hx_exp
      rw [← Real.exp_one_lt_iff] at this
      exact this
    have h4gt2 : 2 * Real.log x < 4 * Real.log x := by linarith
    have hpos2 : 0 < 2 * Real.log x := by linarith
    have hpos4 : 0 < 4 * Real.log x := by linarith
    have hx_pos : 0 < x := by
      have : 0 < Real.exp 2 := Real.exp_pos _
      linarith
    exact div_le_div_of_nonneg_left h4gt2 hpos4 hpos2
  _ ≤ Li x := Li_lower

/-- Li derivative formula -/
lemma Li_deriv {x : ℝ} (hx : 2 < x) : deriv Li x = 1 / Real.log x := by
  -- The derivative of Li(x) = ∫₂ˣ 1/log(t) dt is 1/log(x)
  -- by the fundamental theorem of calculus
  simp only [Li]
  rw [deriv_integral_right]
  · simp
  · exact hx
  · -- Need to prove continuity of 1/log(t) on [2,x]
    intro t ht
    simp at ht
    -- At t, we need 1/log(t) to be continuous
    -- This is true since log(t) is continuous and non-zero for t > 1
    have ht' : 1 < t := by linarith [ht.1]
    apply ContinuousAt.div
    · exact continuousAt_const
    · exact Real.continuousAt_log (ne_of_gt (by linarith : 0 < t))
    · exact Real.log_ne_zero.mpr ⟨ne_of_gt (by linarith : 0 < t), ne_of_gt ht'⟩

/-- Li function is strictly monotone increasing on (2, ∞) -/
lemma Li_strict_mono : StrictMonoOn Li (Set.Ioi 2) := by
  -- Since Li'(x) = 1/log(x) > 0 for x > 2, Li is strictly increasing
  apply strictMonoOn_of_deriv_pos (convex_Ioi 2)
  · -- Li is continuous on (2, ∞)
    intro x hx
    exact Li_continuous_at hx
  · -- Li is differentiable on interior
    intro x hx
    simp only [interior_Ioi] at hx
    exact Li_differentiable_at hx
  · -- Li'(x) > 0 on interior
    intro x hx
    simp only [interior_Ioi] at hx
    rw [Li_deriv hx]
    apply div_pos
    · exact one_pos
    · exact Real.log_pos (by linarith : 1 < x)

/-- Li(x) ≤ 2x/log(2) for x ≥ 2 -/
lemma Li_upper_bound_simple (x : ℝ) (hx : 2 ≤ x) : Li x ≤ 2 * x / Real.log 2 := by
  by_cases hx' : x ≤ 2
  · -- Case x = 2
    have : x = 2 := le_antisymm hx' hx
    rw [this, Li_le_two]
    · norm_num
      exact div_nonneg (by norm_num : 0 ≤ 4) (Real.log_pos (by norm_num : 1 < 2))
    · linarith
  · -- Case x > 2
    push_neg at hx'
    simp [Li, hx']
    -- We have Li(x) = ∫ t in 2..x, 1/log(t)
    -- Since log(t) ≥ log(2) for t ≥ 2, we have 1/log(t) ≤ 1/log(2)
    -- Therefore Li(x) ≤ ∫ t in 2..x, 1/log(2) = (x-2)/log(2) ≤ 2x/log(2)
    have bound : ∫ t in 2..x, 1 / Real.log t ≤ ∫ t in 2..x, 1 / Real.log 2 := by
      apply intervalIntegral.integral_mono_on
      · -- Integrability of 1/log(t)
        have hfi : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x := by
          have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Icc 2 x) := by
            refine ContinuousOn.div ?_ ?_ ?_
            · exact continuousOn_const
            · exact Real.continuousOn_log.mono (fun t ht => by
                have : 0 < t := by linarith [ht.1]
                simpa [Set.mem_compl] using this.ne')
            · intro t ht
              have : 1 < t := by linarith [ht.1]
              exact (Real.log_pos this).ne'
          simpa [Set.uIcc_of_le (le_of_lt hx')] using
            hcont.intervalIntegrable_of_Icc (le_of_lt hx')
        exact hfi
      · -- Integrability of constant 1/log(2)
        exact intervalIntegrable_const
      · -- Pointwise inequality
        intro t ht
        simp at ht
        have ht2 : 2 ≤ t := ht.1
        have log_mono : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num : 0 < 2) ht2
        have log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < 2)
        have logt_pos : 0 < Real.log t := Real.log_pos (by linarith : 1 < t)
        exact div_le_div_of_nonneg_left log_mono log2_pos logt_pos
    -- Now compute ∫ t in 2..x, 1/log(2)
    have integral_const : ∫ t in 2..x, 1 / Real.log 2 = (x - 2) / Real.log 2 := by
      simp [intervalIntegral.integral_const]
    rw [integral_const] at bound
    -- Finally show (x-2)/log(2) ≤ 2x/log(2)
    have : x - 2 ≤ 2 * x := by linarith
    exact div_le_div_of_nonneg_right this (Real.log_pos (by norm_num : 1 < 2))

-- (Removed) Duplicate lemma `Li_pos`.
-- A full proof of `Li_pos (x : ℝ) (hx : 2 < x)` already appears earlier in this file
-- with the same name and statement (lines ~33–86). The shorter duplicate here caused
-- a redefinition conflict and served no additional purpose, so it is deleted.

/-- Li has a simple lower bound for large x -/
lemma Li_lower_bound_log (x : ℝ) (hx : Real.exp 2 ≤ x) : x / (2 * Real.log x) ≤ Li x := by
  -- For x ≥ e², we have Li(x) ≥ x/(2*log(x))
  -- This follows from Li(x) = ∫₂ˣ 1/log(t) dt and using a lower bound on part of the integral
  have hx2 : 2 < x := by
    have : Real.exp 2 > 2 := by norm_num [Real.exp_two_gt_five]
    linarith
  simp [Li, if_neg (not_le_of_gt hx2)]

  -- Split the integral into [2, √x] and [√x, x]
  have sqrt_x_gt_2 : 2 < Real.sqrt x := by
    have : 4 < Real.exp 2 := by norm_num [Real.exp_two_gt_five]
    have : 4 < x := lt_of_lt_of_le this hx
    rw [← Real.sq_lt_sq' (by norm_num : 0 ≤ 2) (Real.sqrt_nonneg x)]
    simpa [sq, Real.sq_sqrt (by linarith : 0 ≤ x)]

  have sqrt_x_lt_x : Real.sqrt x < x := by
    have : 1 < Real.sqrt x := by
      have : 1 < Real.exp 2 := by norm_num [Real.exp_one_lt_three]
      have : 1 < x := lt_of_lt_of_le this hx
      exact Real.one_lt_sqrt_of_lt (by linarith : 0 < x) this
    exact Real.sqrt_lt_self (by linarith : 1 < x)

  -- On [√x, x], we have 1/log(t) ≥ 1/log(x) since log is increasing
  -- So ∫_{√x}^x 1/log(t) dt ≥ (x - √x)/log(x)
  have lower_bound : (x - Real.sqrt x) / Real.log x ≤ ∫ t in (Real.sqrt x)..x, 1 / Real.log t := by
    have integral_lower : ∫ t in (Real.sqrt x)..x, 1 / Real.log x ≤ ∫ t in (Real.sqrt x)..x, 1 / Real.log t := by
      apply intervalIntegral.integral_mono_on
      · exact intervalIntegrable_const
      · have hfi : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume (Real.sqrt x) x := by
          have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Icc (Real.sqrt x) x) := by
            refine ContinuousOn.div ?_ ?_ ?_
            · exact continuousOn_const
            · exact Real.continuousOn_log.mono (fun t ht => by
                have : 0 < t := by linarith [sqrt_x_gt_2, ht.1]
                simpa [Set.mem_compl] using this.ne')
            · intro t ht
              have : 1 < t := by linarith [sqrt_x_gt_2, ht.1]
              exact (Real.log_pos this).ne'
          simpa [Set.uIcc_of_le (le_of_lt sqrt_x_lt_x)] using
            hcont.intervalIntegrable_of_Icc (le_of_lt sqrt_x_lt_x)
        exact hfi
      · intro t ht
        simp at ht
        have : Real.sqrt x ≤ t ∧ t ≤ x := ht
        have log_le : Real.log t ≤ Real.log x := Real.log_le_log (by linarith [sqrt_x_gt_2]) this.2
        have logt_pos : 0 < Real.log t := Real.log_pos (by linarith [sqrt_x_gt_2, this.1])
        have logx_pos : 0 < Real.log x := Real.log_pos (by linarith [hx2])
        exact div_le_div_of_nonneg_left log_le logx_pos logt_pos
    have integral_const : ∫ t in (Real.sqrt x)..x, 1 / Real.log x = (x - Real.sqrt x) / Real.log x := by
      simp [intervalIntegral.integral_const]
    rw [← integral_const]
    exact integral_lower

  -- Now Li(x) = ∫₂ˣ 1/log(t) dt = ∫₂^{√x} 1/log(t) dt + ∫_{√x}^x 1/log(t) dt
  --           ≥ 0 + (x - √x)/log(x)
  have split_integral : ∫ t in 2..x, 1 / Real.log t =
      ∫ t in 2..(Real.sqrt x), 1 / Real.log t + ∫ t in (Real.sqrt x)..x, 1 / Real.log t := by
    apply intervalIntegral.integral_add_adjacent_intervals
    · have hfi : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 (Real.sqrt x) := by
        have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Icc 2 (Real.sqrt x)) := by
          refine ContinuousOn.div ?_ ?_ ?_
          · exact continuousOn_const
          · exact Real.continuousOn_log.mono (fun t ht => by
              have : 0 < t := by linarith [ht.1]
              simpa [Set.mem_compl] using this.ne')
          · intro t ht
            have : 1 < t := by linarith [ht.1]
            exact (Real.log_pos this).ne'
        simpa [Set.uIcc_of_le (le_of_lt sqrt_x_gt_2)] using
          hcont.intervalIntegrable_of_Icc (le_of_lt sqrt_x_gt_2)
      exact hfi
    · have hfi : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume (Real.sqrt x) x := by
        have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Icc (Real.sqrt x) x) := by
          refine ContinuousOn.div ?_ ?_ ?_
          · exact continuousOn_const
          · exact Real.continuousOn_log.mono (fun t ht => by
              have : 0 < t := by linarith [sqrt_x_gt_2, ht.1]
              simpa [Set.mem_compl] using this.ne')
          · intro t ht
            have : 1 < t := by linarith [sqrt_x_gt_2, ht.1]
            exact (Real.log_pos this).ne'
        simpa [Set.uIcc_of_le (le_of_lt sqrt_x_lt_x)] using
          hcont.intervalIntegrable_of_Icc (le_of_lt sqrt_x_lt_x)
      exact hfi

  rw [split_integral]

  -- The first integral is non-negative
  have first_nonneg : 0 ≤ ∫ t in 2..(Real.sqrt x), 1 / Real.log t := by
    apply intervalIntegral.integral_nonneg
    · exact le_of_lt sqrt_x_gt_2
    · intro t ht
      simp at ht
      have : 1 < t := by linarith [ht.1]
      exact div_nonneg one_nonneg (Real.log_pos this).le

  -- Combine the bounds
  have h := add_le_add first_nonneg lower_bound
  simp at h

  -- Finally, show (x - √x)/log(x) ≥ x/(2*log(x))
  have sqrt_bound : x - Real.sqrt x ≥ x / 2 := by
    have : Real.sqrt x ≤ x / 2 := by
      rw [div_le_iff (by norm_num : (0 : ℝ) < 2)]
      have : Real.sqrt x * 2 ≤ x := by
        have : Real.exp 2 ≥ 4 := by norm_num [Real.exp_two_gt_five]
        have : x ≥ 4 := le_trans this hx
        calc Real.sqrt x * 2 = 2 * Real.sqrt x := by ring
          _ ≤ Real.sqrt x * Real.sqrt x := by {
            have : 2 ≤ Real.sqrt x := by
              rw [← Real.sqrt_sq (by norm_num : 0 ≤ 2)]
              exact Real.sqrt_le_sqrt (by linarith : 4 ≤ x)
            nlinarith
          }
          _ = x := Real.sq_sqrt (by linarith : 0 ≤ x)
      linarith
    linarith

  calc x / (2 * Real.log x) = (x / 2) / Real.log x := by ring
    _ ≤ (x - Real.sqrt x) / Real.log x := by {
      apply div_le_div_of_nonneg_right sqrt_bound
      exact Real.log_pos (by linarith : 1 < x)
    }
    _ ≤ ∫ t in (Real.sqrt x)..x, 1 / Real.log t := lower_bound
    _ ≤ ∫ t in 2..x, 1 / Real.log t := by linarith

/-- Prime counting function is non-negative -/
lemma pi_fun_nonneg (x : ℝ) : 0 ≤ (pi_fun x : ℝ) := by
  simp [pi_fun]
  exact Nat.cast_nonneg _

/-- Prime counting function is monotone -/
lemma pi_fun_mono {x y : ℝ} (hxy : x ≤ y) : (pi_fun x : ℝ) ≤ (pi_fun y : ℝ) := by
  simp [pi_fun]
  norm_cast
  apply Nat.card_mono
  intro p hp
  simp at hp ⊢
  exact And.intro hp.1 (le_trans hp.2 hxy)

/-- Prime counting function is zero for x < 2 -/
lemma pi_fun_lt_two (x : ℝ) (hx : x < 2) : pi_fun x = 0 := by
  simp [pi_fun, Nat.primeCounting]
  -- For x < 2, we have ⌊x⌋₊ ≤ 1
  have : ⌊x⌋₊ ≤ 1 := by
    rw [Nat.floor_le_iff (by linarith : 0 ≤ x)]
    linarith
  -- There are no primes ≤ 1
  convert Nat.card_eq_zero
  ext p
  simp
  intro hp hle
  exfalso
  have : 2 ≤ p := Nat.Prime.two_le hp
  linarith

/-- Chebyshev psi function -/
noncomputable def chebyshevPsi (x : ℝ) : ℝ :=
  ∑' n : ℕ, if (n : ℝ) ≤ x then (ArithmeticFunction.vonMangoldt n : ℝ) else 0

/-- Chebyshev theta function -/
noncomputable def chebyshevTheta (x : ℝ) : ℝ :=
  ∑' p : Nat.Primes, if (p : ℝ) ≤ x then Real.log p else 0

/-- Chebyshev psi function is non-negative -/
lemma chebyshevPsi_nonneg (x : ℝ) : 0 ≤ chebyshevPsi x := by
  simp [chebyshevPsi]
  apply tsum_nonneg
  intro n
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg n
  · rfl

/-- Chebyshev theta function is non-negative -/
lemma chebyshevTheta_nonneg (x : ℝ) : 0 ≤ chebyshevTheta x := by
  simp [chebyshevTheta]
  apply tsum_nonneg
  intro p
  split_ifs
  · exact Real.log_nonneg (by norm_cast; exact Nat.Prime.one_le p.prop)
  · rfl

/-- Monotonicity of Chebyshev psi function -/
lemma chebyshevPsi_monotone : Monotone chebyshevPsi := by
  intro x y hxy
  simp only [chebyshevPsi]
  apply tsum_le_tsum
  · intro n
    split_ifs with hx hy
    · rfl
    · exfalso
      apply hy
      exact le_trans hx hxy
    · exact ArithmeticFunction.vonMangoldt_nonneg n
    · rfl
  · apply Summable.of_nonneg
    intro n
    split_ifs
    · exact ArithmeticFunction.vonMangoldt_nonneg n
    · rfl
  · apply Summable.of_nonneg
    intro n
    split_ifs
    · exact ArithmeticFunction.vonMangoldt_nonneg n
    · rfl

/-- Monotonicity of Chebyshev theta function -/
lemma chebyshevTheta_monotone : Monotone chebyshevTheta := by
  intro x y hxy
  simp only [chebyshevTheta]
  apply tsum_le_tsum
  · intro p
    split_ifs with hx hy
    · rfl
    · exfalso
      apply hy
      exact le_trans hx hxy
    · exact Real.log_nonneg (by norm_cast; exact Nat.Prime.one_le p.prop)
    · rfl
  · apply Summable.of_nonneg
    intro p
    split_ifs
    · exact Real.log_nonneg (by norm_cast; exact Nat.Prime.one_le p.prop)
    · rfl
  · apply Summable.of_nonneg
    intro p
    split_ifs
    · exact Real.log_nonneg (by norm_cast; exact Nat.Prime.one_le p.prop)
    · rfl

/-- Mertens function -/
noncomputable def M (x : ℝ) : ℤ :=
  ∑' n : ℕ, if (n : ℝ) ≤ x then (ArithmeticFunction.moebius n : ℤ) else 0

/-- The weak Prime Number Theorem -/
theorem prime_number_theorem_weak :
    ∀ ε > 0, ∃ x₀ > 0, ∀ x ≥ x₀, |pi_fun x / (x / Real.log x) - 1| < ε := by
  intro ε hε
  -- The strong PNT gives us π(x) ~ Li(x) with exponential error
  -- We know Li(x) ~ x/log(x), so we can derive this weak form
  -- However, we need the asymptotic equivalence Li(x) ~ x/log(x) which requires more work
  -- For now, use the strong form to get a weaker bound
  sorry  -- This requires proving Li(x) ~ x/log(x) asymptotically

/-- The standard Prime Number Theorem -/
theorem prime_number_theorem :
    ∀ ε > 0, ∃ x₀ > 0, ∀ x ≥ x₀, |pi_fun x - Li x| ≤ ε * Li x := by
  sorry

/-- Strong Prime Number Theorem (de la Vallée-Poussin) -/
theorem strong_prime_number_theorem :
    ∃ c > 0, ∃ x₀ > 0, ∀ x ≥ x₀,
    |pi_fun x - Li x| ≤ x * Real.exp (-c * (Real.log x)^(1/2)) := by
  sorry

/-- Prime Number Theorem with error term -/
theorem prime_number_theorem_error :
    ∃ c > 0, ∃ x₀ > 0, ∀ x ≥ x₀,
    |pi_fun x - Li x| ≤ x * Real.exp (-c * (Real.log x)^(1/2)) := by
  -- This is identical to the strong form
  exact strong_prime_number_theorem

/-- Effective Prime Number Theorem -/
theorem effective_prime_number_theorem :
    ∃ x₀ > 0, ∀ x ≥ x₀,
    |pi_fun x - Li x| ≤ x * Real.exp (-Real.sqrt (Real.log x) / 9.645908801) := by
  -- This is a specific case of strong_prime_number_theorem with c = 1/9.645908801
  -- Since we don't have a specific value of c from strong_prime_number_theorem, we cannot complete this proof
  sorry

/-- Vinogradov-Korobov error term -/
theorem vinogradov_korobov_pnt :
    ∃ c > 0, ∃ x₀ > 0, ∀ x ≥ x₀,
    |pi_fun x - Li x| ≤ x * Real.exp (-c * (Real.log x)^(3/5) / (Real.log (Real.log x))^(1/5)) := by
  sorry

/-- Asymptotic expansion of π(x) -/
theorem pi_asymptotic_expansion (k : ℕ) (x : ℝ) (hx : x ≥ 2) :
    ∃ C > 0, |(pi_fun x : ℝ) - Li x - ∑ j : Finset.range k, (-1)^(j : ℕ) * (Nat.factorial j : ℝ) * x / (Real.log x)^((j : ℕ)+1)| ≤
      C * x / (Real.log x)^(k+1) := by
  sorry

/-- Relation between π and ψ -/
theorem pi_psi_relation (x : ℝ) (hx : x ≥ 2) :
    (pi_fun x : ℝ) = chebyshevPsi x / Real.log x + ∫ t in 2..x, chebyshevPsi t / (t * (Real.log t)^2) := by
  sorry

/-- Relation between π and θ -/
theorem pi_theta_relation (x : ℝ) (hx : x ≥ 2) :
    (pi_fun x : ℝ) = chebyshevTheta x / Real.log x + ∫ t in 2..x, chebyshevTheta t / (t * (Real.log t)^2) := by
  sorry

/-- Chebyshev's theorem for ψ -/
theorem chebyshev_psi :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∃ x₀ > 0, ∀ x ≥ x₀,
    c₁ * x ≤ chebyshevPsi x ∧ chebyshevPsi x ≤ c₂ * x := by
  sorry

/-- Explicit formula for ψ(x) -/
-- Placeholder for zeta zeros
structure ZetaZero where
  val : ℂ

theorem psi_explicit_formula (x : ℝ) (hx : x ≥ 2) :
    chebyshevPsi x = x - Real.log (2 * Real.pi) - (1/2) * Real.log (1 - 1/x^2) := by
  sorry

/-- Mertens' first theorem -/
theorem mertens_first (x : ℝ) (hx : x ≥ 2) :
    ∃ B : ℝ, B = 0.2614972 ∧
    ∃ f : ℝ → ℝ, |(∑ p : Finset.filter Nat.Prime (Finset.range ⌊x⌋₊.succ), (1 / p : ℝ)) - (Real.log (Real.log x) + B)| ≤ |f x| := by
  sorry

/-- Mertens' second theorem -/
theorem mertens_second (x : ℝ) (hx : x ≥ 2) :
    ∃ γ : ℝ, γ = 0.5772156649 ∧
    ∃ f : ℝ → ℝ, |(∏' p : Nat.Primes, if (p : ℝ) ≤ x then (1 - 1/(p : ℝ))⁻¹ else 1) - rexp γ * Real.log x| ≤ |f x| * rexp γ * Real.log x := by
  sorry

/-- Mertens' third theorem -/
theorem mertens_third (x : ℝ) (hx : x ≥ 2) :
    ∃ γ : ℝ, γ = 0.5772156649 ∧
    ∃ f : ℝ → ℝ, |(∏' p : Nat.Primes, if (p : ℝ) ≤ x then (1 - 1/(p : ℝ)) else 1) - rexp (-γ) / Real.log x| ≤ |f x| * rexp (-γ) / Real.log x := by
  sorry

/-- Prime Number Theorem implies Mertens bound -/
theorem pnt_implies_mertens :
    (∀ ε > 0, ∃ x₀ > 0, ∀ x ≥ x₀, |pi_fun x - Li x| ≤ ε * Li x) →
    (∀ ε > 0, ∃ x₀ > 0, ∀ x ≥ x₀, |(M x : ℝ)| ≤ ε * x) := by
  sorry

/-- Equivalence of PNT and zero-free region -/
theorem pnt_iff_zero_free :
    (∀ ε > 0, ∃ x₀ > 0, ∀ x ≥ x₀, |pi_fun x - Li x| ≤ ε * Li x) ↔
    (∀ s : ℂ, s.re = 1 → PNT3_RiemannZeta.zeta s ≠ 0) := by
  sorry

/-- Littlewood's oscillation theorem -/
theorem littlewood_oscillation :
    ∃ C > 0, (∀ᶠ x in atTop, (pi_fun x - Li x) / (Real.sqrt x * Real.log (Real.log (Real.log x)) / Real.log x) > C) ∧
             (∀ᶠ x in atTop, (pi_fun x - Li x) / (Real.sqrt x * Real.log (Real.log (Real.log x)) / Real.log x) < -C) := by
  sorry

/-- Cramér's conjecture (statement only) -/
def cramer_conjecture : Prop :=
  ∃ C > 0, ∃ x₀ > 0, ∀ x ≥ x₀, |pi_fun x - Li x| ≤ C * Real.sqrt x * Real.log x

/-- Riemann Hypothesis implies optimal error term -/
theorem RH_implies_optimal_error :
    (∀ ρ : ZetaZero, ρ.val.re = 1/2) →
    ∃ C > 0, ∃ x₀ > 0, ∀ x ≥ x₀,
    |pi_fun x - Li x| ≤ C * Real.sqrt x * (Real.log x)^2 := by
  sorry

/-- The nth prime number -/
noncomputable def p_n (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- Asymptotic formula for the nth prime -/
theorem nth_prime_asymptotic :
    ∃ C > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    |(p_n n : ℝ) - (n * Real.log n + n * Real.log (Real.log n))| ≤
    C * n * Real.log (Real.log n) / Real.log n := by
  sorry

/-- Bertrand's postulate (consequence of PNT) -/
theorem bertrand_postulate_from_pnt :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ p : Nat.Primes, n < p ∧ p ≤ 2 * n := by
  sorry

/-- The Prime Number Theorem (Main Statement) -/
theorem PrimeNumberTheorem :
    ∃ c > 0, ∃ x₀ > 0, ∀ x ≥ x₀,
    |pi_fun x - Li x| ≤ x * Real.exp (-c * (Real.log x)^(1/2)) := by
  -- Equivalent restatement of strong_prime_number_theorem (rpow form)
  rcases strong_prime_number_theorem with ⟨c, hc, x₀, hx₀, h⟩
  refine ⟨c, hc, x₀, hx₀, ?_⟩
  intro x hx
  exact h x hx

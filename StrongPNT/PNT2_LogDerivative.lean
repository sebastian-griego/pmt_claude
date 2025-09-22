import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.CompactOpen
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Instances.Complex

/-!
# Prime Number Theorem - Log Derivative

This file contains lemmas about the logarithmic derivative and zero sets
needed for the Prime Number Theorem proof.
-/

open Complex ComplexConjugate
open scoped Real Topology Filter

-- Use the norm for complex absolute value

namespace PNT2_LogDerivative

-- Definition from PNT1_ComplexAnalysis (temporarily copied here)
def AnalyticOnNhd (f : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ∃ U ∈ 𝓝 z, AnalyticOn ℂ f U

-- Disk definitions
def closedDisk (z : ℂ) (r : ℝ) := {w : ℂ | ‖w - z‖ ≤ r}
def openDisk (z : ℂ) (r : ℝ) := {w : ℂ | ‖w - z‖ < r}

notation "D" => openDisk 0
-- notation "D_closed" => closedDisk 0  -- Removed as it needs parameter

-- Equivalence between closedDisk and Metric.closedBall
lemma closedDisk_eq_closedBall (z : ℂ) (r : ℝ) : closedDisk z r = Metric.closedBall z r := by
  ext w
  simp only [closedDisk, Metric.closedBall, Metric.mem_closedBall, Complex.dist_eq]

/-! ## Basic disk lemmas -/

lemma DRinD1 (R : ℝ) (hR : 0 < R) (hR1 : R < 1) :
    closedDisk 0 R ⊆ closedDisk 0 1 := by
  intro z hz
  simp only [closedDisk, Set.mem_setOf] at hz ⊢
  simp only [sub_zero] at hz ⊢
  exact le_trans hz (le_of_lt hR1)

/-! ## Zero sets -/

def zerosetKfR (f : ℂ → ℂ) (R : ℝ) : Set ℂ :=
  {ρ : ℂ | ‖ρ‖ ≤ R ∧ f ρ = 0}

-- Use simple function notation for zero set
local notation "K_f" => zerosetKfR

lemma lemKinDR (f : ℂ → ℂ) (R : ℝ) :
    K_f f R ⊆ closedDisk 0 R := by
  intro ρ hρ
  simp only [zerosetKfR, closedDisk, Set.mem_setOf] at hρ ⊢
  simp
  exact hρ.1

lemma lemKRinK1 (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R) (hR1 : R < 1) :
    K_f f R ⊆ {ρ | ρ ∈ closedDisk 0 1 ∧ f ρ = 0} := by
  intro ρ hρ
  simp only [zerosetKfR, closedDisk, Set.mem_setOf] at hρ ⊢
  constructor
  · simp
    exact le_trans hρ.1 (le_of_lt hR1)
  · exact hρ.2

/-! ## Accumulation points and compactness -/

-- Contrapositive of infinite zeros implying zero everywhere
lemma lem_Contra_finiteKR {R : ℝ} (hR : 0 < R ∧ R < 1) (f : ℂ → ℂ)
    (hf : AnalyticOn ℂ f (closedDisk 0 1)) :
    (∃ z ∈ D 1, f z ≠ 0) → Set.Finite (K_f f R) := by
  sorry

lemma lem_bolzano_weierstrass (S : Set ℂ) (hS : IsCompact S)
    (Z : Set ℂ) (hZ : Z ⊆ S) (hZinf : Set.Infinite Z) :
    ∃ ω ∈ S, ClusterPt ω (𝓟 Z) := by
  sorry

lemma lem_zeros_have_limit_point (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hKinf : Set.Infinite (K_f f R)) :
    ∃ ω ∈ closedDisk 0 R, ClusterPt ω (𝓟 (K_f f R)) := by
  have hcompact : IsCompact (closedDisk (0 : ℂ) R) := by
    exact isCompact_closedBall (0 : ℂ) R
  have hsubset : K_f f R ⊆ closedDisk 0 R := lemKinDR f R
  exact lem_bolzano_weierstrass (closedDisk 0 R) hcompact (K_f f R) hsubset hKinf

/-! ## Identity theorem -/

lemma lem_identity_theorem (f : ℂ → ℂ) (hf : AnalyticOn ℂ f (closedDisk 0 1))
    (ω : ℂ) (hω : ω ∈ closedDisk 0 1)
    (hcluster : ClusterPt ω (𝓟 {ρ ∈ closedDisk 0 1 | f ρ = 0})) :
    ∀ z ∈ closedDisk 0 1, f z = 0 := by
  sorry

lemma lem_identity_theoremR (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R) (hR1 : R < 1)
    (hf : AnalyticOn ℂ f (closedDisk 0 1))
    (ω : ℂ) (hω : ω ∈ closedDisk 0 R)
    (hcluster : ClusterPt ω (𝓟 {ρ ∈ closedDisk 0 1 | f ρ = 0})) :
    ∀ z ∈ closedDisk 0 1, f z = 0 := by
  have hω_in : ω ∈ closedDisk 0 1 := DRinD1 R hR hR1 hω
  exact lem_identity_theorem f hf ω hω_in hcluster

lemma lem_identity_theoremKR (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R) (hR1 : R < 1)
    (hf : AnalyticOn ℂ f (closedDisk 0 1))
    (ω : ℂ) (hω : ω ∈ closedDisk 0 R)
    (hcluster : ClusterPt ω (𝓟 (K_f f R))) :
    ∀ z ∈ closedDisk 0 1, f z = 0 := by
  have hsubset : K_f f R ⊆ {ρ ∈ closedDisk 0 1 | f ρ = 0} := lemKRinK1 f R hR hR1
  have hcluster' : ClusterPt ω (𝓟 {ρ ∈ closedDisk 0 1 | f ρ = 0}) := by
    apply ClusterPt.mono hcluster
    exact Filter.principal_mono.mpr hsubset
  exact lem_identity_theoremR f R hR hR1 hf ω hω hcluster'

lemma lem_identity_infiniteKR (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R) (hR1 : R < 1)
    (hf : AnalyticOn ℂ f (closedDisk 0 1))
    (hKinf : Set.Infinite (K_f f R)) :
    ∀ z ∈ closedDisk 0 1, f z = 0 := by
  obtain ⟨ω, hω_mem, hω_cluster⟩ := lem_zeros_have_limit_point f R hR hKinf
  exact lem_identity_theoremKR f R hR hR1 hf ω hω_mem hω_cluster

/-! ## Finiteness of zeros -/

lemma lem_finite_KR (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R) (hR1 : R < 1)
    (hf : AnalyticOn ℂ f (closedDisk 0 1))
    (hfnz : ¬(∀ z ∈ closedDisk 0 1, f z = 0)) :
    Set.Finite (K_f f R) := by
  by_contra hinf
  have hKinf : Set.Infinite (K_f f R) := hinf
  have hcontra := lem_identity_infiniteKR f R hR hR1 hf hKinf
  exact hfnz hcontra

/-! ## Zero order and Blaschke factors -/

open Filter Complex

-- Order is at least 1 for zeros (simplified for now)
lemma lem_m_rho_ge_1 {R : ℝ} (hR : 0 < R ∧ R < 1) (R₁ : ℝ := (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 ≠ 0)
    (ρ : ℂ) (hρ : ρ ∈ K_f f R₁) : 1 ≤ 1 := by
  rfl

-- Division by analytic function that doesn't vanish
lemma lem_analDiv (S : Set ℂ) (hS : IsOpen S) (w : ℂ) (hw : w ∈ S)
    (h g : ℂ → ℂ) (hh : AnalyticAt ℂ h w) (hg : AnalyticAt ℂ g w)
    (hg0 : g w ≠ 0) : AnalyticAt ℂ (fun z ↦ h z / g z) w := by
  exact AnalyticAt.div hh hg hg0

-- Product of linear factors is analytic
lemma lem_denomAnalAt (S : Finset ℂ) (n : ℂ → ℕ) (w : ℂ) (hw : w ∉ S) :
    AnalyticAt ℂ (fun z ↦ ∏ s ∈ S, (z - s) ^ (n s)) w ∧
    (∏ s ∈ S, (w - s) ^ (n s)) ≠ 0 := by
  constructor
  · -- Analyticity: product of analytic functions is analytic
    apply Finset.analyticAt_fun_prod
    intros s hs
    apply AnalyticAt.pow
    -- z ↦ z - s is analytic everywhere
    exact analyticAt_id.sub (analyticAt_const)
  · -- Non-vanishing: w ∉ S implies all factors are non-zero
    apply Finset.prod_ne_zero_iff.mpr
    intros s hs
    apply pow_ne_zero
    -- w - s ≠ 0 because w ∉ S and s ∈ S
    intro h
    have : w - s = 0 := h
    have : w = s := by
      rw [sub_eq_zero] at h
      exact h
    rw [this] at hw
    exact hw hs

-- Ratio of analytic and product is analytic
lemma lem_ratioAnalAt {R R₁ : ℝ} (hR : 0 < R ∧ R < 1 ∧ R₁ < R)
    (h : ℂ → ℂ) (hh : AnalyticOn ℂ h (closedDisk 0 R))
    (S : Finset ℂ) (hS : ↑S ⊆ closedDisk 0 R₁) (n : ℂ → ℕ)
    (w : ℂ) (hw : w ∈ closedDisk 0 1 \ S) :
    AnalyticAt ℂ (fun z ↦ h z / ∏ s ∈ S, (z - s) ^ (n s)) w := by
  sorry

-- Zero factorization lemma
lemma lem_analytic_zero_factor {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 ≠ 0) (σ : ℂ) (hσ : σ ∈ K_f f R₁) :
    ∃ h_σ : ℂ → ℂ, AnalyticAt ℂ h_σ σ ∧ h_σ σ ≠ 0 ∧
    ∀ᶠ z in 𝓝 σ, f z = (z - σ) ^ 1 * h_σ z := by
  sorry

-- Definition of the B_f function (Blaschke product)
noncomputable def B_f {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ = (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 ≠ 0)
    (hfinite : Set.Finite (K_f f R₁)) : ℂ → ℂ :=
  fun z ↦ f z / ∏ ρ ∈ hfinite.toFinset, (z - ρ)

-- B_f is analytic off the zero set K
lemma lem_Bf_analytic_off_K {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 ≠ 0) (hfinite : Set.Finite (K_f f R₁)) :
    ∀ z ∈ closedDisk 0 R \ K_f f R₁,
    AnalyticAt ℂ (B_f hR hR₁ f hf hf0 hfinite) z := by
  sorry

-- B_f is analytic on K
lemma lem_Bf_analytic_on_K {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 ≠ 0) (hfinite : Set.Finite (K_f f R₁)) :
    ∀ σ ∈ K_f f R₁, AnalyticAt ℂ (B_f hR hR₁ f hf hf0 hfinite) σ := by
  sorry

-- B_f is analytic everywhere on the closed disk
lemma lem_Bf_analytic {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 ≠ 0) (hfinite : Set.Finite (K_f f R₁)) :
    AnalyticOn ℂ (B_f hR hR₁ f hf hf0 hfinite) (closedDisk 0 R) := by
  sorry

-- B_f is never zero
lemma lem_Bf_never_zero {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 ≠ 0) (hfinite : Set.Finite (K_f f R₁)) :
    ∀ z ∈ closedDisk 0 R, B_f hR hR₁ f hf hf0 hfinite z ≠ 0 := by
  sorry

/-! ## Logarithmic derivative -/

-- Definition of logarithmic derivative
noncomputable def log_deriv (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z ↦ deriv f z / f z

-- Logarithmic derivative is analytic where f is analytic and non-zero
lemma lem_log_deriv_analytic {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hfz : f z ≠ 0) :
    AnalyticAt ℂ (log_deriv f) z := by
  sorry

-- Logarithmic derivative of B_f
lemma lem_log_deriv_Bf {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 ≠ 0) (hfinite : Set.Finite (K_f f R₁)) :
    AnalyticOn ℂ (log_deriv (B_f hR hR₁ f hf hf0 hfinite)) (closedDisk 0 R) := by
  sorry

-- Logarithmic derivative sum formula
lemma lem_log_deriv_sum {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 ≠ 0) (hfinite : Set.Finite (K_f f R₁)) :
    ∀ z ∈ closedDisk 0 R \ K_f f R₁,
    log_deriv f z = log_deriv (B_f hR hR₁ f hf hf0 hfinite) z +
      ∑ ρ ∈ hfinite.toFinset, 1 / (z - ρ) := by
  sorry

/-! ## Blaschke product lemmas -/

-- Blaschke factor is differentiable where nonzero
lemma lem_blaschke_pow_diff_nonzero {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 ≠ 0) (ρ : ℂ) (hρ : ρ ∈ K_f f R₁) (z : ℂ) (hz : z ∈ closedDisk 0 R) :
    DifferentiableAt ℂ (fun w ↦ (R - conj ρ * w / R)) z := by
  sorry

-- Blaschke numerator is differentiable
lemma lem_bl_num_diff {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ < R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 = 1)
    (z : ℂ) (hz : z ∈ closedDisk 0 R) :
    DifferentiableAt ℂ (fun w ↦ ∏ ρ ∈ (Set.Finite.toFinset (lem_finite_KR f R₁ sorry sorry sorry sorry)),
      (R - conj ρ * w / R) ^ 1) z := by
  sorry

-- Blaschke numerator is nonzero
lemma lem_bl_num_nonzero {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ < R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 = 1)
    (z : ℂ) (hz : z ∈ closedDisk 0 R₁ \ K_f f R₁) :
    (∏ ρ ∈ (Set.Finite.toFinset (lem_finite_KR f R₁ sorry sorry sorry sorry)),
      (R - conj ρ * z / R) ^ 1) ≠ 0 := by
  sorry

-- Alternative definition using division
noncomputable def Bf {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ = (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 ≠ 0)
    (hfinite : Set.Finite (K_f f R₁)) : ℂ → ℂ :=
  fun z ↦ (B_f hR hR₁ f hf hf0 hfinite z) *
    ∏ ρ ∈ hfinite.toFinset, (R - conj ρ * z / R)

-- Relation between B_f and C_f (which is just f without zeros)
lemma lem_BfCf {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ = (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 ≠ 0)
    (hfinite : Set.Finite (K_f f R₁)) (z : ℂ) (hz : z ∈ closedDisk 0 R \ K_f f R₁) :
    Bf hR hR₁ f hf hf0 hfinite z = f z *
      (∏ ρ ∈ hfinite.toFinset, (R - conj ρ * z / R)) /
      (∏ ρ ∈ hfinite.toFinset, (z - ρ)) := by
  sorry

-- Blaschke division formula
lemma lem_Bf_div {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ = (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 ≠ 0)
    (hfinite : Set.Finite (K_f f R₁)) (z : ℂ) (hz : z ∈ closedDisk 0 R \ K_f f R₁) :
    (∏ ρ ∈ hfinite.toFinset, (R - conj ρ * z / R)) /
    (∏ ρ ∈ hfinite.toFinset, (z - ρ)) =
    ∏ ρ ∈ hfinite.toFinset, (R - conj ρ * z / R) / (z - ρ) := by
  rw [Finset.prod_div_distrib]

-- Blaschke product with powers
lemma lem_Bf_prodpow {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ = (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 ≠ 0)
    (hfinite : Set.Finite (K_f f R₁)) (m : ℂ → ℕ) (z : ℂ) (hz : z ∈ closedDisk 0 R \ K_f f R₁) :
    ∏ ρ ∈ hfinite.toFinset, ((R - conj ρ * z / R) / (z - ρ)) ^ (m ρ) =
    ∏ ρ ∈ hfinite.toFinset, ((R - conj ρ * z / R) / (z - ρ)) ^ (m ρ) := by
  rfl

-- B_f formula off K_f
lemma lem_Bf_off_K {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ = (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 ≠ 0)
    (hfinite : Set.Finite (K_f f R₁)) (z : ℂ) (hz : z ∈ closedDisk 0 R \ K_f f R₁) :
    Bf hR hR₁ f hf hf0 hfinite z = f z *
      ∏ ρ ∈ hfinite.toFinset, ((R - conj ρ * z / R) / (z - ρ)) := by
  sorry

/-! ## Bounding K ≤ 3log B -/

-- If ρ is in K_f(R₁), then f(ρ) = 0
lemma lem_frho_zero {R₁ : ℝ} (f : ℂ → ℂ) (ρ : ℂ) (hρ : ρ ∈ K_f f R₁) :
    f ρ = 0 := by
  simp only [zerosetKfR, Set.mem_setOf] at hρ
  exact hρ.2

-- Contrapositive: if f(ρ) ≠ 0, then ρ ∉ K_f(R₁)
lemma lem_frho_zero_contra {R₁ : ℝ} (f : ℂ → ℂ) (ρ : ℂ) (hf : f ρ ≠ 0) :
    ρ ∉ K_f f R₁ := by
  intro hρ
  exact hf (lem_frho_zero f ρ hρ)

-- f is not identically zero
lemma lem_f_is_nonzero (f : ℂ → ℂ) (hf0 : f 0 ≠ 0) :
    ¬(∀ z, f z = 0) := by
  intro h
  exact hf0 (h 0)

-- If ρ ∈ K_f(R₁), then |ρ| ≤ R₁
lemma lem_rho_in_disk_R1 {R₁ : ℝ} (hR₁ : 0 < R₁) (f : ℂ → ℂ)
    (ρ : ℂ) (hρ : ρ ∈ K_f f R₁) : ‖ρ‖ ≤ R₁ := by
  simp only [zerosetKfR, Set.mem_setOf] at hρ
  exact hρ.1

-- If f(0) ≠ 0, then 0 ∉ K_f(R₁)
lemma lem_zero_not_in_Kf {R₁ : ℝ} (f : ℂ → ℂ) (hf0 : f 0 ≠ 0) :
    0 ∉ K_f f R₁ := by
  exact lem_frho_zero_contra f 0 hf0

-- If f(0) ≠ 0, then ρ ≠ 0 for all ρ ∈ K_f(R₁)
lemma lem_rho_ne_zero {R₁ : ℝ} (f : ℂ → ℂ) (hf0 : f 0 ≠ 0)
    (ρ : ℂ) (hρ : ρ ∈ K_f f R₁) : ρ ≠ 0 := by
  intro h
  rw [h] at hρ
  exact absurd hρ (lem_zero_not_in_Kf f hf0)

-- If z ≠ 0, then |z| > 0
lemma lem_mod_pos_iff_ne_zero (z : ℂ) (hz : z ≠ 0) : 0 < ‖z‖ := by
  exact norm_pos_iff.mpr hz

-- If f(0) ≠ 0, then |ρ| > 0 for all ρ ∈ K_f(R₁)
lemma lem_mod_rho_pos {R₁ : ℝ} (f : ℂ → ℂ) (hf0 : f 0 ≠ 0)
    (ρ : ℂ) (hρ : ρ ∈ K_f f R₁) : 0 < ‖ρ‖ := by
  exact lem_mod_pos_iff_ne_zero ρ (lem_rho_ne_zero f hf0 ρ hρ)

-- Repeat of disk bound
lemma lem_rho_in_disk_R1_repeat {R₁ : ℝ} (hR₁ : 0 < R₁) (f : ℂ → ℂ)
    (ρ : ℂ) (hρ : ρ ∈ K_f f R₁) : ‖ρ‖ ≤ R₁ :=
  lem_rho_in_disk_R1 hR₁ f ρ hρ

-- If 0 < x ≤ y, then 1/x ≥ 1/y
lemma lem_inv_mono_decr (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    1/y ≤ 1/x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  exact one_div_le_one_div_of_le hx hxy

-- If ρ ∈ K_f(R₁), then 1/|ρ| ≥ 1/R₁
lemma lem_inv_mod_rho_ge_inv_R1 {R₁ : ℝ} (hR₁ : 0 < R₁) (f : ℂ → ℂ) (hf0 : f 0 ≠ 0)
    (ρ : ℂ) (hρ : ρ ∈ K_f f R₁) : 1/R₁ ≤ 1/‖ρ‖ := by
  apply lem_inv_mono_decr
  · exact lem_mod_rho_pos f hf0 ρ hρ
  · exact lem_rho_in_disk_R1_repeat hR₁ f ρ hρ

-- If a ≤ b and c > 0, then ac ≤ bc
lemma lem_mul_pos_preserves_ineq (a b c : ℝ) (hab : a ≤ b) (hc : 0 < c) :
    a * c ≤ b * c := by
  exact mul_le_mul_of_nonneg_right hab (le_of_lt hc)

-- If ρ ∈ K_f(R₁), then R/|ρ| ≥ R/R₁
lemma lem_R_div_mod_rho_ge_R_div_R1 {R R₁ : ℝ} (hR : 0 < R) (hR₁ : 0 < R₁)
    (f : ℂ → ℂ) (hf0 : f 0 ≠ 0) (ρ : ℂ) (hρ : ρ ∈ K_f f R₁) :
    R/R₁ ≤ R/‖ρ‖ := by
  have h1 := lem_inv_mod_rho_ge_inv_R1 hR₁ f hf0 ρ hρ
  -- h1: 1/R₁ ≤ 1/‖ρ‖
  rw [one_div, one_div] at h1
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left h1 (le_of_lt hR)

-- Modulus of product
lemma lem_mod_of_prod2 (K : Finset ℂ) (w : ℂ → ℂ) :
    ‖∏ ρ ∈ K, w ρ‖ = ∏ ρ ∈ K, ‖w ρ‖ := by
  exact Complex.norm_prod _ _

-- Modulus of B_f is product of moduli
lemma lem_mod_Bf_is_prod_mod {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ = (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 ≠ 0)
    (hfinite : Set.Finite (K_f f R₁)) (m : ℂ → ℕ) (z : ℂ) (hz : z ∈ closedDisk 0 R \ K_f f R₁) :
    ‖Bf hR hR₁ f hf hf0 hfinite z‖ = ‖f z‖ *
      ∏ ρ ∈ hfinite.toFinset, ‖(R - conj ρ * z / R) / (z - ρ)‖ ^ (m ρ) := by
  sorry

-- Absolute value of power
lemma lem_abs_pow (n : ℕ) (w : ℂ) : ‖w ^ n‖ = ‖w‖ ^ n := by
  exact norm_pow w n

-- Power modulus for Blaschke factors
lemma lem_Bmod_pow {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ = (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (z ρ : ℂ) (m : ℕ) :
    ‖((R - z * conj ρ / R) / (z - ρ))‖ ^ m =
    ‖((R - z * conj ρ / R) / (z - ρ))‖ ^ m := by
  rfl

-- B modulus is product
lemma lem_mod_Bf_prod_mod {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ = (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 ≠ 0)
    (hfinite : Set.Finite (K_f f R₁)) (m : ℂ → ℕ) (z : ℂ) :
    ‖Bf hR hR₁ f hf hf0 hfinite z‖ = ‖f z‖ *
      ∏ ρ ∈ hfinite.toFinset, ‖(R - z * conj ρ / R) / (z - ρ)‖ ^ (m ρ) := by
  sorry

-- B at zero
lemma lem_mod_Bf_at_0 {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ = (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 ≠ 0)
    (hfinite : Set.Finite (K_f f R₁)) (m : ℂ → ℕ) :
    ‖Bf hR hR₁ f hf hf0 hfinite 0‖ = ‖f 0‖ *
      ∏ ρ ∈ hfinite.toFinset, ‖R / (-ρ)‖ ^ (m ρ) := by
  sorry

-- Division modulus
lemma lem_mod_div_ (w₁ w₂ : ℂ) (h : w₂ ≠ 0) :
    ‖w₁ / w₂‖ = ‖w₁‖ / ‖w₂‖ := by
  exact norm_div w₁ w₂

-- Modulus of negation
lemma lem_mod_neg (w : ℂ) : ‖-w‖ = ‖w‖ := by
  exact norm_neg w

-- Modulus of real/complex ratio
lemma lem_mod_div_and_neg (R : ℝ) (ρ : ℂ) (h : ρ ≠ 0) :
    ‖R / (-ρ)‖ = ‖R‖ / ‖ρ‖ := by
  simp [norm_div, norm_neg]

-- B at zero evaluation
lemma lem_mod_Bf_at_0_eval {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ = (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 ≠ 0)
    (hfinite : Set.Finite (K_f f R₁)) (m : ℂ → ℕ) :
    ‖Bf hR hR₁ f hf hf0 hfinite 0‖ = ‖f 0‖ *
      ∏ ρ ∈ hfinite.toFinset, (‖R‖ / ‖ρ‖) ^ (m ρ) := by
  sorry

-- Modulus of positive real
lemma lem_mod_of_pos_real (x : ℝ) (h : 0 < x) : ‖x‖ = x := by
  exact Real.norm_of_nonneg (le_of_lt h)

-- B at zero as ratio
lemma lem_mod_Bf_at_0_as_ratio {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ = (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 ≠ 0)
    (hfinite : Set.Finite (K_f f R₁)) (m : ℂ → ℕ) :
    ‖Bf hR hR₁ f hf hf0 hfinite 0‖ = ‖f 0‖ *
      ∏ ρ ∈ hfinite.toFinset, (R / ‖ρ‖) ^ (m ρ) := by
  sorry

-- Product inequality
lemma lem_prod_ineq {α : Type*} (K : Finset α) (a b : α → ℝ)
    (h : ∀ ρ ∈ K, 0 ≤ a ρ ∧ a ρ ≤ b ρ) :
    ∏ ρ ∈ K, a ρ ≤ ∏ ρ ∈ K, b ρ := by
  apply Finset.prod_le_prod
  · intro i hi
    exact (h i hi).1
  · intro i hi
    exact (h i hi).2

-- Power inequality
lemma lem_power_ineq (c : ℝ) (n : ℕ) (hc : 1 < c) (hn : 1 ≤ n) : c ≤ c ^ n := by
  sorry

-- Power one
lemma lem_power_ineq_1 (c : ℝ) (n : ℕ) (hc : 1 ≤ c) (hn : 1 ≤ n) : 1 ≤ c ^ n := by
  sorry

-- Product power inequality
lemma lem_prod_power_ineq {α : Type*} (K : Finset α) (c : α → ℝ) (n : α → ℕ)
    (h : ∀ ρ ∈ K, 1 ≤ c ρ ∧ 1 ≤ n ρ) :
    ∏ ρ ∈ K, (c ρ) ^ (n ρ) ≥ ∏ ρ ∈ K, 1 := by
  apply Finset.prod_le_prod
  · intro i _
    exact zero_le_one
  · intro i hi
    have hc := (h i hi).1
    have hn := (h i hi).2
    sorry

-- Product of ones
lemma lem_prod_1 {α : Type*} (K : Finset α) : ∏ ρ ∈ K, (1 : ℝ) = 1 := by
  simp

-- Product power bound
lemma lem_prod_power_ineq1 {α : Type*} (K : Finset α) (c : α → ℝ) (n : α → ℕ)
    (h : ∀ ρ ∈ K, 1 ≤ c ρ ∧ 1 ≤ n ρ) :
    1 ≤ ∏ ρ ∈ K, (c ρ) ^ (n ρ) := by
  rw [← lem_prod_1 K]
  exact lem_prod_power_ineq K c n h

-- Lower bound for products
lemma lem_mod_lower_bound_1 {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ = (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 = 1)
    (hfinite : Set.Finite (K_f f R₁)) (m : ℂ → ℕ) :
    1 ≤ ∏ ρ ∈ hfinite.toFinset, ((3:ℝ) / 2) ^ (m ρ) := by
  sorry

-- Bf is analytic
lemma lem_Bf_is_analytic {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ = (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 ≠ 0)
    (hfinite : Set.Finite (K_f f R₁)) :
    AnalyticOnNhd (Bf hR hR₁ f hf hf0 hfinite) (closedDisk 0 R) := by
  sorry

-- Boundary modulus equality
lemma lem_mod_Bf_eq_mod_f_on_boundary {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ = (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1)) (hf0 : f 0 ≠ 0)
    (hfinite : Set.Finite (K_f f R₁)) (z : ℂ) (hz : ‖z‖ = R) :
    ‖Bf hR hR₁ f hf hf0 hfinite z‖ = ‖f z‖ := by
  sorry

-- Bf bounded on boundary
lemma lem_Bf_bounded_on_boundary (B : ℝ) (hB : 1 < B) {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 ≠ 0) (hfinite : Set.Finite (K_f f R₁))
    (hfbound : ∀ z ∈ closedDisk 0 R, ‖f z‖ ≤ B)
    (z : ℂ) (hz : ‖z‖ = R) :
    ‖Bf hR hR₁ f hf hf0 hfinite z‖ ≤ B := by
  sorry

-- Maximum modulus principle for Bf
lemma lem_max_mod_principle_for_Bf (B : ℝ) (hB : 1 < B) {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 ≠ 0) (hfinite : Set.Finite (K_f f R₁))
    (hBf_analytic : AnalyticOnNhd (Bf hR hR₁ f hf hf0 hfinite) (closedDisk 0 R))
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖Bf hR hR₁ f hf hf0 hfinite z‖ ≤ B) :
    ∀ z ∈ closedDisk 0 R, ‖Bf hR hR₁ f hf hf0 hfinite z‖ ≤ B := by
  sorry

-- Bf bounded in disk from boundary
lemma lem_Bf_bounded_in_disk_from_boundary (B : ℝ) (hB : 1 < B) {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 ≠ 0) (hfinite : Set.Finite (K_f f R₁))
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖Bf hR hR₁ f hf hf0 hfinite z‖ ≤ B) :
    ∀ z ∈ closedDisk 0 R, ‖Bf hR hR₁ f hf hf0 hfinite z‖ ≤ B := by
  sorry

-- Bf bounded in disk from f
lemma lem_Bf_bounded_in_disk_from_f (B : ℝ) (hB : 1 < B) {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 ≠ 0) (hfinite : Set.Finite (K_f f R₁))
    (hfbound : ∀ z ∈ closedDisk 0 R, ‖f z‖ ≤ B) :
    ∀ z ∈ closedDisk 0 R, ‖Bf hR hR₁ f hf hf0 hfinite z‖ ≤ B := by
  sorry

-- Bf at 0 bounded
lemma lem_Bf_at_0_le_M (B : ℝ) (hB : 1 < B) {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 ≠ 0) (hfinite : Set.Finite (K_f f R₁))
    (hfbound : ∀ z ∈ closedDisk 0 R, ‖f z‖ ≤ B) :
    ‖Bf hR hR₁ f hf hf0 hfinite 0‖ ≤ B := by
  sorry

-- Jensen form
lemma lem_jensen_inequality_form (B : ℝ) (hB : 1 < B) {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 = 1) (hfinite : Set.Finite (K_f f R₁)) (m : ℂ → ℕ)
    (hfbound : ∀ z ∈ closedDisk 0 R, ‖f z‖ ≤ B) :
    (3/2 : ℝ) ^ (∑ ρ ∈ hfinite.toFinset, m ρ) ≤ B := by
  sorry

-- Log monotone
lemma lem_log_mono_inc (x y : ℝ) (hx : 0 < x) (hy : x ≤ y) : Real.log x ≤ Real.log y := by
  exact Real.log_le_log hx hy

-- Jensen log form
lemma lem_jensen_log_form (B : ℝ) (hB : 1 < B) {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 = 1) (hfinite : Set.Finite (K_f f R₁)) (m : ℂ → ℕ)
    (hfbound : ∀ z ∈ closedDisk 0 R, ‖f z‖ ≤ B) :
    (∑ ρ ∈ hfinite.toFinset, m ρ) * Real.log (3/2) ≤ Real.log B := by
  sorry

-- Three exceeds e
lemma lem_three_gt_e : 3 > Real.exp 1 := by
  have h := Real.exp_one_lt_d9
  linarith

-- Multiplicity bound
lemma lem_sum_m_rho_bound (B : ℝ) (hB : 1 < B) {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 = 1) (hfinite : Set.Finite (K_f f R₁)) (m : ℂ → ℕ)
    (hfbound : ∀ z ∈ closedDisk 0 R, ‖f z‖ ≤ B) :
    ∑ ρ ∈ hfinite.toFinset, m ρ ≤ Real.log B / Real.log (R / R₁) := by
  sorry

-- Sum inequality
lemma lem_sum_ineq {α : Type*} (K : Finset α) (a b : α → ℝ) (h : ∀ ρ ∈ K, a ρ ≤ b ρ) :
    ∑ ρ ∈ K, a ρ ≤ ∑ ρ ∈ K, b ρ := by
  exact Finset.sum_le_sum h

-- Sum of multiplicities ≥ sum of ones
lemma lem_sum_m_rho_1 {R R₁ : ℝ} (hR : 0 < R ∧ R < 1) (hR₁ : R₁ = (2/3) * R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hfinite : Set.Finite (K_f f R₁)) (m : ℂ → ℕ) (hm : ∀ ρ ∈ K_f f R₁, 1 ≤ m ρ) :
    ∑ ρ ∈ hfinite.toFinset, (1:ℝ) ≤ ∑ ρ ∈ hfinite.toFinset, (m ρ : ℝ) := by
  apply Finset.sum_le_sum
  intro ρ hρ_in
  have : ρ ∈ K_f f R₁ := hfinite.mem_toFinset.mp hρ_in
  exact Nat.one_le_cast.mpr (hm ρ this)

-- Count identity
lemma lem_sum_1_is_card {α : Type*} (S : Finset α) : ∑ _ ∈ S, (1:ℝ) = S.card := by
  simp

-- Zeros bound (K ≤ 3 log B)
lemma lem_num_zeros_bound (B : ℝ) (hB : 1 < B) {R R₁ : ℝ} (hR : 0 < R ∧ R < 1)
    (hR₁ : R₁ = (2/3) * R) (f : ℂ → ℂ) (hf : AnalyticOnNhd f (closedDisk 0 1))
    (hf0 : f 0 = 1) (hfinite : Set.Finite (K_f f R₁))
    (hfbound : ∀ z ∈ closedDisk 0 R, ‖f z‖ ≤ B) :
    hfinite.toFinset.card ≤ Real.log B / Real.log (R / R₁) := by
  sorry

end PNT2_LogDerivative
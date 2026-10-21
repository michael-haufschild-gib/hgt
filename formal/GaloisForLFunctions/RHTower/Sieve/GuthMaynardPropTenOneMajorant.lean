import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSmoothedLagSumL2
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSmoothedLagSumMoments
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropTenOne
import GaloisForLFunctions.HTGeometry.LogNormalDifferentiatedEquation

set_option autoImplicit false

/-!
# The majorant `f = ψ · R̃²` of Guth–Maynard Proposition 10.1

Proposition 10.1 is assembled from Proposition 9.1 through a function `f` majorising `R̃²` on
`[-20, 20]` with controlled mass, square mass and Fourier decay. The majorant is the smoothed
density of Lemma 8.4,

`f(u) = ψ(u) ∫ B ψ₃(B(u − x)) ψ₂(x) |R(x)|² dx = ψ(u) R̃(u)²`,

with `B = NM`, inner bump `ψ₃ = innerBump (2η)`, outer bump `ψ₂ = outerBump` (the bumps of
Proposition 7.2) and the fixed cutoff `ψ = innerBump 21`, which equals `1` on `[-21, 21]` and has
values in `[0, 1]`. Hence:

* `R̃(u)² ≤ f(u)` for `|u| ≤ 20`, with equality there;
* `∫ f ≤ ∫ R̃² ≤ 8η · c · |W|` (the `L²` mass of `R̃` and Lemma 8.2 on the window `[1/8, 8]`);
* `∫ f² ≤ ∫ R̃⁴ ≤ 64η² · c · E(W)` (Lemma 8.3 for `R̃`);
* `ξ² |f̂(ξ)| ≤ A₀ η⁵ T² sup f` for `1 ≤ B ≤ η² T` and `W ⊂ [0, T]`.

The last bound is Lemma 8.4 at `j = 2`: the Fourier decay
`(2π|ξ|)² |f̂(ξ)| ≤ D₁ J₃ (1 + B)² ∫ ψ₂ |R|²` traded against the lower bound
`f(1) ≥ B |W|²/(16(1 + 2D) η² T)`, with `J₃ ≪ η` the `L¹` size of the derivatives of the inner
bump of width `2η` and `D₁`, `D` absolute. A cutoff supported in a window `[A⁻¹, A]` cannot be
used here, because `R̃` need not vanish at negative arguments.
-/

open MeasureTheory Set
open scoped FourierTransform

namespace RHTower.GuthMaynard

noncomputable section

/-! ### Uniform bounds for the bumps -/

/-- A family of bounds indexed by `ℕ` has a common bound on each initial segment. -/
theorem exists_uniform_bound_le {P : ℕ → ℝ → Prop}
    (hmono : ∀ i C C', C ≤ C' → P i C → P i C') (h : ∀ i, ∃ C, 0 ≤ C ∧ P i C) (j : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ j, P i C := by
  induction j with
  | zero =>
      obtain ⟨C, hC0, hC⟩ := h 0
      exact ⟨C, hC0, fun i hi => by rw [Nat.le_zero] at hi; subst hi; exact hC⟩
  | succ n ih =>
      obtain ⟨D, hD0, hD⟩ := ih
      obtain ⟨C, hC0, hC⟩ := h (n + 1)
      refine ⟨max D C, le_trans hD0 (le_max_left _ _), fun i hi => ?_⟩
      rcases eq_or_lt_of_le hi with rfl | hlt
      · exact hmono _ _ _ (le_max_right _ _) hC
      · exact hmono _ _ _ (le_max_left _ _) (hD i (Nat.lt_succ_iff.mp hlt))

/-- `|ψ̃₁^{(i)}| ≤ D` for all `i ≤ j`, uniformly in the width `A ≥ 1`. -/
theorem exists_abs_iteratedDeriv_innerBump_le_of_le (j : ℕ) :
    ∃ D, 0 ≤ D ∧ ∀ i ≤ j, ∀ A, 1 ≤ A → ∀ x, |iteratedDeriv i (innerBump A) x| ≤ D :=
  exists_uniform_bound_le (fun _ _ _ hCC' hP A hA x => (hP A hA x).trans hCC')
    (fun i => by
      obtain ⟨C, hC⟩ := exists_abs_iteratedDeriv_innerBump_le i
      exact ⟨max 0 C, le_max_left _ _, fun A hA x => (hC A hA x).trans (le_max_right _ _)⟩) j

/-- `∫ |ψ̃₁^{(i)}| ≤ C A` for all `i ≤ j` and every width `A ≥ 1`: the `i`-th derivative of
`x ↦ φ(x/A)` scales by `A^{-i}` and the integral by `A`. -/
theorem exists_integral_abs_iteratedDeriv_innerBump_le (j : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ j, ∀ A, 1 ≤ A → ∫ y, |iteratedDeriv i (innerBump A) y| ≤ C * A := by
  refine exists_uniform_bound_le
    (fun _ _ _ hCC' hP A hA => (hP A hA).trans (mul_le_mul_of_nonneg_right hCC' (by linarith)))
    (fun i => ⟨∫ y, |iteratedDeriv i plateauBump y|,
      integral_nonneg fun _ => abs_nonneg _, fun A hA => ?_⟩) j
  have hA0 : 0 < A := by linarith
  have hfun : innerBump A = fun x => plateauBump (A⁻¹ * x) := by
    funext y; simp [innerBump, div_eq_inv_mul]
  rw [hfun, iteratedDeriv_comp_const_mul (contDiff_plateauBump.of_le (by exact_mod_cast le_top))]
  have habs : ∀ y, |A⁻¹ ^ i * iteratedDeriv i plateauBump (A⁻¹ * y)|
      = A⁻¹ ^ i * |iteratedDeriv i plateauBump (A⁻¹ * y)| := fun y => by
    rw [abs_mul, abs_pow, abs_inv, abs_of_pos hA0]
  simp_rw [habs]
  rw [integral_const_mul,
    Measure.integral_comp_mul_left (fun y => |iteratedDeriv i plateauBump y|) A⁻¹,
    inv_inv, abs_of_pos hA0, smul_eq_mul]
  have h1 : A⁻¹ ^ i ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hA)
  have h2 : 0 ≤ A * ∫ y, |iteratedDeriv i plateauBump y| :=
    mul_nonneg hA0.le (integral_nonneg fun _ => abs_nonneg _)
  nlinarith

/-- The outer bump has mass at most `8`: it is at most `1` and vanishes off `[1/8, 8]`. -/
theorem integral_outerBump_le : ∫ x, outerBump x ≤ 8 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => outerBump_eq_zero_of_not_mem_Icc hx)]
  calc ∫ x in Icc (8 : ℝ)⁻¹ 8, outerBump x
      ≤ ∫ _x in Icc (8 : ℝ)⁻¹ 8, (1 : ℝ) :=
        setIntegral_mono_on contDiff_outerBump.continuous.integrableOn_Icc
          continuous_const.integrableOn_Icc measurableSet_Icc fun x _ => outerBump_le_one x
    _ ≤ 8 := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul]
        norm_num

/-- A smooth function with a bounded derivative is Lipschitz with that constant. -/
theorem abs_sub_le_of_abs_deriv_le {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {D : ℝ}
    (hd : ∀ u, |deriv ψ u| ≤ D) (a b : ℝ) : |ψ a - ψ b| ≤ D * |a - b| :=
  GaloisForLFunctions.HTGeometry.abs_sub_le_of_deriv_bound
    (fun x => (hψ.differentiable (by simp) x).hasDerivAt) hd a b

/-! ### General properties of the smoothed density -/

/-- The smoothed density is continuous: the kernel is continuous in the parameter and dominated
by the integrable profile `|B| · sup ψ₃ · |ψ₂| · |W|²`. -/
theorem continuous_smoothedDensity {ψ₁ ψ₂ ψ₃ : ℝ → ℝ} (hc₁ : Continuous ψ₁) (hc₂ : Continuous ψ₂)
    (hs₂ : HasCompactSupport ψ₂) (hc₃ : Continuous ψ₃) (hs₃ : HasCompactSupport ψ₃) (B : ℝ)
    (W : Finset ℝ) : Continuous (smoothedDensity ψ₁ ψ₂ ψ₃ B W) := by
  obtain ⟨C₃, hC₃⟩ := hc₃.bounded_above_of_compact_support hs₃
  have hC₃0 : 0 ≤ C₃ := le_trans (norm_nonneg _) (hC₃ 0)
  have hψ₂ : Integrable ψ₂ := hc₂.integrable_of_hasCompactSupport hs₂
  refine hc₁.mul (continuous_of_dominated
    (bound := fun x => |B| * C₃ * |ψ₂ x| * (W.card : ℝ) ^ 2) (fun u => ?_) (fun u => ?_) ?_ ?_)
  · have := hc₂.measurable
    have := hc₃.measurable
    have := measurable_lagSum W
    exact (by fun_prop : Measurable fun x =>
      B * ψ₃ (B * (u - x)) * ψ₂ x * ‖lagSum W x‖ ^ 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖lagSum W x‖ ^ 2)]
    have h1 : |ψ₃ (B * (u - x))| ≤ C₃ := by
      simpa [Real.norm_eq_abs] using hC₃ (B * (u - x))
    have h2 : ‖lagSum W x‖ ^ 2 ≤ (W.card : ℝ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_lagSum_le W x) 2
    refine mul_le_mul ?_ h2 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h1 (abs_nonneg B)) (abs_nonneg _)
  · exact (hψ₂.abs.const_mul (|B| * C₃)).mul_const _
  · refine Filter.Eventually.of_forall fun x => ?_
    exact ((continuous_const.mul (hc₃.comp (continuous_const.mul
      (continuous_id.sub continuous_const)))).mul_const _).mul_const _

/-- The smoothed density inherits the compact support of its outer cutoff. -/
theorem hasCompactSupport_smoothedDensity {ψ₁ ψ₂ ψ₃ : ℝ → ℝ} (hs₁ : HasCompactSupport ψ₁)
    (B : ℝ) (W : Finset ℝ) : HasCompactSupport (smoothedDensity ψ₁ ψ₂ ψ₃ B W) := by
  have h : smoothedDensity ψ₁ ψ₂ ψ₃ B W
      = ψ₁ * fun u => ∫ x, B * ψ₃ (B * (u - x)) * ψ₂ x * ‖lagSum W x‖ ^ 2 := rfl
  rw [h]
  exact hs₁.mul_right

/-! ### The majorant of Proposition 10.1 -/

/-- The majorant `f = ψ · R̃²` of Proposition 10.1: the smoothing of `|R|²` at scale `1/B` with
the bumps of Proposition 7.2 (inner width `2η`, outer `outerBump`), cut off by the fixed plateau
`innerBump 21`, which equals `1` on `[-21, 21]`. -/
def propTenOneMajorant (η B : ℝ) (W : Finset ℝ) : ℝ → ℝ :=
  smoothedDensity (innerBump 21) outerBump (innerBump (2 * η)) B W

/-- The window constant of Lemma 8.2 on the window `[1/8, 8]`. -/
def windowConstant : ℝ := 5 * Real.pi / 2 * 8 * max 1 (Real.log 8)

theorem windowConstant_nonneg : 0 ≤ windowConstant :=
  mul_nonneg (by positivity) (le_trans zero_le_one (le_max_left _ _))

theorem propTenOneMajorant_nonneg {η B : ℝ} (hB : 0 ≤ B) (W : Finset ℝ) (u : ℝ) :
    0 ≤ propTenOneMajorant η B W u :=
  smoothedDensity_nonneg (innerBump_nonneg 21) outerBump_nonneg (innerBump_nonneg (2 * η)) hB W u

theorem continuous_propTenOneMajorant {η : ℝ} (hη : 0 < η) (B : ℝ) (W : Finset ℝ) :
    Continuous (propTenOneMajorant η B W) :=
  continuous_smoothedDensity (contDiff_innerBump 21).continuous contDiff_outerBump.continuous
    hasCompactSupport_outerBump (contDiff_innerBump (2 * η)).continuous
    (hasCompactSupport_innerBump (by linarith)) B W

theorem hasCompactSupport_propTenOneMajorant (η B : ℝ) (W : Finset ℝ) :
    HasCompactSupport (propTenOneMajorant η B W) :=
  hasCompactSupport_smoothedDensity (hasCompactSupport_innerBump (by norm_num)) B W

/-- `f = ψ · R̃²` with `R̃` the smoothed lag sum of Proposition 7.2. -/
theorem propTenOneMajorant_eq {η N M : ℝ} (hη : 0 < η) (hNM : 0 ≤ N * M) (W : Finset ℝ) (u : ℝ) :
    propTenOneMajorant η (N * M) W u
      = innerBump 21 u * smoothedLagSum (innerBump (2 * η)) outerBump N M W u ^ 2 := by
  rw [smoothedLagSum_sq (isSmoothingPair_innerBump_outerBump (by linarith)) hNM W u]
  rfl

/-- **The majorisation.** `R̃(u)² ≤ f(u)` for `|u| ≤ 20`, since the cutoff is `1` there. -/
theorem smoothedLagSum_sq_le_propTenOneMajorant {η N M : ℝ} (hη : 0 < η) (hNM : 0 ≤ N * M)
    (W : Finset ℝ) {u : ℝ} (hu : |u| ≤ 20) :
    smoothedLagSum (innerBump (2 * η)) outerBump N M W u ^ 2
      ≤ propTenOneMajorant η (N * M) W u := by
  rw [propTenOneMajorant_eq hη hNM W u, innerBump_eq_one (by norm_num) (by linarith), one_mul]

/-- The inner bump of width `2η` has mass at most `8η`. -/
theorem integral_innerBump_two_mul_le {η : ℝ} (hη : 0 < η) : ∫ x, innerBump (2 * η) x ≤ 8 * η := by
  have := integral_innerBump_le (A := 2 * η) (by linarith)
  linarith

/-- **The mass of the majorant.** `∫ f ≤ ∫ R̃² ≤ 8η · c · |W|` for `1`-separated `W`. -/
theorem integral_propTenOneMajorant_le {η N M : ℝ} (hη : 0 < η) (hNM : 0 < N * M)
    {W : Finset ℝ} (hW : IsSeparated 1 W) :
    ∫ u, propTenOneMajorant η (N * M) W u ≤ 8 * η * windowConstant * W.card := by
  have hpair := isSmoothingPair_innerBump_outerBump (A := 2 * η) (by linarith)
  have hint := (integrable_and_integral_smoothedLagSum_sq hpair hNM W).1
  have hstep : ∫ u, propTenOneMajorant η (N * M) W u
      ≤ ∫ u, smoothedLagSum (innerBump (2 * η)) outerBump N M W u ^ 2 := by
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun u => propTenOneMajorant_nonneg hNM.le W u) hint
      (Filter.Eventually.of_forall fun u => ?_)
    rw [propTenOneMajorant_eq hη hNM.le W u]
    nlinarith [innerBump_le_one 21 u, innerBump_nonneg 21 u,
      sq_nonneg (smoothedLagSum (innerBump (2 * η)) outerBump N M W u)]
  refine hstep.trans ((integral_smoothedLagSum_sq_le (A := 8) (by norm_num) hpair hNM
    (fun x hx => outerBump_eq_zero_of_not_mem_Icc hx) hW).trans ?_)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (integral_innerBump_two_mul_le hη) windowConstant_nonneg)
    (Nat.cast_nonneg _)

/-- **The square mass of the majorant.** `∫ f² ≤ ∫ R̃⁴ ≤ 64η² · c · E(W)`. -/
theorem integral_sq_propTenOneMajorant_le {η N M : ℝ} (hη : 0 < η) (hNM : 0 < N * M)
    (W : Finset ℝ) :
    ∫ u, propTenOneMajorant η (N * M) W u ^ 2
      ≤ 64 * η ^ 2 * windowConstant * additiveEnergy W := by
  have hpair := isSmoothingPair_innerBump_outerBump (A := 2 * η) (by linarith)
  have hsupp : ∀ x, x ∉ Icc (8 : ℝ)⁻¹ 8 → outerBump x = 0 :=
    fun x hx => outerBump_eq_zero_of_not_mem_Icc hx
  have hint := (integrable_and_integral_smoothedLagSum_pow_four_le hpair hNM hsupp W).1
  have hstep : ∫ u, propTenOneMajorant η (N * M) W u ^ 2
      ≤ ∫ u, smoothedLagSum (innerBump (2 * η)) outerBump N M W u ^ 4 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _) hint
      (Filter.Eventually.of_forall fun u => ?_)
    have h2 : (smoothedLagSum (innerBump (2 * η)) outerBump N M W u ^ 2) ^ 2
        = smoothedLagSum (innerBump (2 * η)) outerBump N M W u ^ 4 := by ring
    show propTenOneMajorant η (N * M) W u ^ 2
      ≤ smoothedLagSum (innerBump (2 * η)) outerBump N M W u ^ 4
    rw [propTenOneMajorant_eq hη hNM.le W u, mul_pow, h2]
    nlinarith [pow_le_one₀ (innerBump_nonneg 21 u) (innerBump_le_one 21 u) (n := 2),
      pow_nonneg (smoothedLagSum_nonneg (innerBump (2 * η)) outerBump N M W u) 4,
      sq_nonneg (innerBump 21 u)]
  refine hstep.trans ((integral_smoothedLagSum_pow_four_le_energy (A := 8) (by norm_num) hpair
    hNM hsupp W).trans ?_)
  have hsq : (∫ x, innerBump (2 * η) x) ^ 2 ≤ 64 * η ^ 2 := by
    have h1 := integral_innerBump_two_mul_le hη
    have h0 : 0 ≤ ∫ x, innerBump (2 * η) x := integral_nonneg fun _ => innerBump_nonneg _ _
    nlinarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq windowConstant_nonneg)
    (Nat.cast_nonneg _)

/-! ### Fourier decay of the majorant -/

/-- **Lemma 8.4 for the Proposition 10.1 majorant.** There is an absolute `A₀` such that for
`T ≥ 1`, width `η ≥ 1`, smoothing scale `1 ≤ B ≤ η² T` and `W ⊂ [0, T]`,
`ξ² |f̂(ξ)| ≤ A₀ η⁵ T² sup f` for every frequency `ξ`.

The decay `(2π|ξ|)² |f̂(ξ)| ≤ D₁ J₃ (1 + B)² ∫ψ₂|R|²` is traded against the lower bound
`f(1) ≥ B |W|²/(16(1 + 2D) η² T)` using `∫ψ₂|R|² ≤ 8 |W|²` and `(1 + B)² ≤ 4B η² T`. -/
theorem exists_fourier_decay_propTenOneMajorant :
    ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ (T η B : ℝ) (W : Finset ℝ), 1 ≤ T → 1 ≤ η → 1 ≤ B → B ≤ η ^ 2 * T →
      (∀ t ∈ W, t ∈ Icc 0 T) → ∀ ξ : ℝ,
        ξ ^ 2 * ‖𝓕 (complexify (propTenOneMajorant η B W)) ξ‖
          ≤ A₀ * η ^ 5 * T ^ 2 * ⨆ x, propTenOneMajorant η B W x := by
  obtain ⟨D₁, hD₁0, hD₁⟩ := exists_abs_iteratedDeriv_innerBump_le_of_le 2
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_integral_abs_iteratedDeriv_innerBump_le 2
  obtain ⟨Dout, hDout⟩ := exists_abs_iteratedDeriv_outerBump_le 1
  obtain ⟨Din, hDin0, hDin⟩ := exists_abs_iteratedDeriv_innerBump_le_of_le 1
  obtain ⟨D, hD⟩ : ∃ D, D = max 0 (max Dout Din) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hD ▸ le_max_left _ _
  refine ⟨1024 * D₁ * C₃ * (1 + 2 * D), by positivity,
    fun T η B W hT hη hB hBT hW ξ => ?_⟩
  have hη0 : 0 < η := by linarith
  have hB0 : 0 < B := by linarith
  have hT0 : 0 < T := by linarith
  have h2η : (1 : ℝ) ≤ 2 * η := by linarith
  have hK : (1 : ℝ) ≤ η ^ 2 := by nlinarith
  have hc₂ : Continuous outerBump := contDiff_outerBump.continuous
  have hs₂ : HasCompactSupport outerBump := hasCompactSupport_outerBump
  have hs₃ : HasCompactSupport (innerBump (2 * η)) := hasCompactSupport_innerBump (by linarith)
  -- the supremum of `f`
  obtain ⟨S, hS⟩ : ∃ S, S = ⨆ x, propTenOneMajorant η B W x := ⟨_, rfl⟩
  have hf1S : propTenOneMajorant η B W 1 ≤ S :=
    hS ▸ le_ciSup ((continuous_propTenOneMajorant hη0 B W).bddAbove_range_of_hasCompactSupport
      (hasCompactSupport_propTenOneMajorant η B W)) 1
  have hS0 : 0 ≤ S := le_trans (propTenOneMajorant_nonneg hB0.le W 1) hf1S
  -- Lemma 8.4 decay at `j = 2`
  have hdec : (2 * Real.pi * |ξ|) ^ 2 * ‖𝓕 (complexify (propTenOneMajorant η B W)) ξ‖
      ≤ D₁ * (C₃ * (2 * η)) * (1 + B) ^ 2 * ∫ x, |outerBump x| * ‖lagSum W x‖ ^ 2 :=
    pow_mul_norm_fourier_smoothedDensity_le (j := 2) (D₁ := D₁) (J₃ := C₃ * (2 * η))
      (contDiff_innerBump 21) (hasCompactSupport_innerBump (by norm_num)) hc₂ hs₂
      (contDiff_innerBump (2 * η)) hs₃ hB0 (fun i hi u => hD₁ i hi 21 (by norm_num) u)
      (fun i hi => hC₃ i hi (2 * η) h2η) W ξ
  -- `∫ ψ₂ |R|² ≤ 8 |W|²`
  have hg : ∫ x, |outerBump x| * ‖lagSum W x‖ ^ 2 ≤ (W.card : ℝ) ^ 2 * 8 := by
    have hL : Integrable fun x => |outerBump x| * ‖lagSum W x‖ ^ 2 :=
      (integrable_mul_norm_lagSum_sq hc₂ hs₂ W).abs.congr
        (Filter.Eventually.of_forall fun x => by
          show |outerBump x * ‖lagSum W x‖ ^ 2| = |outerBump x| * ‖lagSum W x‖ ^ 2
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖lagSum W x‖ ^ 2)])
    have hstep : ∫ x, |outerBump x| * ‖lagSum W x‖ ^ 2
        ≤ ∫ x, (W.card : ℝ) ^ 2 * outerBump x := by
      refine integral_mono hL ((hc₂.integrable_of_hasCompactSupport hs₂).const_mul _) fun x => ?_
      rw [abs_of_nonneg (outerBump_nonneg x)]
      nlinarith [outerBump_nonneg x,
        pow_le_pow_left₀ (norm_nonneg (lagSum W x)) (norm_lagSum_le W x) 2]
    rw [integral_const_mul] at hstep
    refine hstep.trans ?_
    nlinarith [integral_outerBump_le, sq_nonneg (W.card : ℝ)]
  -- the size of `f` at `1`
  have hL₂ : ∀ a b, |outerBump a - outerBump b| ≤ D * |a - b| :=
    abs_sub_le_of_abs_deriv_le contDiff_outerBump fun u => by
      have h := hDout u
      rw [iteratedDeriv_one] at h
      rw [hD]
      exact h.trans (le_trans (le_max_left _ _) (le_max_right _ _))
  have hL₃ : ∀ a b, |innerBump (2 * η) a - innerBump (2 * η) b| ≤ D * |a - b| :=
    abs_sub_le_of_abs_deriv_le (contDiff_innerBump (2 * η)) fun u => by
      have h := hDin 1 le_rfl (2 * η) h2η u
      rw [iteratedDeriv_one] at h
      rw [hD]
      exact h.trans (le_trans (le_max_right _ _) (le_max_right _ _))
  have hlow : B * (W.card : ℝ) ^ 2 / (16 * ((1 + 2 * D) * η ^ 2 * T))
      ≤ propTenOneMajorant η B W 1 :=
    smoothedDensity_one_ge (ψ₁ := innerBump 21) (x₀ := 0) hc₂ hs₂
      (contDiff_innerBump (2 * η)).continuous hs₃ outerBump_nonneg (innerBump_nonneg (2 * η))
      (innerBump_eq_one (by norm_num) (by norm_num)) outerBump_one (innerBump_zero (2 * η))
      hD0 hL₂ hL₃ hB0 hK hT hBT (fun t ht => ⟨(hW t ht).1, by rw [zero_add]; exact (hW t ht).2⟩)
  have hW2 : B * (W.card : ℝ) ^ 2 ≤ 16 * ((1 + 2 * D) * η ^ 2 * T) * S := by
    have hden : (0 : ℝ) < 16 * ((1 + 2 * D) * η ^ 2 * T) := by positivity
    have h := hlow.trans hf1S
    rw [div_le_iff₀ hden] at h
    linarith
  -- assembly
  obtain ⟨X, hX⟩ : ∃ X, X = ‖𝓕 (complexify (propTenOneMajorant η B W)) ξ‖ := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = ∫ x, |outerBump x| * ‖lagSum W x‖ ^ 2 := ⟨_, rfl⟩
  rw [← hX, ← hG] at hdec
  rw [← hG] at hg
  have hX0 : 0 ≤ X := hX ▸ norm_nonneg _
  have hG0 : 0 ≤ G := hG ▸ integral_nonneg fun x => by positivity
  have hpi : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hsq : (2 * Real.pi * |ξ|) ^ 2 = 4 * Real.pi ^ 2 * ξ ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]; ring
  have hstep1 : ξ ^ 2 * X ≤ (2 * Real.pi * |ξ|) ^ 2 * X := by
    rw [hsq]
    exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ξ]) hX0
  have hstep2 : (1 + B) ^ 2 ≤ 4 * B * (η ^ 2 * T) := by
    have h1 : 4 * B * B ≤ 4 * B * (η ^ 2 * T) := mul_le_mul_of_nonneg_left hBT (by positivity)
    nlinarith [sq_nonneg (B - 1)]
  rw [← hX, ← hS]
  calc ξ ^ 2 * X ≤ (2 * Real.pi * |ξ|) ^ 2 * X := hstep1
    _ ≤ D₁ * (C₃ * (2 * η)) * (1 + B) ^ 2 * G := hdec
    _ ≤ D₁ * (C₃ * (2 * η)) * (4 * B * (η ^ 2 * T)) * ((W.card : ℝ) ^ 2 * 8) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hstep2 (by positivity)) hg hG0 (by positivity)
    _ = 64 * D₁ * C₃ * η * (η ^ 2 * T) * (B * (W.card : ℝ) ^ 2) := by ring
    _ ≤ 64 * D₁ * C₃ * η * (η ^ 2 * T) * (16 * ((1 + 2 * D) * η ^ 2 * T) * S) :=
        mul_le_mul_of_nonneg_left hW2 (by positivity)
    _ = 1024 * D₁ * C₃ * (1 + 2 * D) * η ^ 5 * T ^ 2 * S := by ring

end

end RHTower.GuthMaynard

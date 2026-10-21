import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSmoothedLagSum
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSumL2

set_option autoImplicit false

/-!
# The `L²` mass of the smoothed lag sum `R̃`

For a smoothing pair `ψ₁, ψ₂` and scales with `NM > 0`, the smoothed lag sum of Guth–Maynard
(7.5), `R̃(u)² = ∫ NM ψ₁(NM(u − x)) ψ₂(x) |R(x)|² dx`, has total mass

`∫_ℝ R̃(u)² du = (∫ ψ₁) · ∫ ψ₂(x) |R(x)|² dx`.

The integrand is nonnegative and integrable on the plane, so the order of integration may be
swapped; the inner integral in `u` is the mass `∫ψ₁` of the kernel `u ↦ NM ψ₁(NM(u − x))`, which
is independent of the centre `x` by translation and scaling invariance of Lebesgue measure.

If moreover `ψ₂` vanishes off `[A⁻¹, A]` and `W` is `1`-separated, Lemma 8.2
(`setIntegral_Icc_inv_normSq_lagSum_le`) turns this into

`∫_ℝ R̃(u)² du ≤ (∫ ψ₁) · (5π/2) A max(1, log A) · |W|`,

the `L²` input of Proposition 10.1 (the `L⁴` input is Lemma 8.3 for `R̃`).
-/

open MeasureTheory Set

namespace RHTower.GuthMaynard

noncomputable section

variable {ψ₁ ψ₂ : ℝ → ℝ} {N M A : ℝ}

/-- The smoothing kernel `u ↦ NM ψ₁(NM(u − x))` has mass `∫ψ₁`, for every centre `x`. -/
theorem integral_smoothingKernel (hNM : 0 < N * M) (ψ₁ : ℝ → ℝ) (x : ℝ) :
    ∫ u, N * M * ψ₁ (N * M * (u - x)) = ∫ y, ψ₁ y := by
  rw [integral_const_mul, integral_sub_right_eq_self (fun y => ψ₁ (N * M * y)) x,
    Measure.integral_comp_mul_left (fun y => ψ₁ y) (N * M), abs_inv, abs_of_pos hNM, smul_eq_mul,
    mul_inv_cancel_left₀ hNM.ne']

/-- Integrating the `R̃²`-integrand in the smoothing variable returns the mass of `ψ₁`. -/
theorem integral_smoothedLagSumIntegrand_right (hNM : 0 < N * M) (W : Finset ℝ) (x : ℝ) :
    ∫ u, smoothedLagSumIntegrand ψ₁ ψ₂ N M W u x
      = (∫ y, ψ₁ y) * (ψ₂ x * ‖lagSum W x‖ ^ 2) := by
  have e : ∀ u, smoothedLagSumIntegrand ψ₁ ψ₂ N M W u x
      = N * M * ψ₁ (N * M * (u - x)) * (ψ₂ x * ‖lagSum W x‖ ^ 2) := fun u => by
    unfold smoothedLagSumIntegrand; ring
  simp_rw [e]
  rw [integral_mul_const, integral_smoothingKernel hNM]

/-- The plane integrand `(x, u) ↦ NM ψ₁(NM(u − x)) ψ₂(x) |R(x)|²` is integrable on `ℝ²`:
its `u`-integral is `(∫ψ₁) ψ₂(x) |R(x)|²`, which is integrable in `x`. -/
theorem integrable_uncurry_smoothedLagSumIntegrand (h : IsSmoothingPair ψ₁ ψ₂) (hNM : 0 < N * M)
    (W : Finset ℝ) :
    Integrable (Function.uncurry fun x u => smoothedLagSumIntegrand ψ₁ ψ₂ N M W u x)
      (volume.prod volume) := by
  have hψ₁ : Integrable ψ₁ := h.continuous₁.integrable_of_hasCompactSupport h.compactSupport₁
  have hψ₂ : Integrable ψ₂ := h.continuous₂.integrable_of_hasCompactSupport h.compactSupport₂
  have hmeas : Measurable
      (Function.uncurry fun x u => smoothedLagSumIntegrand ψ₁ ψ₂ N M W u x) := by
    have h1 := h.continuous₁.measurable
    have h2 := h.continuous₂.measurable
    have h3 := measurable_lagSum W
    unfold Function.uncurry smoothedLagSumIntegrand
    fun_prop
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
  · have h1 : Integrable fun u =>
        N * M * ψ₁ (N * M * (u - x)) * (ψ₂ x * ‖lagSum W x‖ ^ 2) :=
      (((hψ₁.comp_mul_left' hNM.ne').comp_sub_right x).const_mul (N * M)).mul_const _
    refine h1.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [Function.uncurry, smoothedLagSumIntegrand]
    ring
  · have hg : Integrable fun x => ψ₂ x * ‖lagSum W x‖ ^ 2 := by
      refine (hψ₂.bdd_mul (c := (W.card : ℝ) ^ 2)
        ((measurable_lagSum W).norm.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖lagSum W x‖ ^ 2)]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_lagSum_le W x) 2)).congr
        (Filter.Eventually.of_forall fun x => ?_)
      ring
    refine (hg.const_mul (∫ y, ψ₁ y)).congr (Filter.Eventually.of_forall fun x => ?_)
    have hnorm : ∀ u,
        ‖(Function.uncurry fun x u => smoothedLagSumIntegrand ψ₁ ψ₂ N M W u x) (x, u)‖
          = smoothedLagSumIntegrand ψ₁ ψ₂ N M W u x := fun u => by
      simp only [Function.uncurry]
      rw [Real.norm_eq_abs, abs_of_nonneg (smoothedLagSumIntegrand_nonneg h hNM.le W u x)]
    simp_rw [hnorm]
    exact (integral_smoothedLagSumIntegrand_right hNM W x).symm

/-- **The `L²` mass of `R̃`.** For a smoothing pair and `NM > 0` the function `R̃²` is integrable
and `∫_ℝ R̃(u)² du = (∫ψ₁) ∫ ψ₂(x) |R(x)|² dx`. -/
theorem integrable_and_integral_smoothedLagSum_sq (h : IsSmoothingPair ψ₁ ψ₂) (hNM : 0 < N * M)
    (W : Finset ℝ) :
    Integrable (fun u => smoothedLagSum ψ₁ ψ₂ N M W u ^ 2) ∧
      ∫ u, smoothedLagSum ψ₁ ψ₂ N M W u ^ 2
        = (∫ x, ψ₁ x) * ∫ x, ψ₂ x * ‖lagSum W x‖ ^ 2 := by
  have hprod := integrable_uncurry_smoothedLagSumIntegrand h hNM W
  have hsq : ∀ u, ∫ x, smoothedLagSumIntegrand ψ₁ ψ₂ N M W u x
      = smoothedLagSum ψ₁ ψ₂ N M W u ^ 2 := fun u => (smoothedLagSum_sq h hNM.le W u).symm
  constructor
  · have hswap : Integrable
        (Function.uncurry fun u x => smoothedLagSumIntegrand ψ₁ ψ₂ N M W u x)
        (volume.prod volume) := hprod.swap
    obtain ⟨-, hint⟩ := (integrable_prod_iff hswap.aestronglyMeasurable).mp hswap
    refine hint.congr (Filter.Eventually.of_forall fun u => ?_)
    have hnorm : ∀ x,
        ‖(Function.uncurry fun u x => smoothedLagSumIntegrand ψ₁ ψ₂ N M W u x) (u, x)‖
          = smoothedLagSumIntegrand ψ₁ ψ₂ N M W u x := fun x => by
      simp only [Function.uncurry]
      rw [Real.norm_eq_abs, abs_of_nonneg (smoothedLagSumIntegrand_nonneg h hNM.le W u x)]
    simp_rw [hnorm]
    exact hsq u
  · have hrw : ∫ u, smoothedLagSum ψ₁ ψ₂ N M W u ^ 2
        = ∫ u, ∫ x, smoothedLagSumIntegrand ψ₁ ψ₂ N M W u x := by simp_rw [hsq]
    rw [hrw, ← integral_integral_swap hprod]
    simp_rw [integral_smoothedLagSumIntegrand_right hNM W]
    rw [integral_const_mul]

/-- **`∫ R̃² ≪ (∫ψ₁) |W|`.** For a smoothing pair with `ψ₂` supported in `[A⁻¹, A]`, `A ≥ 1`,
`NM > 0` and a `1`-separated `W`:
`∫_ℝ R̃(u)² du ≤ (∫ψ₁) · (5π/2) A max(1, log A) · |W|`. -/
theorem integral_smoothedLagSum_sq_le (hA : 1 ≤ A) (h : IsSmoothingPair ψ₁ ψ₂) (hNM : 0 < N * M)
    (hsupp : ∀ x, x ∉ Icc A⁻¹ A → ψ₂ x = 0) {W : Finset ℝ} (hW : IsSeparated 1 W) :
    ∫ u, smoothedLagSum ψ₁ ψ₂ N M W u ^ 2
      ≤ (∫ x, ψ₁ x) * (5 * Real.pi / 2 * A * max 1 (Real.log A)) * W.card := by
  have hψ₁ : 0 ≤ ∫ x, ψ₁ x := integral_nonneg h.nonneg₁
  have hbound : ∫ x, ψ₂ x * ‖lagSum W x‖ ^ 2
      ≤ 5 * Real.pi / 2 * A * max 1 (Real.log A) * W.card := by
    have hloc : ∫ x, ψ₂ x * ‖lagSum W x‖ ^ 2
        = ∫ x in Icc A⁻¹ A, ψ₂ x * ‖lagSum W x‖ ^ 2 :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hsupp x hx, zero_mul]).symm
    have hint₁ : IntegrableOn (fun x => ψ₂ x * ‖lagSum W x‖ ^ 2) (Icc A⁻¹ A) :=
      Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
        (by
          have := h.continuous₂.measurable
          have := measurable_lagSum W
          exact (by fun_prop : Measurable fun x =>
            ψ₂ x * ‖lagSum W x‖ ^ 2).aestronglyMeasurable)
        (M := (W.card : ℝ) ^ 2) (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by
            have := h.nonneg₂ x
            positivity)]
          have h1 := h.le_one₂ x
          have h2 : ‖lagSum W x‖ ^ 2 ≤ (W.card : ℝ) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_lagSum_le W x) 2
          nlinarith [h.nonneg₂ x, sq_nonneg ‖lagSum W x‖])
    have hint₂ : IntegrableOn (fun x => ‖lagSum W x‖ ^ 2) (Icc A⁻¹ A) :=
      Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
        (measurable_norm_lagSum_sq W).aestronglyMeasurable
        (M := (W.card : ℝ) ^ 2) (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_lagSum_le W x) 2)
    rw [hloc]
    refine le_trans (setIntegral_mono_on hint₁ hint₂ measurableSet_Icc fun x _ => ?_)
      (setIntegral_Icc_inv_normSq_lagSum_le hA hW)
    have h1 := h.le_one₂ x
    nlinarith [h.nonneg₂ x, sq_nonneg ‖lagSum W x‖]
  rw [(integrable_and_integral_smoothedLagSum_sq h hNM W).2, mul_assoc]
  exact mul_le_mul_of_nonneg_left hbound hψ₁

end

end RHTower.GuthMaynard

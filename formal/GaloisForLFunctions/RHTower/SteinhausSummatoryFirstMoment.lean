import GaloisForLFunctions.RHTower.SteinhausFrozenVarianceCauchyLimit
import GaloisForLFunctions.RHTower.SteinhausPrefixResampling

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace RHTower
open SteinhausModel

/-- The literal summatory magnitude at its square-root arithmetic scale. -/
def steinhausNormalizedSummatoryNorm (N : ℕ) (ω : Omega) : ℝ≥0∞ :=
  ENNReal.ofReal (‖∑ n ∈ Finset.Icc 1 N, X n ω‖ / Real.sqrt N)

private theorem norm_summatory_le (N : ℕ) (ω : Omega) :
    ‖∑ n ∈ Finset.Icc 1 N, X n ω‖ ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ‖X n ω‖ := norm_sum_le _ _
    _ = _ := by simp [norm_X]

private theorem measurable_summatory (N : ℕ) :
    Measurable (fun ω => ∑ n ∈ Finset.Icc 1 N, X n ω) :=
  Finset.measurable_sum _ (fun n _ => measurable_X n)

theorem measurable_steinhausNormalizedSummatoryNorm (N : ℕ) :
    Measurable (steinhausNormalizedSummatoryNorm N) :=
  ((measurable_summatory N).norm.div_const (Real.sqrt N)).ennreal_ofReal

private theorem integrable_frozen_summatory_normSq (y N : ℕ) (ω : Omega) :
    Integrable (fun η => ‖∑ n ∈ Finset.Icc 1 N,
      X n (freezeSteinhausPrefix (Nat.primesBelow y) ω η)‖ ^ (2 : ℕ)) steinhausMeasure := by
  have hm : Measurable (fun η => ‖∑ n ∈ Finset.Icc 1 N,
      X n (freezeSteinhausPrefix (Nat.primesBelow y) ω η)‖ ^ (2 : ℕ)) := by
    simpa only [Function.comp_def] using
      (((measurable_summatory N).comp
        (continuous_freezeSteinhausPrefix (Nat.primesBelow y) ω).measurable).norm.pow_const 2)
  refine Integrable.mono' (integrable_const ((N : ℝ) ^ (2 : ℕ))) hm.aestronglyMeasurable ?_
  filter_upwards with η
  have h := norm_summatory_le N (freezeSteinhausPrefix (Nat.primesBelow y) ω η)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg (∑ n ∈ Finset.Icc 1 N,
    X n (freezeSteinhausPrefix (Nat.primesBelow y) ω η))]

/-- The conditional squared normalized magnitude is the literal normalized variance. -/
theorem lintegral_steinhausNormalizedSummatoryNorm_frozen_sq (y N : ℕ) (ω : Omega) :
    (∫⁻ η, steinhausNormalizedSummatoryNorm N
      (freezeSteinhausPrefix (Nat.primesBelow y) ω η) ^ (2 : ℝ) ∂steinhausMeasure) =
      ENNReal.ofReal (steinhausNormalizedFrozenSummatoryVariance y N ω) := by
  have hp (η : Omega) : steinhausNormalizedSummatoryNorm N
      (freezeSteinhausPrefix (Nat.primesBelow y) ω η) ^ (2 : ℝ) =
      ENNReal.ofReal (‖∑ n ∈ Finset.Icc 1 N,
        X n (freezeSteinhausPrefix (Nat.primesBelow y) ω η)‖ ^ (2 : ℕ) / N) := by
    rw [steinhausNormalizedSummatoryNorm, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) 2,
      div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [lintegral_congr hp]
  have hi := (integrable_frozen_summatory_normSq y N ω).div_const (N : ℝ)
  have hnonneg : 0 ≤ᵐ[steinhausMeasure] (fun η =>
      ‖∑ n ∈ Finset.Icc 1 N, X n (freezeSteinhausPrefix (Nat.primesBelow y) ω η)‖ ^
        (2 : ℕ) / N) :=
    Filter.Eventually.of_forall (fun _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg, integral_div]
  rfl

/-- Fixed-prefix Cauchy mass and deterministic arithmetic error control the original first moment. -/
theorem lintegral_steinhausNormalizedSummatoryNorm_le (y N : ℕ) :
    (∫⁻ ω, steinhausNormalizedSummatoryNorm N ω ∂steinhausMeasure) ≤
      (∫⁻ ω, steinhausEulerCauchyMass y ω ^ (1 / 2 : ℝ) ∂steinhausMeasure) +
        ENNReal.ofReal (steinhausSmoothPairCountError y N) ^ (1 / 2 : ℝ) := by
  have hpoint (ω : Omega) :
      ENNReal.ofReal (steinhausNormalizedFrozenSummatoryVariance y N ω) ^ (1 / 2 : ℝ) ≤
        steinhausEulerCauchyMass y ω ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (steinhausSmoothPairCountError y N) ^ (1 / 2 : ℝ) := by
    have hV : steinhausNormalizedFrozenSummatoryVariance y N ω ≤
        (steinhausEulerCauchyMass y ω).toReal + steinhausSmoothPairCountError y N := by
      have h := abs_steinhausNormalizedFrozenSummatoryVariance_sub_cauchyMass_le y N ω
      have ha := le_abs_self (steinhausNormalizedFrozenSummatoryVariance y N ω -
        (steinhausEulerCauchyMass y ω).toReal)
      linarith
    have hE : ENNReal.ofReal (steinhausNormalizedFrozenSummatoryVariance y N ω) ≤
        steinhausEulerCauchyMass y ω + ENNReal.ofReal (steinhausSmoothPairCountError y N) := by
      have h := ENNReal.ofReal_le_ofReal hV
      rwa [ENNReal.ofReal_add ENNReal.toReal_nonneg (steinhausSmoothPairCountError_nonneg y N),
        ENNReal.ofReal_toReal (steinhausEulerCauchyMass_ne_top y ω)] at h
    exact (ENNReal.rpow_le_rpow hE (by norm_num)).trans
      (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num))
  calc
    _ ≤ ∫⁻ ω, (∫⁻ η, steinhausNormalizedSummatoryNorm N
        (freezeSteinhausPrefix (Nat.primesBelow y) ω η) ^ (2 : ℝ) ∂steinhausMeasure) ^
          (1 / 2 : ℝ) ∂steinhausMeasure :=
      lintegral_le_frozenPrefix_secondMoment_sqrt _ _ (measurable_steinhausNormalizedSummatoryNorm N)
    _ = ∫⁻ ω, ENNReal.ofReal (steinhausNormalizedFrozenSummatoryVariance y N ω) ^
        (1 / 2 : ℝ) ∂steinhausMeasure := by
      simp_rw [lintegral_steinhausNormalizedSummatoryNorm_frozen_sq]
    _ ≤ ∫⁻ ω, (steinhausEulerCauchyMass y ω ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (steinhausSmoothPairCountError y N) ^ (1 / 2 : ℝ)) ∂steinhausMeasure :=
      lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_add_left ((measurable_steinhausEulerCauchyMass y).pow_const (1 / 2 : ℝ))]
      simp

/-- The first absolute moment of the original summatory polynomial is little-o of square-root N. -/
theorem tendsto_lintegral_steinhausNormalizedSummatoryNorm :
    Tendsto (fun N => ∫⁻ ω, steinhausNormalizedSummatoryNorm N ω ∂steinhausMeasure)
      atTop (𝓝 0) := by
  apply ENNReal.tendsto_atTop_zero.mpr
  intro δ hδ
  have hb : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  obtain ⟨y, hy⟩ := ENNReal.tendsto_atTop_zero.mp
    tendsto_lintegral_steinhausEulerCauchyMass_sqrt (δ / 2) hb
  have herr : Tendsto (fun N => ENNReal.ofReal (steinhausSmoothPairCountError y N) ^
      (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp (tendsto_steinhausSmoothPairCountError y)
    simpa only [Function.comp_def, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      using h.ennrpow_const (1 / 2 : ℝ)
  obtain ⟨N₀, hN₀⟩ := ENNReal.tendsto_atTop_zero.mp herr (δ / 2) hb
  refine ⟨N₀, fun N hN => ?_⟩
  exact (lintegral_steinhausNormalizedSummatoryNorm_le y N).trans
    ((add_le_add (hy y le_rfl) (hN₀ N hN)).trans_eq (ENNReal.add_halves δ))

/-- The nonnegative normalized moment equals the ordinary real first moment at the same scale. -/
theorem lintegral_steinhausNormalizedSummatoryNorm_eq_ofReal (N : ℕ) :
    (∫⁻ ω, steinhausNormalizedSummatoryNorm N ω ∂steinhausMeasure) =
      ENNReal.ofReal ((∫ ω, ‖∑ n ∈ Finset.Icc 1 N, X n ω‖ ∂steinhausMeasure) / Real.sqrt N) := by
  have hi : Integrable (fun ω => ‖∑ n ∈ Finset.Icc 1 N, X n ω‖) steinhausMeasure := by
    refine Integrable.mono' (integrable_const (N : ℝ))
      (measurable_summatory N).norm.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [norm_norm]
    exact norm_summatory_le N ω
  have hn : 0 ≤ᵐ[steinhausMeasure] (fun ω =>
      ‖∑ n ∈ Finset.Icc 1 N, X n ω‖ / Real.sqrt N) :=
    Filter.Eventually.of_forall (fun _ => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  unfold steinhausNormalizedSummatoryNorm
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.div_const _) hn, integral_div]

/-- Unconditional arithmetic first-mean decay for the original completely multiplicative model. -/
theorem tendsto_integral_norm_steinhausSummatory_div_sqrt :
    Tendsto (fun N : ℕ =>
      (∫ ω, ‖∑ n ∈ Finset.Icc 1 N, X n ω‖ ∂steinhausMeasure) / Real.sqrt N)
        atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp
    tendsto_lintegral_steinhausNormalizedSummatoryNorm
  have heq (N : ℕ) : (∫⁻ ω, steinhausNormalizedSummatoryNorm N ω ∂steinhausMeasure).toReal =
      (∫ ω, ‖∑ n ∈ Finset.Icc 1 N, X n ω‖ ∂steinhausMeasure) / Real.sqrt N := by
    rw [lintegral_steinhausNormalizedSummatoryNorm_eq_ofReal,
      ENNReal.toReal_ofReal (div_nonneg (integral_nonneg (fun _ => norm_nonneg _))
        (Real.sqrt_nonneg _))]
  simpa only [Function.comp_def, heq, ENNReal.toReal_zero] using h

end RHTower

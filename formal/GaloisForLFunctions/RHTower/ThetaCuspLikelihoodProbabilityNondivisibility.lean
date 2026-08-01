import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodAtomicNondivisibility

/-!
# Normalized theta likelihood probability law and square-gap nondivisibility

`ThetaCuspLikelihoodAtomicNondivisibility` proves the square-gap obstruction for the
unnormalized seam carrier and for every nonzero scalar multiple.  This module identifies its exact
total mass with the source partition, constructs the literal normalized probability measure
`P_B`, and transfers every part of the obstruction to that law.

The final subclass interface does not manufacture an analytic definition of generalized gamma
convolution.  It packages precisely the standard defining inclusion needed by the paper:
every law in the supplied class is infinitely divisible.  The resulting exclusion is uniform over
every concrete GGC or Thorin-marginal formalization satisfying that inclusion.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
  GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal MeasureTheory

namespace RHTower

noncomputable section

/-! ### Exact total mass and normalization -/

/-- The total mass of the tilted higher carrier is exactly its fixed-measure Laplace response. -/
theorem thetaCuspHigherLikelihoodTiltedMeasure_univ
    {B : ℝ} (hB : 0 < B) :
    thetaCuspHigherLikelihoodTiltedMeasure B Set.univ =
      ENNReal.ofReal (thetaCuspHigherLikelihoodSpectralResponse B) := by
  rw [thetaCuspHigherLikelihoodTiltedMeasure,
    withDensity_apply _ MeasurableSet.univ]
  have hdensity :
      (fun t : ℝ => ((thetaCuspHigherLikelihoodTiltDensity B t : NNReal) : ENNReal)) =
        fun t : ℝ => ENNReal.ofReal (Real.exp (-B * t)) := by
    funext t
    rfl
  rw [hdensity]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB)
    (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)]
  rw [integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB]

/-- The unnormalized seam carrier has total mass exactly `Z(B)`. -/
theorem thetaCuspLikelihoodSeamTiltedMeasure_univ
    {B : ℝ} (hB : 0 < B) :
    thetaCuspLikelihoodSeamTiltedMeasure B Set.univ =
      ENNReal.ofReal (thetaCuspLikelihoodPartition B) := by
  rw [thetaCuspLikelihoodSeamTiltedMeasure, Measure.add_apply,
    thetaCuspHigherLikelihoodTiltedMeasure_univ hB]
  have hresponse : 0 ≤ thetaCuspHigherLikelihoodSpectralResponse B := by
    rw [← integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB]
    exact integral_nonneg fun _ => (Real.exp_pos _).le
  rw [thetaCuspLikelihoodPartition,
    ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hresponse]
  simp

/-- Literal normalized theta seam likelihood
`P_B = Z(B)⁻¹ • (δ₀ + exp(-B t) ν)`. -/
def thetaCuspLikelihoodProbabilityMeasure (B : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (thetaCuspLikelihoodPartition B))⁻¹ •
    thetaCuspLikelihoodSeamTiltedMeasure B

private theorem thetaCuspLikelihoodNormalization_ne_zero (B : ℝ) :
    (ENNReal.ofReal (thetaCuspLikelihoodPartition B))⁻¹ ≠ 0 :=
  (@ENNReal.inv_ne_zero
    (ENNReal.ofReal (thetaCuspLikelihoodPartition B))).mpr ENNReal.ofReal_ne_top

/-- For every positive spectral coordinate, the normalized law has total mass one. -/
theorem thetaCuspLikelihoodProbabilityMeasure_univ
    {B : ℝ} (hB : 0 < B) :
    thetaCuspLikelihoodProbabilityMeasure B Set.univ = 1 := by
  rw [thetaCuspLikelihoodProbabilityMeasure, Measure.smul_apply,
    thetaCuspLikelihoodSeamTiltedMeasure_univ hB, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (thetaCuspLikelihoodPartition_pos hB))
    ENNReal.ofReal_ne_top

/-- The normalized carrier is an actual probability measure, not merely a nonzero scalar
multiple of the source carrier. -/
theorem thetaCuspLikelihoodProbabilityMeasure_isProbabilityMeasure
    {B : ℝ} (hB : 0 < B) :
    IsProbabilityMeasure (thetaCuspLikelihoodProbabilityMeasure B) :=
  ⟨thetaCuspLikelihoodProbabilityMeasure_univ hB⟩

/-- Probability-measure wrapper for the normalized likelihood `P_B`. -/
def thetaCuspLikelihoodProbabilityLaw (B : ℝ) (hB : 0 < B) :
    ProbabilityMeasure ℝ :=
  ⟨thetaCuspLikelihoodProbabilityMeasure B,
    thetaCuspLikelihoodProbabilityMeasure_isProbabilityMeasure hB⟩

/-! ### Half-line support -/

theorem ae_nonneg_thetaCuspHigherLikelihoodTiltedMeasure (B : ℝ) :
    ∀ᵐ t ∂thetaCuspHigherLikelihoodTiltedMeasure B, 0 ≤ t := by
  rw [thetaCuspHigherLikelihoodTiltedMeasure,
    ae_withDensity_iff
      (measurable_thetaCuspHigherLikelihoodTiltDensity B).coe_nnreal_ennreal]
  filter_upwards [ae_nonneg_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
  exact fun _ => ht

theorem ae_nonneg_thetaCuspLikelihoodSeamTiltedMeasure (B : ℝ) :
    ∀ᵐ t ∂thetaCuspLikelihoodSeamTiltedMeasure B, 0 ≤ t := by
  rw [thetaCuspLikelihoodSeamTiltedMeasure, ae_add_measure_iff]
  constructor
  · rw [ae_dirac_iff measurableSet_Ici]
  · exact ae_nonneg_thetaCuspHigherLikelihoodTiltedMeasure B

/-- The normalized likelihood is carried by the intrinsic half-line `[0, ∞)`. -/
theorem ae_nonneg_thetaCuspLikelihoodProbabilityMeasure (B : ℝ) :
    ∀ᵐ t ∂thetaCuspLikelihoodProbabilityMeasure B, 0 ≤ t := by
  rw [thetaCuspLikelihoodProbabilityMeasure]
  apply Measure.ae_smul_measure
  exact ae_nonneg_thetaCuspLikelihoodSeamTiltedMeasure B

theorem thetaCuspLikelihoodProbabilityMeasure_Iio_zero (B : ℝ) :
    thetaCuspLikelihoodProbabilityMeasure B (Set.Iio 0) = 0 := by
  have h := ae_nonneg_thetaCuspLikelihoodProbabilityMeasure B
  change thetaCuspLikelihoodProbabilityMeasure B {a : ℝ | a < 0} = 0
  simpa only [not_le] using ae_iff.mp h

/-! ### Exact normalized atoms -/

theorem thetaCuspLikelihoodProbabilityMeasure_singleton_zero (B : ℝ) :
    thetaCuspLikelihoodProbabilityMeasure B {0} =
      (ENNReal.ofReal (thetaCuspLikelihoodPartition B))⁻¹ := by
  rw [thetaCuspLikelihoodProbabilityMeasure, Measure.smul_apply, smul_eq_mul,
    thetaCuspLikelihoodSeamTiltedMeasure_singleton_zero, mul_one]

theorem thetaCuspLikelihoodProbabilityMeasure_singleton_three (B : ℝ) :
    thetaCuspLikelihoodProbabilityMeasure B {3} =
      (ENNReal.ofReal (thetaCuspLikelihoodPartition B))⁻¹ *
        (((thetaCuspHigherLikelihoodTiltDensity B 3 : NNReal) : ENNReal) *
          ENNReal.ofReal (thetaCuspLikelihoodAtomWeight 2)) := by
  rw [thetaCuspLikelihoodProbabilityMeasure, Measure.smul_apply, smul_eq_mul,
    thetaCuspLikelihoodSeamTiltedMeasure_singleton_three]

/-- Exact paper formula `P_B{3} = Z(B)⁻¹ exp(-3B) exp(-9/2) 2⁴`. -/
theorem thetaCuspLikelihoodProbabilityMeasure_singleton_three_explicit (B : ℝ) :
    thetaCuspLikelihoodProbabilityMeasure B {3} =
      (ENNReal.ofReal (thetaCuspLikelihoodPartition B))⁻¹ *
        ENNReal.ofReal
          (Real.exp (-3 * B) * (Real.exp (-(9 / 2 : ℝ)) * 16)) := by
  rw [thetaCuspLikelihoodProbabilityMeasure_singleton_three]
  congr 1
  change ENNReal.ofReal (Real.exp (-B * 3)) *
      ENNReal.ofReal (thetaCuspLikelihoodAtomWeight 2) = _
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  congr 1
  · ring_nf
  · norm_num [thetaCuspLikelihoodAtomWeight, thetaCuspLikelihoodGap]

theorem thetaCuspLikelihoodProbabilityMeasure_singleton_zero_pos
    {B : ℝ} (_hB : 0 < B) :
    0 < thetaCuspLikelihoodProbabilityMeasure B {0} := by
  rw [pos_iff_ne_zero,
    thetaCuspLikelihoodProbabilityMeasure_singleton_zero]
  exact thetaCuspLikelihoodNormalization_ne_zero B

theorem thetaCuspLikelihoodProbabilityMeasure_singleton_three_ne_zero
    (B : ℝ) :
    thetaCuspLikelihoodProbabilityMeasure B {3} ≠ 0 := by
  rw [thetaCuspLikelihoodProbabilityMeasure, Measure.smul_apply, smul_eq_mul]
  exact mul_ne_zero
    (thetaCuspLikelihoodNormalization_ne_zero B)
    (thetaCuspLikelihoodSeamTiltedMeasure_singleton_three_ne_zero B)

theorem thetaCuspLikelihoodProbabilityMeasure_singleton_three_pos (B : ℝ) :
    0 < thetaCuspLikelihoodProbabilityMeasure B {3} :=
  pos_iff_ne_zero.mpr
    (thetaCuspLikelihoodProbabilityMeasure_singleton_three_ne_zero B)

theorem thetaCuspLikelihoodProbabilityMeasure_singleton_six (B : ℝ) :
    thetaCuspLikelihoodProbabilityMeasure B {6} = 0 := by
  rw [thetaCuspLikelihoodProbabilityMeasure, Measure.smul_apply, smul_eq_mul,
    thetaCuspLikelihoodSeamTiltedMeasure_singleton_six, mul_zero]

/-! ### Square-gap survivor and nondivisibility -/

/-- The normalized atom support charges `3` but not `3 + 3`. -/
theorem not_additivelyClosedAtomSupport_thetaCuspLikelihoodProbabilityMeasure
    (B : ℝ) :
    ¬ AdditivelyClosedAtomSupport (thetaCuspLikelihoodProbabilityMeasure B) :=
  not_additivelyClosedAtomSupport_smul_thetaCuspLikelihoodSeamTiltedMeasure
    B (thetaCuspLikelihoodNormalization_ne_zero B)

/-- The normalized two-particle law creates the missing atom at `6`. -/
theorem thetaCuspLikelihoodProbabilityMeasure_selfConv_singleton_six_ne_zero
    (B : ℝ) :
    (thetaCuspLikelihoodProbabilityMeasure B ∗
      thetaCuspLikelihoodProbabilityMeasure B) {6} ≠ 0 := by
  let μ := thetaCuspLikelihoodProbabilityMeasure B
  letI : SFinite μ := by
    dsimp [μ, thetaCuspLikelihoodProbabilityMeasure,
      thetaCuspLikelihoodSeamTiltedMeasure,
      thetaCuspHigherLikelihoodTiltedMeasure,
      thetaCuspHigherLikelihoodSpectralMeasure,
      thetaCuspAtomLikelihoodSpectralMeasure]
    infer_instance
  have hbound : μ {3} * μ {3} ≤ (μ ∗ μ) {6} := by
    have h := measure_singleton_le_conv μ μ (3 : ℝ) 3
    norm_num at h
    exact h
  intro hzero
  have hleft : μ {3} * μ {3} = 0 :=
    nonpos_iff_eq_zero.mp (hbound.trans_eq hzero)
  exact mul_ne_zero
    (thetaCuspLikelihoodProbabilityMeasure_singleton_three_ne_zero B)
    (thetaCuspLikelihoodProbabilityMeasure_singleton_three_ne_zero B) hleft

/-- The literal normalized probability law `P_B` is not infinitely divisible. -/
theorem thetaCuspLikelihoodProbabilityMeasure_not_infinitelyDivisible
    (B : ℝ) :
    ¬ InfinitelyDivisible (thetaCuspLikelihoodProbabilityMeasure B) :=
  not_infinitelyDivisible_smul_thetaCuspLikelihoodSeamTiltedMeasure
    B (thetaCuspLikelihoodNormalization_ne_zero B)

/-! ### GGC and Thorin-subordinator exclusions -/

/-- Interface for a concrete law class whose defining data imply infinite divisibility.  This is
the exact parent property used for generalized gamma convolutions and Thorin-subordinator
marginals. -/
structure InfinitelyDivisibleLawClass where
  Mem : Measure ℝ → Prop
  infinitelyDivisible : ∀ μ, Mem μ → InfinitelyDivisible μ

/-- `P_B` belongs to no generalized-gamma-convolution class carrying its standard
infinite-divisibility inclusion. -/
theorem thetaCuspLikelihoodProbabilityMeasure_not_generalizedGammaConvolution
    (B : ℝ) (ggc : InfinitelyDivisibleLawClass) :
    ¬ ggc.Mem (thetaCuspLikelihoodProbabilityMeasure B) := by
  intro hggc
  exact thetaCuspLikelihoodProbabilityMeasure_not_infinitelyDivisible B
    (ggc.infinitelyDivisible _ hggc)

/-- `P_B` is not a marginal of any Thorin-subordinator class carrying its standard
infinite-divisibility inclusion. -/
theorem thetaCuspLikelihoodProbabilityMeasure_not_thorinSubordinatorMarginal
    (B : ℝ) (thorinMarginal : InfinitelyDivisibleLawClass) :
    ¬ thorinMarginal.Mem (thetaCuspLikelihoodProbabilityMeasure B) := by
  intro hthorin
  exact thetaCuspLikelihoodProbabilityMeasure_not_infinitelyDivisible B
    (thorinMarginal.infinitelyDivisible _ hthorin)

end

end RHTower

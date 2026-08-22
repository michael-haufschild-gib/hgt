import GaloisForLFunctions.HTGeometry.GaussianCovarianceStableRankLowerTail
import GaloisForLFunctions.HTGeometry.SubspaceOptimalDesign

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def gaussianHalfActivationTube
    {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) : Set E :=
  {v | ‖A v‖ ^ 2 ≤
    (gaussianIntervalActivationMass / 2) *
      ∑ i : Fin n, A.singularValues i ^ 2}

theorem measurableSet_gaussianHalfActivationTube
    {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    (A : E →ₗ[ℝ] F) :
    MeasurableSet (gaussianHalfActivationTube (n := n) A) := by
  exact measurableSet_le
    ((LinearMap.continuous_of_finiteDimensional A).norm.pow 2).measurable measurable_const

def gaussianWeightedHalfActivationTubeMass
    {n : ℕ} {C E F : Type*} [Fintype C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : C → E →ₗ[ℝ] F) (w : C → ℝ) (v : E) : ℝ :=
  ∑ c, w c * Set.indicator
    (gaussianHalfActivationTube (n := n) (A c)) (1 : E → ℝ) v

theorem gaussianWeightedHalfActivationTubeMass_nonneg
    {n : ℕ} {C E F : Type*} [Fintype C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : C → E →ₗ[ℝ] F) (w : C → ℝ) (hw : ∀ c, 0 ≤ w c) (v : E) :
    0 ≤ gaussianWeightedHalfActivationTubeMass (n := n) A w v := by
  unfold gaussianWeightedHalfActivationTubeMass
  exact Finset.sum_nonneg fun c _ => mul_nonneg (hw c) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem gaussianWeightedHalfActivationTubeMass_le_one
    {n : ℕ} {C E F : Type*} [Fintype C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : C → E →ₗ[ℝ] F) (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C) (v : E) :
    gaussianWeightedHalfActivationTubeMass (n := n) A w v ≤ 1 := by
  unfold gaussianWeightedHalfActivationTubeMass
  calc
    (∑ c, w c * Set.indicator
      (gaussianHalfActivationTube (n := n) (A c)) (1 : E → ℝ) v) ≤
        ∑ c, w c * 1 := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _ (hw.1 c)
      by_cases hc : v ∈ gaussianHalfActivationTube (n := n) (A c)
      · simp [Set.indicator_of_mem hc]
      · simp [Set.indicator_of_notMem hc]
    _ = 1 := by rw [← Finset.sum_mul, hw.2, one_mul]

theorem measurable_gaussianWeightedHalfActivationTubeMass
    {n : ℕ} {C E F : Type*} [Fintype C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    (A : C → E →ₗ[ℝ] F) (w : C → ℝ) :
    Measurable (gaussianWeightedHalfActivationTubeMass (n := n) A w) := by
  unfold gaussianWeightedHalfActivationTubeMass
  apply Finset.measurable_sum
  intro c _
  exact (measurable_one.indicator
    (measurableSet_gaussianHalfActivationTube (n := n) (A c))).const_mul (w c)

theorem integral_gaussianWeightedHalfActivationTubeMass
    {n : ℕ} {C E F : Type*} [Fintype C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ]
    (A : C → E →ₗ[ℝ] F) (w : C → ℝ) :
    (∫ v, gaussianWeightedHalfActivationTubeMass (n := n) A w v ∂μ) =
      ∑ c, w c * μ.real (gaussianHalfActivationTube (n := n) (A c)) := by
  unfold gaussianWeightedHalfActivationTubeMass
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro c _
    rw [integral_const_mul, integral_indicator_one
      (measurableSet_gaussianHalfActivationTube (n := n) (A c))]
  · intro c _
    exact ((integrable_const (1 : ℝ)).indicator
      (measurableSet_gaussianHalfActivationTube (n := n) (A c))).const_mul (w c)

/-- Weighted Gaussian observer law: a probability design eliminates target-family cardinality.
Only the design-averaged individual lower tails remain. -/
theorem stdGaussian_measure_weightedHalfActivationTubeMass_ge_le
    {n : ℕ} {C E F : Type*} [Fintype C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    (A : C → E →ₗ[ℝ] F) (hn : Module.finrank ℝ E = n)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian E).real {v |
        κ ≤ gaussianWeightedHalfActivationTubeMass (n := n) A w v} ≤
      (∑ c, w c * Real.exp
        (-(gaussianIntervalActivationMass ^ 2 / 2) *
          ((∑ i : Fin n, (A c).singularValues i ^ 2) ^ 2 /
            ∑ i : Fin n, (A c).singularValues i ^ 4))) / κ := by
  have hmeas := measurable_gaussianWeightedHalfActivationTubeMass (n := n) A w
  have hnonneg : 0 ≤ᵐ[stdGaussian E]
      gaussianWeightedHalfActivationTubeMass (n := n) A w :=
    Filter.Eventually.of_forall fun v =>
      gaussianWeightedHalfActivationTubeMass_nonneg A w hw.1 v
  have hint : Integrable
      (gaussianWeightedHalfActivationTubeMass (n := n) A w) (stdGaussian E) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg
      (gaussianWeightedHalfActivationTubeMass_nonneg A w hw.1 v)]
    exact gaussianWeightedHalfActivationTubeMass_le_one A w hw v
  have hmark := mul_meas_ge_le_integral_of_nonneg hnonneg hint κ
  have hintEq := integral_gaussianWeightedHalfActivationTubeMass
    (n := n) (stdGaussian E) A w
  rw [hintEq] at hmark
  apply (le_div_iff₀ hκ).2
  rw [mul_comm]
  refine hmark.trans ?_
  apply Finset.sum_le_sum
  intro c _
  exact mul_le_mul_of_nonneg_left
    (stdGaussian_measure_linearMap_norm_sq_le_halfActivation (A c) hn)
    (hw.1 c)

/-- Common stable-rank floor form. Target count disappears completely. -/
theorem stdGaussian_measure_weightedHalfActivationTubeMass_ge_le_stableFloor
    {n : ℕ} {C E F : Type*} [Fintype C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    (A : C → E →ₗ[ℝ] F) (hn : Module.finrank ℝ E = n)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (stableFloor : ℝ)
    (hstable : ∀ c, stableFloor ≤
      (∑ i : Fin n, (A c).singularValues i ^ 2) ^ 2 /
        ∑ i : Fin n, (A c).singularValues i ^ 4)
    {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian E).real {v |
        κ ≤ gaussianWeightedHalfActivationTubeMass (n := n) A w v} ≤
      Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) * stableFloor) / κ := by
  refine (stdGaussian_measure_weightedHalfActivationTubeMass_ge_le
    A hn w hw hκ).trans ?_
  apply div_le_div_of_nonneg_right _ hκ.le
  calc
    (∑ c, w c * Real.exp
        (-(gaussianIntervalActivationMass ^ 2 / 2) *
          ((∑ i : Fin n, (A c).singularValues i ^ 2) ^ 2 /
            ∑ i : Fin n, (A c).singularValues i ^ 4))) ≤
      ∑ c, w c * Real.exp
        (-(gaussianIntervalActivationMass ^ 2 / 2) * stableFloor) := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _ (hw.1 c)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (hstable c)
        (neg_nonpos.mpr (by positivity))
    _ = Real.exp
        (-(gaussianIntervalActivationMass ^ 2 / 2) * stableFloor) := by
      rw [← Finset.sum_mul, hw.2, one_mul]

end

end GaloisForLFunctions.HTGeometry

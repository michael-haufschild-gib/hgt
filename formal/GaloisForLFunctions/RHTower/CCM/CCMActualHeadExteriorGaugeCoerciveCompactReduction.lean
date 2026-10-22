import GaloisForLFunctions.RHTower.CCM.CCMActualHeadExteriorCosineMeasureGauge
import GaloisForLFunctions.RHTower.CCM.CCMPrimeFreeApertureCharacteristicPair

/-!
# Coercive compact reduction for exterior CCM gauges

The source-faithful corrected CCM symbol is identified with its earlier explicit finite-prime
formula. Its Gamma channel is coercive while its polar, finite-prime, and arbitrary finite-measure
cosine-gauge channels are uniformly bounded. Hence every signed finite exterior-measure
representative tends to positive infinity at both frequency tails. Global representative
nonnegativity is therefore equivalent to nonnegativity on one compact symmetric interval.
-/


open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

theorem correctedCCMSymbol_eq_ccmCorrectedSymbol (a xi : ℝ) :
    correctedCCMSymbol a xi =
      GaloisForLFunctions.RHTower.ccmCorrectedSymbol a xi := by
  have hsum :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        criticalMellinAtomWeight k * Real.cos (xi * Real.log k)) =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1 : ℝ) / 2) *
          Real.cos (xi * Real.log k) := by
    apply Finset.sum_congr rfl
    intro k _hk
    unfold criticalMellinAtomWeight
    ring
  unfold correctedCCMSymbol ccmArchimedeanMultiplier polarPrimeStieltjesSymbol polarMultiplier
    criticalMellinPrimeCosineModule
    GaloisForLFunctions.RHTower.ccmCorrectedSymbol
    GaloisForLFunctions.RHTower.ccmArchSymbol
    GaloisForLFunctions.RHTower.ccmPrimeCutoffSum
    GaloisForLFunctions.RHTower.ccmPolarMultiplier
  rw [hsum]
  norm_num [div_eq_mul_inv]
  ring

theorem criticalMellinPrimeCosineModule_eq_two_ccmPrimeCutoffSum (a xi : ℝ) :
    criticalMellinPrimeCosineModule a xi =
      2 * GaloisForLFunctions.RHTower.ccmPrimeCutoffSum a xi := by
  unfold criticalMellinPrimeCosineModule criticalMellinAtomWeight
    GaloisForLFunctions.RHTower.ccmPrimeCutoffSum
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- Total absolute mass of the finite prime cosine channel at aperture `a`. -/
def ccmFinitePrimeCosineMass (a : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
    |ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1 : ℝ) / 2)|

/-- Explicit uniform budget for every bounded polar--prime perturbation. -/
def ccmPolarPrimeUniformBudget (a : ℝ) : ℝ :=
  8 * |Real.sinh a| + 4 * Real.cosh a + 2 * ccmFinitePrimeCosineMass a

theorem abs_ccmPrimeCutoffSum_le_finitePrimeCosineMass (a xi : ℝ) :
    |GaloisForLFunctions.RHTower.ccmPrimeCutoffSum a xi| ≤
      ccmFinitePrimeCosineMass a := by
  unfold GaloisForLFunctions.RHTower.ccmPrimeCutoffSum ccmFinitePrimeCosineMass
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k _hk
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem abs_polarPrimeStieltjesSymbol_le_uniformBudget (a xi : ℝ) :
    |polarPrimeStieltjesSymbol a xi| ≤ ccmPolarPrimeUniformBudget a := by
  rw [show polarPrimeStieltjesSymbol a xi =
      GaloisForLFunctions.RHTower.ccmPolarMultiplier a xi -
        2 * GaloisForLFunctions.RHTower.ccmPrimeCutoffSum a xi by
    rw [polarPrimeStieltjesSymbol,
      criticalMellinPrimeCosineModule_eq_two_ccmPrimeCutoffSum]
    rfl]
  refine (abs_sub _ _).trans ?_
  have hpolar := GaloisForLFunctions.RHTower.abs_ccmPolarMultiplier_le a xi
  have hprime := abs_ccmPrimeCutoffSum_le_finitePrimeCosineMass a xi
  rw [abs_mul]
  norm_num
  unfold ccmPolarPrimeUniformBudget
  linarith

theorem correctedCCMSymbol_lower_bound (a xi : ℝ) :
    GaloisForLFunctions.RHTower.ccmArchSymbol xi - ccmPolarPrimeUniformBudget a ≤
      correctedCCMSymbol a xi := by
  rw [correctedCCMSymbol_eq_ccmCorrectedSymbol]
  unfold GaloisForLFunctions.RHTower.ccmCorrectedSymbol
  have hpolar := GaloisForLFunctions.RHTower.abs_ccmPolarMultiplier_le a xi
  have hprime := abs_ccmPrimeCutoffSum_le_finitePrimeCosineMass a xi
  have hpolarLower :
      -(8 * |Real.sinh a| + 4 * Real.cosh a) ≤
        GaloisForLFunctions.RHTower.ccmPolarMultiplier a xi :=
    neg_le_of_abs_le hpolar
  have hprimeUpper :
      GaloisForLFunctions.RHTower.ccmPrimeCutoffSum a xi ≤
        ccmFinitePrimeCosineMass a := le_trans (le_abs_self _) hprime
  unfold ccmPolarPrimeUniformBudget
  linarith

theorem tendsto_correctedCCMSymbol_atTop (a : ℝ) :
    Tendsto (correctedCCMSymbol a) atTop atTop := by
  have hshift := tendsto_atTop_add_const_right atTop
    (-ccmPolarPrimeUniformBudget a)
    GaloisForLFunctions.RHTower.tendsto_ccmArchSymbol_atTop
  exact tendsto_atTop_mono (correctedCCMSymbol_lower_bound a) hshift

theorem correctedCCMSymbol_even (a xi : ℝ) :
    correctedCCMSymbol a (-xi) = correctedCCMSymbol a xi := by
  rw [correctedCCMSymbol_eq_ccmCorrectedSymbol,
    correctedCCMSymbol_eq_ccmCorrectedSymbol,
    GaloisForLFunctions.RHTower.ccmCorrectedSymbol_even]

theorem tendsto_correctedCCMSymbol_atBot (a : ℝ) :
    Tendsto (correctedCCMSymbol a) atBot atTop := by
  have h := (tendsto_correctedCCMSymbol_atTop a).comp tendsto_neg_atBot_atTop
  exact h.congr' (Filter.Eventually.of_forall fun xi =>
    correctedCCMSymbol_even a xi)

theorem continuous_correctedCCMSymbol (a : ℝ) :
    Continuous (correctedCCMSymbol a) := by
  have hfun : correctedCCMSymbol a =
      GaloisForLFunctions.RHTower.ccmCorrectedSymbol a :=
    funext (correctedCCMSymbol_eq_ccmCorrectedSymbol a)
  rw [hfun]
  exact GaloisForLFunctions.RHTower.continuous_ccmCorrectedSymbol a

theorem abs_ccmActualHeadExteriorCosineMeasureGauge_le_measureReal
    (mu : Measure ℝ) [IsFiniteMeasure mu] (xi : ℝ) :
    |ccmActualHeadExteriorCosineMeasureGauge mu xi| ≤ mu.real Set.univ := by
  unfold ccmActualHeadExteriorCosineMeasureGauge
  simpa only [Real.norm_eq_abs, one_mul] using
    (MeasureTheory.norm_integral_le_of_norm_le_const (μ := mu)
      (f := fun h : ℝ => Real.cos (2 * Real.pi * h * xi)) (C := 1)
      (Filter.Eventually.of_forall fun h => Real.abs_cos_le_one _))

theorem ccmActualHeadExteriorCosineMeasureGauge_even
    (mu : Measure ℝ) (xi : ℝ) :
    ccmActualHeadExteriorCosineMeasureGauge mu (-xi) =
      ccmActualHeadExteriorCosineMeasureGauge mu xi := by
  unfold ccmActualHeadExteriorCosineMeasureGauge
  apply MeasureTheory.integral_congr_ae
  filter_upwards with h
  rw [show 2 * Real.pi * h * -xi = -(2 * Real.pi * h * xi) by ring, Real.cos_neg]

theorem ccmCorrectedExteriorMeasureGaugeRepresentative_even
    (a : SuzukiPositiveAperture) (mu nu : Measure ℝ) (xi : ℝ) :
    ccmCorrectedExteriorMeasureGaugeRepresentative a mu nu (-xi) =
      ccmCorrectedExteriorMeasureGaugeRepresentative a mu nu xi := by
  unfold ccmCorrectedExteriorMeasureGaugeRepresentative
  rw [show 2 * Real.pi * -xi = -(2 * Real.pi * xi) by ring,
    correctedCCMSymbol_even,
    ccmActualHeadExteriorCosineMeasureGauge_even,
    ccmActualHeadExteriorCosineMeasureGauge_even]

theorem correctedExteriorMeasureGaugeRepresentative_lower_bound
    (a : SuzukiPositiveAperture) (mu nu : Measure ℝ)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] (xi : ℝ) :
    correctedCCMSymbol a.1 (2 * Real.pi * xi) - mu.real Set.univ - nu.real Set.univ ≤
      ccmCorrectedExteriorMeasureGaugeRepresentative a mu nu xi := by
  have hmu := abs_ccmActualHeadExteriorCosineMeasureGauge_le_measureReal mu xi
  have hnu := abs_ccmActualHeadExteriorCosineMeasureGauge_le_measureReal nu xi
  have hmuLower : -mu.real Set.univ ≤
      ccmActualHeadExteriorCosineMeasureGauge mu xi := neg_le_of_abs_le hmu
  have hnuUpper : ccmActualHeadExteriorCosineMeasureGauge nu xi ≤
      nu.real Set.univ := le_trans (le_abs_self _) hnu
  unfold ccmCorrectedExteriorMeasureGaugeRepresentative
  linarith

theorem tendsto_correctedExteriorMeasureGaugeRepresentative_atTop
    (a : SuzukiPositiveAperture) (mu nu : Measure ℝ)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    Tendsto (ccmCorrectedExteriorMeasureGaugeRepresentative a mu nu) atTop atTop := by
  have hscale : Tendsto (fun xi : ℝ => 2 * Real.pi * xi) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (mul_pos zero_lt_two Real.pi_pos)).2 tendsto_id
  have hcorrected := (tendsto_correctedCCMSymbol_atTop a.1).comp hscale
  have hshift := tendsto_atTop_add_const_right atTop
    (-(mu.real Set.univ) - nu.real Set.univ) hcorrected
  have hshift' : Tendsto (fun xi : ℝ =>
      correctedCCMSymbol a.1 (2 * Real.pi * xi) -
        mu.real Set.univ - nu.real Set.univ) atTop atTop := by
    convert hshift using 1
    ext xi
    simp only [Function.comp_apply]
    ring
  exact tendsto_atTop_mono
    (correctedExteriorMeasureGaugeRepresentative_lower_bound a mu nu) hshift'

theorem tendsto_correctedExteriorMeasureGaugeRepresentative_atBot
    (a : SuzukiPositiveAperture) (mu nu : Measure ℝ)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    Tendsto (ccmCorrectedExteriorMeasureGaugeRepresentative a mu nu) atBot atTop := by
  have h := (tendsto_correctedExteriorMeasureGaugeRepresentative_atTop a mu nu).comp
    tendsto_neg_atBot_atTop
  exact h.congr' (Filter.Eventually.of_forall fun xi =>
    ccmCorrectedExteriorMeasureGaugeRepresentative_even a mu nu xi)

/-- Every fixed finite-measure gauge representative is automatically positive outside a compact
frequency interval. -/
theorem exists_compactCore_correctedExteriorMeasureGaugeRepresentative_pos
    (a : SuzukiPositiveAperture) (mu nu : Measure ℝ)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    ∃ R : ℝ, 0 < R ∧ ∀ xi : ℝ, R ≤ |xi| →
      0 < ccmCorrectedExteriorMeasureGaugeRepresentative a mu nu xi := by
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1
    ((tendsto_correctedExteriorMeasureGaugeRepresentative_atTop a mu nu).eventually
      (eventually_gt_atTop 0))
  obtain ⟨c, hc⟩ := Filter.eventually_atBot.1
    ((tendsto_correctedExteriorMeasureGaugeRepresentative_atBot a mu nu).eventually
      (eventually_gt_atTop 0))
  let R : ℝ := max 1 (max b (-c))
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨R, hRpos, ?_⟩
  intro xi hxi
  by_cases hx : 0 ≤ xi
  · apply hb xi
    rw [abs_of_nonneg hx] at hxi
    exact (le_max_left b (-c)).trans ((le_max_right 1 (max b (-c))).trans hxi)
  · apply hc xi
    rw [abs_of_neg (lt_of_not_ge hx)] at hxi
    have hnegcR : -R ≤ c := by
      have hmc : -c ≤ R :=
        (le_max_right b (-c)).trans (le_max_right 1 (max b (-c)))
      linarith
    linarith

/-- Global nonnegativity of a fixed finite-measure representative is exactly a compact-core
condition; both frequency tails are automatic. -/
theorem exists_compactCore_nonneg_iff_correctedExteriorMeasureGaugeRepresentative_nonneg
    (a : SuzukiPositiveAperture) (mu nu : Measure ℝ)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    ∃ R : ℝ, 0 < R ∧
      ((∀ xi : ℝ, |xi| ≤ R →
          0 ≤ ccmCorrectedExteriorMeasureGaugeRepresentative a mu nu xi) ↔
        ∀ xi : ℝ,
          0 ≤ ccmCorrectedExteriorMeasureGaugeRepresentative a mu nu xi) := by
  obtain ⟨R, hR, houtside⟩ :=
    exists_compactCore_correctedExteriorMeasureGaugeRepresentative_pos a mu nu
  refine ⟨R, hR, ?_⟩
  constructor
  · intro hcore xi
    by_cases hxi : |xi| ≤ R
    · exact hcore xi hxi
    · exact (houtside xi (le_of_lt (lt_of_not_ge hxi))).le
  · intro hglobal xi _hxi
    exact hglobal xi

end RHTower


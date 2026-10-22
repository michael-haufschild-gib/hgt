import GaloisForLFunctions.RHTower.CCM.CCMSmoothSupportUncertainty

/-!
# An explicit support threshold for the full arithmetic energy gap

The low-frequency support bound and the literal Gamma Fourier weight give
`A (1 - 2 R |support u|) ||u||² <= ||u||²_form` whenever `A < weight(R)`.
Combining this with the full prime--pole envelope gives an explicit positive
measure threshold. No connectedness or sign condition on the source is used.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace RHTower

open ThetaSourceWard

/-- Exact Fourier support lower bound for the actual Gamma form norm. -/
theorem ccmSmooth_formNorm_lower_supportMeasure
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (A R : ℝ) (hA : 0 ≤ A) (hR : 0 < R) (hweight : A < ccmArchimedeanFormWeight R) :
    A * (1 - 2 * R * ccmSmoothSupportMeasure u) *
        ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 ≤ ‖u.toCCMFormVector‖ ^ 2 := by
  let f := ccmArchimedeanFormEmbedding a u.toCCMFormVector
  let P := fourierCutoff (centralInterval R) (measurableSet_centralInterval R)
  have hi : Integrable (fun xi : ℝ => ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) :=
    (Lp.memLp (fourierUnitary f)).integrable_norm_pow (by norm_num)
  have hsplit : (∫ xi in centralInterval R, ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) +
      ‖f - P f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [show P = fourierCutoff (centralInterval R) (measurableSet_centralInterval R) from rfl,
      norm_sq_sub_fourierCutoff_central_eq_tailIntegral,
      integral_indicator (measurableSet_centralInterval R).compl,
      integral_add_compl (measurableSet_centralInterval R) hi,
      ← norm_sq_eq_integral, fourierUnitary.norm_map]
  have hwindow := ccmSmooth_fourierWindow_mass_le_supportMeasure u R hR.le
  have htail : (1 - 2 * R * ccmSmoothSupportMeasure u) * ‖f‖ ^ 2 ≤ ‖f - P f‖ ^ 2 := by
    change (∫ xi in centralInterval R, ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) ≤
      2 * R * ccmSmoothSupportMeasure u * ‖f‖ ^ 2 at hwindow
    nlinarith
  have hbudget := mul_norm_sq_sub_fourierCutoff_ccmArchimedeanFormEmbedding_le a
    u.toCCMFormVector hR hweight
  calc
    _ = A * ((1 - 2 * R * ccmSmoothSupportMeasure u) * ‖f‖ ^ 2) := by ring
    _ ≤ A * ‖f - P f‖ ^ 2 := mul_le_mul_of_nonneg_left htail hA
    _ ≤ _ := hbudget

/-- A literal lower bound for the complete Weil source, retaining its support dependence. -/
theorem ccmSmooth_source_lower_supportMeasure
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (A R : ℝ) (hA : 0 ≤ A) (hR : 0 < R) (hweight : A < ccmArchimedeanFormWeight R) :
    (A * (1 - 2 * R * ccmSmoothSupportMeasure u) - ccmRestrictedWeilRemainderEnvelope a) *
        ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
  have hg := ccmSmooth_formNorm_lower_supportMeasure u A R hA hR hweight
  have hb := ccmRestrictedWeilForm_sourceRelative_lowerBound a u.toCCMFormVector
  rw [ccmRestrictedWeilForm_self_re_eq_source] at hb
  change ‖u.toCCMFormVector‖ ^ 2 - ccmRestrictedWeilRemainderEnvelope a *
    ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 ≤ _ at hb
  nlinarith

def ccmExplicitSupportFrequencyRadius (a : SuzukiPositiveAperture) (L : ℝ) : ℝ :=
  ccmArchimedeanBudgetFrequencyRadius
    (4 * (ccmRestrictedWeilRemainderEnvelope a + |L| + 1)) ⟨1, zero_lt_one⟩

def ccmExplicitSupportThreshold (a : SuzukiPositiveAperture) (L : ℝ) : ℝ :=
  1 / (4 * ccmExplicitSupportFrequencyRadius a L)

theorem ccmExplicitSupportFrequencyRadius_eq_exp (a : SuzukiPositiveAperture) (L : ℝ) :
    ccmExplicitSupportFrequencyRadius a L =
      Real.exp (ccmArchimedeanLogComparisonConstant *
        (4 * (ccmRestrictedWeilRemainderEnvelope a + |L| + 1) + 2)) := by
  unfold ccmExplicitSupportFrequencyRadius ccmArchimedeanBudgetFrequencyRadius
    ccmArchimedeanBudgetFrequencyLevel
  have hM := ccmRestrictedWeilRemainderEnvelope_nonneg a
  rw [max_eq_right (by positivity : 0 ≤ 4 * (ccmRestrictedWeilRemainderEnvelope a + |L| + 1))]
  simp only [one_pow, div_one]
  congr 1
  ring

theorem ccmExplicitSupportFrequencyRadius_pos (a : SuzukiPositiveAperture) (L : ℝ) :
    0 < ccmExplicitSupportFrequencyRadius a L :=
  ccmArchimedeanBudgetFrequencyRadius_pos _ _

theorem ccmExplicitSupportThreshold_pos (a : SuzukiPositiveAperture) (L : ℝ) :
    0 < ccmExplicitSupportThreshold a L := by
  unfold ccmExplicitSupportThreshold
  exact div_pos zero_lt_one (mul_pos (by norm_num) (ccmExplicitSupportFrequencyRadius_pos a L))

/-- An explicit support threshold gives arbitrary physical coercivity and retains half the form norm. -/
theorem ccmSmooth_explicitSupport_coercivity
    (a : SuzukiPositiveAperture) (L : ℝ) (u : CCMComplexSmoothInteriorSource a)
    (hu : ccmSmoothSupportMeasure u ≤ ccmExplicitSupportThreshold a L) :
    L * ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 +
        (1 / 2 : ℝ) * ‖u.toCCMFormVector‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
  let M := ccmRestrictedWeilRemainderEnvelope a
  let B := 4 * (M + |L| + 1)
  let A := ccmArchimedeanBudgetFrequencyLevel B ⟨1, zero_lt_one⟩
  let R := ccmExplicitSupportFrequencyRadius a L
  have hM : 0 ≤ M := ccmRestrictedWeilRemainderEnvelope_nonneg a
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hAval : A = 4 * (M + |L| + 1) + 1 := by
    simp only [A, ccmArchimedeanBudgetFrequencyLevel, one_pow, div_one, max_eq_right hB, B]
  have hA : 0 < A := ccmArchimedeanBudgetFrequencyLevel_pos B ⟨1, zero_lt_one⟩
  have hR : 0 < R := ccmExplicitSupportFrequencyRadius_pos a L
  have hweight : A < ccmArchimedeanFormWeight R :=
    ccmArchimedeanBudgetFrequencyLevel_lt_weight_radius B ⟨1, zero_lt_one⟩
  have hwindow : 2 * R * ccmSmoothSupportMeasure u ≤ (1 / 2 : ℝ) := by
    change ccmSmoothSupportMeasure u ≤ 1 / (4 * R) at hu
    have h := mul_le_mul_of_nonneg_left hu (show 0 ≤ 4 * R by positivity)
    rw [mul_one_div_cancel (show 4 * R ≠ 0 by positivity)] at h
    nlinarith
  have hcoefficient : 2 * (M + L) ≤ A * (1 - 2 * R * ccmSmoothSupportMeasure u) := by
    calc
      _ ≤ A / 2 := by rw [hAval]; linarith [le_abs_self L]
      _ ≤ _ := by
        have hmul := mul_nonneg hA.le (sub_nonneg.mpr hwindow)
        nlinarith
  have hform := ccmSmooth_formNorm_lower_supportMeasure u A R hA.le hR hweight
  have hpay := (mul_le_mul_of_nonneg_right hcoefficient
    (sq_nonneg ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖)).trans hform
  have hbase := ccmRestrictedWeilForm_sourceRelative_lowerBound a u.toCCMFormVector
  rw [ccmRestrictedWeilForm_self_re_eq_source] at hbase
  change ‖u.toCCMFormVector‖ ^ 2 - M *
    ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 ≤ _ at hbase
  nlinarith

/-- Explicit support control for the exact RH energy comparison, with all arithmetic terms. -/
theorem thetaThreeEnergy_explicitSupport_gap
    (a : SuzukiPositiveAperture) (L : ℝ) (u : CCMComplexSmoothInteriorSource a)
    (hu : ccmSmoothSupportMeasure u ≤ ccmExplicitSupportThreshold a L) :
    thetaPolarScalingEnergy thetaCuspTiltSource (ccmThetaGroundProfile u) +
        L * thetaGroundNormSq (ccmThetaGroundProfile u) +
        (1 / 2 : ℝ) * ‖u.toCCMFormVector‖ ^ 2 ≤
      thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource
          (ccmThetaGroundProfile u).toBoundedContinuousFunction +
        thetaGammaScalingEnergy thetaCuspTiltSource (ccmThetaGroundProfile u) := by
  have h := ccmSmooth_explicitSupport_coercivity a L u hu
  rw [ccmRestrictedWeilSourceQuadratic_eq_three_theta_energies] at h
  rw [thetaGroundNormSq_ccmProfile_eq_physical]
  change _ + L * ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 + _ ≤ _
  linarith

/-- A nonzero nonpositive smooth direction pays an explicit minimum support measure. -/
theorem ccmSmooth_nonpositive_explicit_supportFloor
    (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a)
    (hu : u.toCCMFormVector ≠ 0)
    (hQ : ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector ≤ 0) :
    ccmExplicitSupportThreshold a 0 < ccmSmoothSupportMeasure u := by
  by_contra hsmall
  have h := ccmSmooth_explicitSupport_coercivity a 0 u (le_of_not_gt hsmall)
  have hnorm : 0 < ‖u.toCCMFormVector‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  nlinarith

end RHTower

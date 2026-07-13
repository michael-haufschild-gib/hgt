import GaloisForLFunctions.RHTower.XiEndpointCompletedValueBound
import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import GaloisForLFunctions.RHTower.CCMPrimeGammaSourceEnergySpectrum

/-!
# Projective reflection source--temperature master spectrum

This module identifies one transverse Xi invariant in four exact charts:

* the projective distortion between reciprocal coordinates at critical-line-reflected zeros;
* the reflected Born-temperature mismatch;
* the horizontal support radius of the Xi divisor;
* the absolute-convergence abscissa shift of the fixed-window prime--Gamma negative source.

The same invariant controls the endpoint reflection-defect energy through a strictly increasing
completed-source budget.  At radius zero the budget is zero; at the full critical-strip radius
`1/2` it is exactly the unconditional endpoint source factor already obtained from the completed
value.  Thus this is a quantitative interpolation law, not merely a list of RH equivalences.
-/

open Complex

namespace RHTower

noncomputable section

def xiEndpointProjectiveReflectionDisplacement (q : XiZeroCopy) : ℝ :=
  ‖xiRawReciprocalCoordinate q -
      xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖ /
    (2 * ‖xiRawReciprocalCoordinate q‖ *
      ‖xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖)

def xiEndpointProjectiveReflectionDisplacementSq (q : XiZeroCopy) : ℝ :=
  ‖xiRawReciprocalCoordinate q -
      xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖ ^ 2 /
    (4 * ‖xiRawReciprocalCoordinate q‖ ^ 2 *
      ‖xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖ ^ 2)

theorem xiEndpointProjectiveReflectionDisplacement_sq (q : XiZeroCopy) :
    xiEndpointProjectiveReflectionDisplacementSq q =
      ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
  rw [xiEndpointProjectiveReflectionDisplacementSq,
    endpoint_defect_term_eq]
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [xiRawReciprocalCoordinate]
  have hline : ((xiZeroCopyLineConjEquiv q).1 : ℂ) =
      1 - (starRingEnd ℂ) (q.1 : ℂ) := rfl
  rw [hline]
  rw [Complex.normSq_inv, Complex.normSq_inv]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im,
    sub_neg_eq_add, zero_add]
  have him : (q.1 : ℂ).im ≠ 0 := xi_divisor_support_im_ne_zero q.1
  have hA : (q.1 : ℂ).re ^ 2 + (q.1 : ℂ).im ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero him]
  have hB : (1 - (q.1 : ℂ).re) ^ 2 + (q.1 : ℂ).im ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero him]
  field_simp [hA, hB]
  ring

theorem xiEndpointProjectiveReflectionDisplacement_eq_abs (q : XiZeroCopy) :
    xiEndpointProjectiveReflectionDisplacement q =
      |(q.1 : ℂ).re - 1 / 2| := by
  have hrho : (q.1 : ℂ) ≠ 0 := by
    have hs := xi_divisor_support_re_mem_open_unit q.1
    intro h
    rw [h] at hs
    norm_num at hs
  have hdagger : ((xiZeroCopyLineConjEquiv q).1 : ℂ) ≠ 0 := by
    have hs := xi_divisor_support_re_mem_open_unit (xiZeroCopyLineConjEquiv q).1
    intro h
    rw [h] at hs
    norm_num at hs
  have hnr : 0 < ‖xiRawReciprocalCoordinate q‖ := by
    rw [norm_pos_iff]
    exact inv_ne_zero hrho
  have hnd : 0 < ‖xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖ := by
    rw [norm_pos_iff]
    exact inv_ne_zero hdagger
  have hden : 0 < 2 * ‖xiRawReciprocalCoordinate q‖ *
      ‖xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖ := by positivity
  have hsqdef : xiEndpointProjectiveReflectionDisplacement q ^ 2 =
      xiEndpointProjectiveReflectionDisplacementSq q := by
    rw [xiEndpointProjectiveReflectionDisplacement,
      xiEndpointProjectiveReflectionDisplacementSq, div_pow]
    field_simp [ne_of_gt hnr, ne_of_gt hnd]
    ring
  have hsq : xiEndpointProjectiveReflectionDisplacement q ^ 2 =
      ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    rw [hsqdef, xiEndpointProjectiveReflectionDisplacement_sq]
  have hnonneg : 0 ≤ xiEndpointProjectiveReflectionDisplacement q := by
    exact div_nonneg (norm_nonneg _) hden.le
  have habssq : |(q.1 : ℂ).re - 1 / 2| ^ 2 =
      ((q.1 : ℂ).re - 1 / 2) ^ 2 := sq_abs _
  nlinarith [abs_nonneg ((q.1 : ℂ).re - 1 / 2)]

theorem bornBeta_lineConj_mismatch (q : XiZeroCopy) :
    |bornBeta (q.1 : ℂ) - bornBeta ((xiZeroCopyLineConjEquiv q).1 : ℂ)| =
      4 * |(q.1 : ℂ).re - 1 / 2| := by
  change |2 * (q.1 : ℂ).re - 2 * (1 - (q.1 : ℂ).re)| = _
  rw [show 2 * (q.1 : ℂ).re - 2 * (1 - (q.1 : ℂ).re) =
    4 * ((q.1 : ℂ).re - 1 / 2) by ring]
  rw [abs_mul]
  norm_num

def xiBornReflectionDisplacement (q : XiZeroCopy) : ℝ :=
  |bornBeta (q.1 : ℂ) - bornBeta ((xiZeroCopyLineConjEquiv q).1 : ℂ)| / 4

theorem xiBornReflectionDisplacement_eq_abs (q : XiZeroCopy) :
    xiBornReflectionDisplacement q = |(q.1 : ℂ).re - 1 / 2| := by
  rw [xiBornReflectionDisplacement, bornBeta_lineConj_mismatch]
  ring

theorem xiProjective_eq_bornReflectionDisplacement (q : XiZeroCopy) :
    xiEndpointProjectiveReflectionDisplacement q =
      xiBornReflectionDisplacement q := by
  rw [xiEndpointProjectiveReflectionDisplacement_eq_abs,
    xiBornReflectionDisplacement_eq_abs]

theorem xiRight_projectiveReflectionDisplacement_eq_centered
    (q : XiRightZeroCopy) :
    xiEndpointProjectiveReflectionDisplacement q.1 =
      (xiRightCenteredZero q).re := by
  have hpos : 0 < (q.1.1 : ℂ).re - 1 / 2 := by
    simpa [xiRightCenteredZero, I_mul_xiSpectralPoint] using q.2
  rw [xiEndpointProjectiveReflectionDisplacement_eq_abs,
    abs_of_pos hpos, xiRightCenteredZero, I_mul_xiSpectralPoint]
  simp only [Complex.sub_re]
  norm_num

def xiProjectiveReflectionRadius : ℝ :=
  sSup (Set.range (fun q : XiRightZeroCopy =>
    xiEndpointProjectiveReflectionDisplacement q.1))

def xiBornReflectionRadius : ℝ :=
  sSup (Set.range (fun q : XiRightZeroCopy =>
    xiBornReflectionDisplacement q.1))

/-- Completed endpoint-energy budget at transverse projective radius `alpha`. -/
def xiProjectiveEndpointBudget (alpha : ℝ) : ℝ :=
  (4 * alpha ^ 2 /
    (1 / xiEndpointCompletedCurvature - 3 / 4 - alpha ^ 2)) *
    xiEndpointCompletedCurvature

theorem xiProjectiveReflectionRadius_eq_transverseSup :
    xiProjectiveReflectionRadius = xiRightTransverseSup := by
  have hset : Set.range (fun q : XiRightZeroCopy =>
      xiEndpointProjectiveReflectionDisplacement q.1) =
      xiRightTransverseSet := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q, (xiRight_projectiveReflectionDisplacement_eq_centered q).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, xiRight_projectiveReflectionDisplacement_eq_centered q⟩
  rw [xiProjectiveReflectionRadius, xiRightTransverseSup, hset]

theorem xiBornReflectionRadius_eq_projectiveReflectionRadius :
    xiBornReflectionRadius = xiProjectiveReflectionRadius := by
  apply congrArg sSup
  ext x
  simp only [Set.mem_range]
  constructor <;> rintro ⟨q, rfl⟩ <;>
    exact ⟨q, by rw [xiProjective_eq_bornReflectionDisplacement]⟩

theorem xiProjectiveReflectionRadius_nonneg :
    0 ≤ xiProjectiveReflectionRadius := by
  rw [xiProjectiveReflectionRadius_eq_transverseSup]
  exact xiRightTransverseSup_nonneg

theorem xiZeroHalfPlaneBound_iff_projectiveReflectionRadius_le
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    XiZeroHalfPlaneBound alpha ↔ xiProjectiveReflectionRadius ≤ alpha := by
  rw [xiProjectiveReflectionRadius_eq_transverseSup]
  constructor
  · intro hzeros
    exact (xiRectangularWeilTailPowerLower_iff_transverseSup_le_global
      (L := 1) one_pos halpha).1
        ((xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le
          (L := 1) one_pos halpha).2 hzeros)
  · intro hsup
    exact (xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le
      (L := 1) one_pos halpha).1
        ((xiRectangularWeilTailPowerLower_iff_transverseSup_le_global
          (L := 1) one_pos halpha).2 hsup)

theorem xiRectangularPrimeGamma_abscissa_eq_projectiveRadius_of_not_rh
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (hnot : ¬ RiemannHypothesis) :
    LSeries.abscissaOfAbsConv
        (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) =
      ((1 + xiProjectiveReflectionRadius : ℝ) : EReal) := by
  rw [xiProjectiveReflectionRadius_eq_transverseSup]
  exact xiRectangularPrimeGammaTailNegativePart_abscissa_eq_transverseSup_of_not_rh
    hL hN hnot

theorem abs_xiZero_re_sub_half_le_of_halfPlaneBound
    {alpha : ℝ} (hzeros : XiZeroHalfPlaneBound alpha) (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ alpha := by
  have hqzero : xi (q.1 : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support q.1
  have hupper := hzeros (q.1 : ℂ) hqzero
  have hdagzero : xi ((xiZeroCopyLineConjEquiv q).1 : ℂ) = 0 :=
    xi_eq_zero_of_mem_divisor_support (xiZeroCopyLineConjEquiv q).1
  have hlower := hzeros ((xiZeroCopyLineConjEquiv q).1 : ℂ) hdagzero
  change 1 - (q.1 : ℂ).re ≤ 1 / 2 + alpha at hlower
  rw [abs_le]
  constructor <;> linarith

theorem endpoint_defect_term_le_projective_factor_cross
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2)
    (hzeros : XiZeroHalfPlaneBound alpha) (q : XiZeroCopy) :
    ‖xiRawReciprocalCoordinate q -
      xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q)‖ ^ 2 ≤
      (4 * alpha ^ 2 /
        (1 / xiEndpointCompletedCurvature - 3 / 4 - alpha ^ 2)) *
        (xiRawReciprocalCoordinate q *
          (starRingEnd ℂ)
            (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re := by
  rw [endpoint_defect_term_eq, endpoint_cross_term_re_eq]
  have hCpos : 0 < xiEndpointCompletedCurvature :=
    xiEndpointCompletedCurvature_pos
  have hCinv : 2 < 1 / xiEndpointCompletedCurvature := by
    rw [lt_div_iff₀ hCpos]
    nlinarith [xiEndpointCompletedCurvature_lt_one_half]
  have halphaSq : alpha ^ 2 ≤ 1 / 4 := by
    nlinarith [sq_nonneg alpha]
  have hbase : 0 <
      1 / xiEndpointCompletedCurvature - 3 / 4 - alpha ^ 2 := by
    nlinarith
  have hdelta := abs_xiZero_re_sub_half_le_of_halfPlaneBound hzeros q
  have hdeltaSq : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ alpha ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg ((q.1 : ℂ).re - 1 / 2)) hdelta 2
    simpa only [sq_abs] using this
  have hheight := xiZeroCopy_im_sq_ge_endpoint_source_inverse_gap q
  have hcrossBase :
      1 / xiEndpointCompletedCurvature - 3 / 4 - alpha ^ 2 ≤
        (q.1 : ℂ).im ^ 2 + (q.1 : ℂ).re * (1 - (q.1 : ℂ).re) := by
    nlinarith [sq_nonneg ((q.1 : ℂ).re - 1 / 2)]
  have hnum : (1 - 2 * (q.1 : ℂ).re) ^ 2 ≤ 4 * alpha ^ 2 := by
    nlinarith
  have him : (q.1 : ℂ).im ≠ 0 := xi_divisor_support_im_ne_zero q.1
  have hApos : 0 < (q.1 : ℂ).re ^ 2 + (q.1 : ℂ).im ^ 2 := by
    nlinarith [sq_pos_of_ne_zero him]
  have hBpos : 0 < (1 - (q.1 : ℂ).re) ^ 2 + (q.1 : ℂ).im ^ 2 := by
    nlinarith [sq_pos_of_ne_zero him]
  have hdenpos : 0 <
      ((q.1 : ℂ).re ^ 2 + (q.1 : ℂ).im ^ 2) *
        ((1 - (q.1 : ℂ).re) ^ 2 + (q.1 : ℂ).im ^ 2) :=
    mul_pos hApos hBpos
  calc
    _ ≤ ((4 * alpha ^ 2 /
          (1 / xiEndpointCompletedCurvature - 3 / 4 - alpha ^ 2)) *
        ((q.1 : ℂ).im ^ 2 + (q.1 : ℂ).re * (1 - (q.1 : ℂ).re))) /
        (((q.1 : ℂ).re ^ 2 + (q.1 : ℂ).im ^ 2) *
          ((1 - (q.1 : ℂ).re) ^ 2 + (q.1 : ℂ).im ^ 2)) := by
      rw [div_le_div_iff_of_pos_right hdenpos]
      rw [div_mul_eq_mul_div, le_div_iff₀ hbase]
      have hnumNonneg : 0 ≤ (1 - 2 * (q.1 : ℂ).re) ^ 2 := sq_nonneg _
      have halphaMulNonneg : 0 ≤ 4 * alpha ^ 2 := by positivity
      nlinarith
    _ = _ := by ring

theorem xiEndpointDefectEnergy_le_of_halfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2)
    (hzeros : XiZeroHalfPlaneBound alpha) :
    xiEndpointReflectionDefectEnergy ≤ xiProjectiveEndpointBudget alpha := by
  rw [xiProjectiveEndpointBudget]
  let K : ℝ := 4 * alpha ^ 2 /
    (1 / xiEndpointCompletedCurvature - 3 / 4 - alpha ^ 2)
  have hR : Summable (fun q : XiZeroCopy =>
      (xiRawReciprocalCoordinate q *
        (starRingEnd ℂ)
          (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re) := by
    exact Summable.of_norm_bounded summable_xiEndpointCrossTerm.norm (fun q => by
      rw [Real.norm_eq_abs]
      exact abs_re_le_norm _)
  have hscaled := hR.mul_left K
  have hsumle := summable_xiEndpointReflectionDefectEnergy.tsum_le_tsum
    (fun q => endpoint_defect_term_le_projective_factor_cross
      halpha halphaHalf hzeros q) hscaled
  have hcross :
      (∑' q : XiZeroCopy,
        (xiRawReciprocalCoordinate q *
          (starRingEnd ℂ)
            (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re) =
        xiEndpointCompletedCurvature := by
    rw [← Complex.re_tsum summable_xiEndpointCrossTerm,
      ← xiEndpointCompletedCurvature_eq_cross_re]
  rw [xiEndpointReflectionDefectEnergy]
  calc
    _ ≤ ∑' q : XiZeroCopy, K *
        (xiRawReciprocalCoordinate q *
          (starRingEnd ℂ)
            (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re := hsumle
    _ = K * ∑' q : XiZeroCopy,
        (xiRawReciprocalCoordinate q *
          (starRingEnd ℂ)
            (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re :=
      tsum_mul_left
    _ = _ := by rw [hcross]

theorem xiEndpointDefectEnergy_le_of_projectiveReflectionRadius
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2)
    (hradius : xiProjectiveReflectionRadius ≤ alpha) :
    xiEndpointReflectionDefectEnergy ≤ xiProjectiveEndpointBudget alpha := by
  exact xiEndpointDefectEnergy_le_of_halfPlaneBound halpha halphaHalf
    ((xiZeroHalfPlaneBound_iff_projectiveReflectionRadius_le halpha).2 hradius)

theorem primeGamma_abscissa_le_iff_projectiveReflectionRadius_le
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) ≤
          ((1 + alpha : ℝ) : EReal) ↔
      xiProjectiveReflectionRadius ≤ alpha := by
  by_cases hRH : RiemannHypothesis
  · have habot :=
      xiRectangularPrimeGammaTailNegativePart_abscissa_eq_bot_of_rh hL hN hRH
    have hzeros : XiZeroHalfPlaneBound alpha := by
      intro rho hzero
      have hre := xi_zero_re_eq_half_of_RH hRH hzero
      linarith
    have hradius :=
      (xiZeroHalfPlaneBound_iff_projectiveReflectionRadius_le halpha).1 hzeros
    rw [habot]
    exact iff_of_true bot_le hradius
  · have hae :=
      xiRectangularPrimeGamma_abscissa_eq_projectiveRadius_of_not_rh hL hN hRH
    rw [hae]
    constructor
    · intro h
      have hreal : 1 + xiProjectiveReflectionRadius ≤ 1 + alpha := by
        exact_mod_cast h
      linarith
    · intro h
      exact_mod_cast (show 1 + xiProjectiveReflectionRadius ≤ 1 + alpha by linarith)

/-- **Projective source--temperature master spectrum.**  At every transverse scale in the
critical strip, the fixed-window prime--Gamma abscissa, the reciprocal-orbit projective radius,
the reflected Born-temperature radius, and the Xi half-plane bound are the same exact datum.
That datum also controls the completed endpoint reflection energy quadratically. -/
theorem xiProjectiveSourceTemperatureMasterSpectrum
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha)
    (halphaHalf : alpha ≤ 1 / 2) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    let sourceBound :=
      LSeries.abscissaOfAbsConv
          (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) ≤
        ((1 + alpha : ℝ) : EReal)
    let projectiveBound := xiProjectiveReflectionRadius ≤ alpha
    let thermalBound := xiBornReflectionRadius ≤ alpha
    let divisorBound := XiZeroHalfPlaneBound alpha
    (sourceBound ↔ projectiveBound) ∧
    (projectiveBound ↔ thermalBound) ∧
    (projectiveBound ↔ divisorBound) ∧
    (sourceBound →
      xiEndpointReflectionDefectEnergy ≤ xiProjectiveEndpointBudget alpha) := by
  dsimp only
  refine ⟨primeGamma_abscissa_le_iff_projectiveReflectionRadius_le
      hL halpha hN, ?_, ?_, ?_⟩
  · rw [xiBornReflectionRadius_eq_projectiveReflectionRadius]
  · exact (xiZeroHalfPlaneBound_iff_projectiveReflectionRadius_le halpha).symm
  · intro hsource
    exact xiEndpointDefectEnergy_le_of_projectiveReflectionRadius halpha halphaHalf
      ((primeGamma_abscissa_le_iff_projectiveReflectionRadius_le
        hL halpha hN).1 hsource)

theorem xiProjectiveEndpointBudget_zero :
    xiProjectiveEndpointBudget 0 = 0 := by
  simp [xiProjectiveEndpointBudget]

theorem xiProjectiveEndpointBudget_half :
    xiProjectiveEndpointBudget (1 / 2) =
      (xiEndpointCompletedCurvature / (1 - xiEndpointCompletedCurvature)) *
        xiEndpointCompletedCurvature := by
  rw [xiProjectiveEndpointBudget]
  have hC : xiEndpointCompletedCurvature ≠ 0 :=
    ne_of_gt xiEndpointCompletedCurvature_pos
  have hC1 : 1 - xiEndpointCompletedCurvature ≠ 0 := by
    nlinarith [xiEndpointCompletedCurvature_lt_one_half]
  field_simp [hC, hC1]
  ring

theorem xiProjectiveEndpointBudget_strictMonoOn :
    StrictMonoOn xiProjectiveEndpointBudget (Set.Icc 0 (1 / 2)) := by
  intro a ha b hb hab
  have hCpos := xiEndpointCompletedCurvature_pos
  have hCinv : 2 < 1 / xiEndpointCompletedCurvature := by
    rw [lt_div_iff₀ hCpos]
    nlinarith [xiEndpointCompletedCurvature_lt_one_half]
  have haSq : a ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg a]
  have hbSq : b ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg b]
  have hDa : 0 < 1 / xiEndpointCompletedCurvature - 3 / 4 - a ^ 2 := by
    nlinarith
  have hDb : 0 < 1 / xiEndpointCompletedCurvature - 3 / 4 - b ^ 2 := by
    nlinarith
  have habSq : a ^ 2 < b ^ 2 := by nlinarith
  rw [xiProjectiveEndpointBudget, xiProjectiveEndpointBudget]
  apply mul_lt_mul_of_pos_right _ hCpos
  rw [div_lt_div_iff₀ hDa hDb]
  nlinarith [sq_nonneg a, sq_nonneg b]

theorem xiProjectiveReflectionRadius_eq_zero_iff_rh :
    xiProjectiveReflectionRadius = 0 ↔ RiemannHypothesis := by
  obtain ⟨N, hN⟩ := exists_xiRectangularAdmissibleCutoff (1 : ℝ)
  constructor
  · intro hzero
    apply (riemannHypothesis_iff_primeGammaTailNegativePart_abscissa_le_one
      (L := 1) one_pos hN).2
    have hradius : xiProjectiveReflectionRadius ≤ 0 := hzero.le
    have hsource :=
      (primeGamma_abscissa_le_iff_projectiveReflectionRadius_le
        (L := 1) (alpha := 0) one_pos (by norm_num) hN).2 hradius
    simpa using hsource
  · intro hRH
    have hsource :=
      (riemannHypothesis_iff_primeGammaTailNegativePart_abscissa_le_one
        (L := 1) one_pos hN).1 hRH
    have hradius :=
      (primeGamma_abscissa_le_iff_projectiveReflectionRadius_le
        (L := 1) (alpha := 0) one_pos (by norm_num) hN).1 (by simpa using hsource)
    exact le_antisymm hradius xiProjectiveReflectionRadius_nonneg

/-- The zero fiber of the master spectrum: projective reflection, Born-temperature reflection,
endpoint energy, and RH vanish together. -/
theorem xiProjectiveBornEndpoint_zero_iff_rh :
    (xiProjectiveReflectionRadius = 0 ↔ xiBornReflectionRadius = 0) ∧
    (xiProjectiveReflectionRadius = 0 ↔ xiEndpointReflectionDefectEnergy = 0) ∧
    (xiProjectiveReflectionRadius = 0 ↔ RiemannHypothesis) := by
  refine ⟨?_, ?_, xiProjectiveReflectionRadius_eq_zero_iff_rh⟩
  · rw [xiBornReflectionRadius_eq_projectiveReflectionRadius]
  · rw [xiProjectiveReflectionRadius_eq_zero_iff_rh,
      xiEndpointReflectionDefectEnergy_eq_zero_iff_rh]

end

end RHTower

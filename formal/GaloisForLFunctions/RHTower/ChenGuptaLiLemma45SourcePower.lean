/-
# Chen--Gupta--Li Lemma 4.5 source-scale power saving

Turns CGL's rational power-spacing certificate into arbitrary closed
power savings for the exact zero-frequency off-diagonal term.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45FibreZeroModeAggregate

noncomputable section

namespace RHTower

/-- A same-character spacing scale with a positive rational exponent. -/
structure CGLPowerSeparatedFibrePacket {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) where
  base : ℝ
  base_one : 1 ≤ base
  numerator : ℕ
  numerator_pos : 0 < numerator
  denominator : ℕ
  denominator_pos : 0 < denominator
  spacing_power : base ^ numerator ≤ P.spacing ^ denominator

theorem cglPowerSeparatedFibrePacket_power_le
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R}
    (S : CGLPowerSeparatedFibrePacket P) (m : ℕ) :
    S.base ^ (S.numerator * m) ≤ P.spacing ^ (S.denominator * m) := by
  have hpow := pow_le_pow_left₀ (pow_nonneg (le_trans zero_le_one S.base_one) S.numerator)
    S.spacing_power m
  simpa only [pow_mul] using hpow

theorem cglPowerSeparatedFibrePacket_reciprocal_le
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R}
    (S : CGLPowerSeparatedFibrePacket P) (m : ℕ) :
    1 / P.spacing ^ (S.denominator * m) ≤
      1 / S.base ^ (S.numerator * m) := by
  apply one_div_le_one_div_of_le
  · exact pow_pos (lt_of_lt_of_le zero_lt_one S.base_one) _
  · exact cglPowerSeparatedFibrePacket_power_le S m

/-- Source-scale bounds needed to make the CGL Lemma 4.5 finite zero-mode
estimate polynomial in one base parameter. -/
structure CGLLemma45SourceScale {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (N : CGLPositiveLength) where
  separation : CGLPowerSeparatedFibrePacket P
  fourierScale_le :
    cglAffineFourierScale N (cglLemma45FibreModulus q) ≤ separation.base
  totient_le : ((cglLemma45FibreModulus q).value.totient : ℝ) ≤ separation.base
  rowCountExponent : ℕ
  rowCount_le : (R : ℝ) ≤ separation.base ^ rowCountExponent

theorem cglLemma45FibreZeroModeRowBound_le_scale
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45SourceScale P N) (w : CGLRealSmoothBump) (n : ℕ) :
    cglLemma45FibreZeroModeRowBound P w N n ≤
      S.separation.base ^ 6 *
        (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n / P.spacing ^ n) *
          cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
            cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 := by
  let Q := cglLemma45FibreModulus q
  let C : ℝ := cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n / P.spacing ^ n
  let D : ℝ := cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0
  have hbase : 0 ≤ S.separation.base := le_trans zero_le_one S.separation.base_one
  have hphi : ((Q.value.totient : ℝ) ^ 3) ≤ S.separation.base ^ 3 :=
    pow_le_pow_left₀ (by positivity) S.totient_le _
  have hC : 0 ≤ C := by
    unfold C
    exact div_nonneg (cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump n)
      (pow_nonneg P.spacing_pos.le _)
  have hD : 0 ≤ D := cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump 0
  have hscale : 0 ≤ cglAffineFourierScale N Q := (cglAffineFourierScale_pos N Q).le
  have hscale_le : cglAffineFourierScale N Q ≤ S.separation.base := S.fourierScale_le
  change (Q.value.totient : ℝ) ^ 3 *
      ((cglAffineFourierScale N Q * C) *
        (cglAffineFourierScale N Q * D) *
          (cglAffineFourierScale N Q * D)) ≤ _
  calc
    _ ≤ S.separation.base ^ 3 *
        ((S.separation.base * C) * (S.separation.base * D) *
          (S.separation.base * D)) := by gcongr
    _ = _ := by ring

theorem norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_scale
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45SourceScale P N) (w : CGLRealSmoothBump) (n : ℕ) :
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) 0‖ ≤
      S.separation.base ^ (3 * S.rowCountExponent + 6) *
        (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n / P.spacing ^ n) *
          cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
            cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 := by
  have hR3 : (R : ℝ) ^ 3 ≤ S.separation.base ^ (3 * S.rowCountExponent) := by
    calc
      (R : ℝ) ^ 3 ≤ (S.separation.base ^ S.rowCountExponent) ^ 3 :=
        pow_le_pow_left₀ (by positivity) S.rowCount_le _
      _ = S.separation.base ^ (3 * S.rowCountExponent) := by
        rw [← pow_mul, Nat.mul_comm]
  have hrow := cglLemma45FibreZeroModeRowBound_le_scale S w n
  calc
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) 0‖ ≤
        (R : ℝ) ^ 3 * cglLemma45FibreZeroModeRowBound P w N n :=
      norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_cubicRowBudget P w N n
    _ ≤ S.separation.base ^ (3 * S.rowCountExponent) *
        (S.separation.base ^ 6 *
          (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n / P.spacing ^ n) *
            cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
              cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0) := by
      exact mul_le_mul hR3 hrow (cglLemma45FibreZeroModeRowBound_nonneg P w N n)
        (pow_nonneg (le_trans zero_le_one S.separation.base_one) _)
    _ = _ := by
      calc
        S.separation.base ^ (3 * S.rowCountExponent) *
            (S.separation.base ^ 6 *
              (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n / P.spacing ^ n) *
                cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
                  cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0) =
            (S.separation.base ^ (3 * S.rowCountExponent) * S.separation.base ^ 6) *
              (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n / P.spacing ^ n) *
                cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
                  cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 := by ring
        _ = _ := by rw [← pow_add]

theorem norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_scale_reciprocal
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45SourceScale P N) (w : CGLRealSmoothBump) (m : ℕ) :
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) 0‖ ≤
      S.separation.base ^ (3 * S.rowCountExponent + 6) *
        (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
          (S.separation.denominator * m) /
          S.separation.base ^ (S.separation.numerator * m)) *
          cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
            cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 := by
  have hrec := cglPowerSeparatedFibrePacket_reciprocal_le S.separation m
  have hrec' : (P.spacing ^ (S.separation.denominator * m))⁻¹ ≤
      (S.separation.base ^ (S.separation.numerator * m))⁻¹ := by
    simpa only [one_div] using hrec
  have hratio :
      cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
          (S.separation.denominator * m) /
          P.spacing ^ (S.separation.denominator * m) ≤
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
          (S.separation.denominator * m) /
          S.separation.base ^ (S.separation.numerator * m) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hrec'
      (cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump _)
  have hbase : 0 ≤ S.separation.base := le_trans zero_le_one S.separation.base_one
  have hD : 0 ≤ cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 :=
    cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump 0
  calc
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) 0‖ ≤
        S.separation.base ^ (3 * S.rowCountExponent + 6) *
          (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
            (S.separation.denominator * m) /
            P.spacing ^ (S.separation.denominator * m)) *
            cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
              cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 :=
      norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_scale S w
        (S.separation.denominator * m)
    _ ≤ _ := by gcongr

theorem cglBasePowerRatio_le_reciprocal
    (base : ℝ) (hbase : 1 ≤ base) (E K A : ℕ) (hEA : E + K ≤ A) :
    base ^ E / base ^ A ≤ 1 / base ^ K := by
  have hpos : 0 < base := lt_of_lt_of_le zero_lt_one hbase
  rw [div_le_iff₀ (pow_pos hpos A)]
  calc
    base ^ E ≤ base ^ A / base ^ K := by
      rw [le_div_iff₀ (pow_pos hpos K)]
      rw [← pow_add]
      exact pow_le_pow_right₀ hbase hEA
    _ = 1 / base ^ K * base ^ A := by ring

/-- A sufficient finite Fourier-decay order for one source power target. -/
structure CGLLemma45SourceDecayOrder
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45SourceScale P N) where
  targetExponent : ℕ
  multiplier : ℕ
  dominates : 3 * S.rowCountExponent + 6 + targetExponent ≤
    S.separation.numerator * multiplier

def cglLemma45CanonicalSourceDecayOrder
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45SourceScale P N) (targetExponent : ℕ) :
    CGLLemma45SourceDecayOrder S where
  targetExponent := targetExponent
  multiplier := 3 * S.rowCountExponent + 6 + targetExponent
  dominates := by
    calc
      3 * S.rowCountExponent + 6 + targetExponent =
          1 * (3 * S.rowCountExponent + 6 + targetExponent) := by ring
      _ ≤ S.separation.numerator * (3 * S.rowCountExponent + 6 + targetExponent) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr S.separation.numerator_pos)

theorem norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_sourcePower
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45SourceScale P N) (w : CGLRealSmoothBump)
    (D : CGLLemma45SourceDecayOrder S) :
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) 0‖ ≤
      (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
        (S.separation.denominator * D.multiplier) *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0) /
          S.separation.base ^ D.targetExponent := by
  have hratio := cglBasePowerRatio_le_reciprocal S.separation.base
    S.separation.base_one (3 * S.rowCountExponent + 6) D.targetExponent
    (S.separation.numerator * D.multiplier) D.dominates
  have hconstant : 0 ≤
      cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
        (S.separation.denominator * D.multiplier) *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 := by
    repeat' apply mul_nonneg
    · exact cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump _
    · exact cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump 0
    · exact cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump 0
  calc
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) 0‖ ≤
        S.separation.base ^ (3 * S.rowCountExponent + 6) *
          (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
            (S.separation.denominator * D.multiplier) /
            S.separation.base ^ (S.separation.numerator * D.multiplier)) *
            cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
              cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 :=
      norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_scale_reciprocal S w D.multiplier
    _ = (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
          (S.separation.denominator * D.multiplier) *
          cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
          cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0) *
          (S.separation.base ^ (3 * S.rowCountExponent + 6) /
            S.separation.base ^ (S.separation.numerator * D.multiplier)) := by ring
    _ ≤ (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
          (S.separation.denominator * D.multiplier) *
          cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
          cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0) *
          (1 / S.separation.base ^ D.targetExponent) := by
      exact mul_le_mul_of_nonneg_left hratio hconstant
    _ = _ := by ring

/-- CGL's zero-frequency off-diagonal term has every requested source power
after choosing its closed canonical Fourier-decay order. -/
theorem norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_any_sourcePower
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45SourceScale P N) (w : CGLRealSmoothBump)
    (targetExponent : ℕ) :
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) 0‖ ≤
      (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
        (S.separation.denominator * (3 * S.rowCountExponent + 6 + targetExponent)) *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0) /
          S.separation.base ^ targetExponent := by
  simpa [cglLemma45CanonicalSourceDecayOrder] using
    norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_sourcePower S w
      (cglLemma45CanonicalSourceDecayOrder S targetExponent)

end RHTower

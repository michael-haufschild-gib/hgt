import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeRectangularPrimitiveCurrent
import GaloisForLFunctions.RHTower.CCMFirstClockVolterra
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularGammaPolarSourceLaw
import GaloisForLFunctions.RHTower.CCMGuinandWeilXiScrewGreenConnection
import GaloisForLFunctions.RHTower.SuzukiScrewGrowthBound
import GaloisForLFunctions.RHTower.SuzukiScrewSmoothTestCriterion
import GaloisForLFunctions.HTGeometry.OscBudgetSymbolBound

/-!
# CCM-FU central rectangular affine weld

This module identifies every literal third-grade FU slice with an affine-renormalized central
prime--polar rectangle, transports that rectangle into Suzuki's Xi-screw chart, and proves that
the entire diagonal Gamma/Lerch chart defect is uniformly bounded cofinally. Consequently the
RH-bearing triangular prime--polar window is exactly, up to a bounded term, one positive marked
mixture of literal Xi-screw codiagonals.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

private theorem centralPolarTriangleIntegral
    (t : ℝ) :
    (∫ h in (0 : ℝ)..t, (t - h) * (2 * Real.cosh (h / 2))) =
      8 * (Real.cosh (t / 2) - 1) := by
  let P : ℝ → ℝ := fun h =>
    4 * ((t - h) * Real.sinh (h / 2)) + 8 * Real.cosh (h / 2)
  have hP : ∀ h ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt P ((t - h) * (2 * Real.cosh (h / 2))) h := by
    intro h _hh
    have hlin : HasDerivAt (fun x : ℝ => t - x) (-1) h := by
      simpa using (hasDerivAt_id h).const_sub t
    have hsinh : HasDerivAt (fun x : ℝ => Real.sinh (x / 2))
        ((1 / 2 : ℝ) * Real.cosh (h / 2)) h := by
      apply ((Real.hasDerivAt_sinh (h / 2)).comp h
        ((hasDerivAt_id h).div_const 2)).congr_deriv
      ring
    have hcosh : HasDerivAt (fun x : ℝ => Real.cosh (x / 2))
        ((1 / 2 : ℝ) * Real.sinh (h / 2)) h := by
      apply ((Real.hasDerivAt_cosh (h / 2)).comp h
        ((hasDerivAt_id h).div_const 2)).congr_deriv
      ring
    have hraw := ((hlin.mul hsinh).const_mul 4).add (hcosh.const_mul 8)
    exact hraw.congr_deriv (by ring)
  have hInt : IntervalIntegrable
      (fun h : ℝ => (t - h) * (2 * Real.cosh (h / 2))) volume 0 t :=
    (by fun_prop : Continuous (fun h : ℝ =>
      (t - h) * (2 * Real.cosh (h / 2)))) |>.intervalIntegrable 0 t
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hP hInt]
  dsimp only [P]
  norm_num
  ring

private theorem centralPolarTriangleSetIntegral
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ h in Set.Ioc (0 : ℝ) t,
        (((t - h) * (2 * Real.cosh (h / 2)) : ℝ) : ℂ)) =
      ((8 * (Real.cosh (t / 2) - 1) : ℝ) : ℂ) := by
  rw [← intervalIntegral.integral_of_le ht]
  rw [intervalIntegral.integral_ofReal]
  norm_cast
  exact centralPolarTriangleIntegral t

private theorem centralRectangularPrimePolarSource_eq_stieltjesPairing
    {t : ℝ} (ht : 0 ≤ t) :
    rectangularPrimePolarSourceCoefficient (t / 2) (t / 2) =
      2 * (criticalMellinStieltjesPairing (t / 2)
        (fun h : ℝ => ((t - h : ℝ) : ℂ))).re := by
  have hprime := rectangularPrimeAutocorrelationSum_central_eq_commonTriangle
    (L := t) ht (le_refl t)
  have hprime' :
      rectangularPrimeAutocorrelationSum (t / 2) (t / 2) =
        ∑ k ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
          criticalMellinAtomWeight k * (t - Real.log k) := by
    rw [hprime]
    apply Finset.sum_congr rfl
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by
      exact_mod_cast (show 0 < k by omega)
    have hkexp : (k : ℝ) ≤ Real.exp t :=
      (Nat.le_floor_iff (Real.exp_pos t).le).mp (Finset.mem_Icc.mp hk).2
    have hlogt : Real.log k ≤ t := (Real.log_le_iff_le_exp hkpos).mpr hkexp
    rw [max_eq_right (sub_nonneg.mpr hlogt), criticalMellinAtomWeight_eq_div_sqrt]
  have hpolar := centralPolarTriangleSetIntegral ht
  rw [rectangularPrimePolarSourceCoefficient, hprime',
    rectangularEvenPolarFeature_central_sq ht,
    criticalMellinStieltjesPairing]
  have hpolar' :
      (∫ h in Set.Ioc (0 : ℝ) (2 * (t / 2)),
        ((t - h : ℝ) : ℂ) * (2 * Real.cosh (h / 2) : ℂ)) =
        ((8 * (Real.cosh (t / 2) - 1) : ℝ) : ℂ) := by
    rw [show 2 * (t / 2) = t by ring]
    convert hpolar using 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with h
    push_cast
    ring
  rw [hpolar']
  rw [show 2 * (t / 2) = t by ring]
  have hsum :
      (∑ x ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
        (criticalMellinAtomWeight x : ℂ) * ((t - Real.log x : ℝ) : ℂ)).re =
      ∑ x ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
        criticalMellinAtomWeight x * (t - Real.log x) := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Complex.ofReal_mul]
    exact Complex.ofReal_re _
  rw [Complex.sub_re, Complex.ofReal_re, hsum]
  ring

/-- Central two-edge prime--polar source is twice the first primitive of the completed
critical-Mellin error. This identity is valid through every prime-entry kink. -/
theorem centralRectangularPrimePolarSource_eq_completedErrorPrimitive
    {t : ℝ} (ht : 0 ≤ t) :
    rectangularPrimePolarSourceCoefficient (t / 2) (t / 2) =
      2 * ∫ h in (0 : ℝ)..t, criticalMellinCompletedError h := by
  have hibp := criticalMellinStieltjesPairing_integrationByParts
    (a := t / 2) (by positivity : 0 ≤ t / 2)
    (F := fun h : ℝ => ((t - h : ℝ) : ℂ))
    (F' := fun _h : ℝ => (-1 : ℂ))
    (fun x hx => by
      have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
        simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
      simpa only [Complex.ofReal_sub] using hid.const_sub (t : ℂ))
    (continuous_const.intervalIntegrable 0 (2 * (t / 2)))
    (by norm_num; ring)
  rw [show 2 * (t / 2) = t by ring] at hibp
  rw [centralRectangularPrimePolarSource_eq_stieltjesPairing ht, hibp]
  have hreal :
      (∫ h in Set.Ioc (0 : ℝ) t,
        (criticalMellinCompletedError h : ℂ) * (-1 : ℂ)).re =
        -(∫ h in (0 : ℝ)..t, criticalMellinCompletedError h) := by
    rw [show (fun h : ℝ =>
        (criticalMellinCompletedError h : ℂ) * (-1 : ℂ)) =
        fun h : ℝ => ((-criticalMellinCompletedError h : ℝ) : ℂ) by
      funext h
      push_cast
      ring]
    have hcast :
        (∫ h in Set.Ioc (0 : ℝ) t,
          ((-criticalMellinCompletedError h : ℝ) : ℂ)) =
        ((∫ h in Set.Ioc (0 : ℝ) t,
          -criticalMellinCompletedError h : ℝ) : ℂ) := by
      exact integral_ofReal
    rw [hcast, Complex.ofReal_re,
      ← intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_neg]
  rw [Complex.neg_re, hreal]
  ring

/-- Central prime--polar source is the Gamma-renormalized real Xi screw coordinate. This is the
exact source/spectral dictionary at variable central aperture. -/
theorem centralRectangularPrimePolarSource_eq_xiScrew_sub_gamma
    {t : ℝ} (ht : 0 ≤ t) :
    rectangularPrimePolarSourceCoefficient (t / 2) (t / 2) =
      2 * (xiScrewDivisor t).re -
        rectangularGammaPolarCorrection (t / 2) (t / 2) := by
  have hsource := xiWeilPolarization_rectangular_eq_primePolarSource_add_gammaCorrection
    (L := t / 2) (a := t / 2) (by positivity : 0 ≤ t / 2) (le_refl (t / 2))
  rw [xiWeilPolarization_central_rectangular_eq_two_mul_screw] at hsource
  have hre := congrArg Complex.re hsource
  norm_num at hre
  linarith

/-- Affine-renormalized central source increment. Its subtracted jet is the literal completed
prime--polar coefficient at the fixed lower wall. -/
def ccmFUCentralRectangularAffineRemainder (b t : ℝ) : ℝ :=
  rectangularPrimePolarSourceCoefficient (t / 2) (t / 2) -
    rectangularPrimePolarSourceCoefficient (b / 2) (b / 2) -
      2 * (t - b) * criticalMellinCompletedError b

/-- The FU affine remainder in the actual Xi-screw/Gamma chart. -/
def ccmFUCentralScrewGammaAffineRemainder (b t : ℝ) : ℝ :=
  (2 * (xiScrewDivisor t).re -
      rectangularGammaPolarCorrection (t / 2) (t / 2)) -
    (2 * (xiScrewDivisor b).re -
      rectangularGammaPolarCorrection (b / 2) (b / 2)) -
      2 * (t - b) * criticalMellinCompletedError b

/-- Source and Xi-screw/Gamma affine remainders agree without a limit or RH premise. -/
theorem ccmFUCentralRectangularAffineRemainder_eq_screwGamma
    {b t : ℝ} (hb : 0 ≤ b) (hbt : b ≤ t) :
    ccmFUCentralRectangularAffineRemainder b t =
      ccmFUCentralScrewGammaAffineRemainder b t := by
  rw [ccmFUCentralRectangularAffineRemainder,
    ccmFUCentralScrewGammaAffineRemainder,
    centralRectangularPrimePolarSource_eq_xiScrew_sub_gamma (hb.trans hbt),
    centralRectangularPrimePolarSource_eq_xiScrew_sub_gamma hb]

/-- **FU--Suzuki central weld.** Every marked FU rectangular slice is exactly negative one half
of the affine-renormalized central two-edge prime--polar source. Fixed-wall memory is the true
zero-frequency completed source coefficient; no positive/negative region is separated. -/
theorem ccmThirdGradeCesaroRectangularPrimePolarSlice_eq_neg_half_centralAffineRemainder
    {b H t : ℝ} (hb : 0 < b) (hbt : b ≤ t) (htH : t ≤ H) :
    ccmThirdGradeCesaroRectangularPrimePolarSlice b H t =
      -(1 / 2 : ℝ) * ccmFUCentralRectangularAffineRemainder b t := by
  rw [ccmThirdGradeCesaroRectangularPrimePolarSlice_eq_completedErrorPrimitive
    hb hbt htH]
  rw [ccmFUCentralRectangularAffineRemainder,
    centralRectangularPrimePolarSource_eq_completedErrorPrimitive (hb.le.trans hbt),
    centralRectangularPrimePolarSource_eq_completedErrorPrimitive hb.le]
  have hE := intervalIntegrable_criticalMellinCompletedError_on_Icc hbt
  rw [intervalIntegral.integral_sub
    (continuous_const.intervalIntegrable b t) hE,
    intervalIntegral.integral_const]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_criticalMellinCompletedError_on_Icc hb.le)
    hE
  have hdiff :
      (∫ h in (0 : ℝ)..t, criticalMellinCompletedError h) -
          (∫ h in (0 : ℝ)..b, criticalMellinCompletedError h) =
        ∫ h in b..t, criticalMellinCompletedError h := by
    linarith
  rw [show (∫ h in (0 : ℝ)..t, criticalMellinCompletedError h) =
      (∫ h in (0 : ℝ)..b, criticalMellinCompletedError h) +
        ∫ h in b..t, criticalMellinCompletedError h by linarith]
  ring

/-- Positive marked mixture of affine-renormalized central rectangular sources. This is a
pre-scalar source family: all aperture slices remain coupled until the final integration. -/
def ccmFUCentralRectangularAffineMixture (b H : ℝ) : ℝ :=
  (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
    ccmFUCentralRectangularAffineRemainder b t) +
  (32 / H ^ 4) * ccmFUCentralRectangularAffineRemainder b H

/-- The literal marked FU prime--polar current is negative one half of the full positive marked
mixture of central affine remainders. This is an exact cross-aperture identity, not an atomwise
estimate or a positivity replacement. -/
theorem ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent_eq_neg_half_centralAffineMixture
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent b H =
      -(1 / 2 : ℝ) * ccmFUCentralRectangularAffineMixture b H := by
  rw [ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent_eq_fubini hb hbH]
  have hbulk :
      (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
        ccmThirdGradeCesaroRectangularPrimePolarSlice b H t) =
      -(1 / 2 : ℝ) *
        ∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
          ccmFUCentralRectangularAffineRemainder b t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hbH] at ht
    change ccmThirdGradeCesaroRectangularMixDensity H t *
        ccmThirdGradeCesaroRectangularPrimePolarSlice b H t =
      -(1 / 2 : ℝ) *
        (ccmThirdGradeCesaroRectangularMixDensity H t *
          ccmFUCentralRectangularAffineRemainder b t)
    rw [ccmThirdGradeCesaroRectangularPrimePolarSlice_eq_neg_half_centralAffineRemainder
      hb ht.1 ht.2]
    ring
  rw [hbulk,
    ccmThirdGradeCesaroRectangularPrimePolarSlice_eq_neg_half_centralAffineRemainder
      hb hbH (le_refl H)]
  unfold ccmFUCentralRectangularAffineMixture
  ring

/-- Source-faithful FU landing in the central rectangular chart. -/
theorem ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_neg_half_centralAffineMixture
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H =
      -(1 / 2 : ℝ) * ccmFUCentralRectangularAffineMixture b H := by
  rw [ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_markedRectangularCurrent
    hb hbH]
  exact
    ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent_eq_neg_half_centralAffineMixture
      hb hbH

/-- On the moving central diagonal, the Gamma--polar correction is exactly an affine term plus
the decaying Lerch remainder.  This is the variable-length law; fixed-length aperture bounds do
not imply it. -/
theorem rectangularGammaPolarCorrection_central_eq_screwLerch
    {t : ℝ} (ht : 0 < t) :
    rectangularGammaPolarCorrection (t / 2) (t / 2) =
      screwLinearCoeff * t + 2 * (screwLerchConst - screwLerchTail t) := by
  have hcancel :=
    normalizedRectangularBottomArchContribution_sub_two_mul_polar_sq
      (L := t / 2) (a := t / 2) (by positivity : 0 ≤ t / 2) (le_refl (t / 2))
  have hre := congrArg Complex.re hcancel
  norm_num only [Complex.sub_re, Complex.ofReal_re] at hre
  rw [normalizedRectangularBottomArchContribution_central_explicit ht,
    rectangularEvenPolarFeature_central_sq ht.le] at hre
  rw [screwLinearCoeff]
  linarith

/-- The residual central Gamma chart after subtracting its tangent at the fixed FU wall. -/
def ccmFUCentralGammaLerchAffineDefect (b t : ℝ) : ℝ :=
  screwLerchTail t - screwLerchTail b - (t - b) * screwLerchTail₁ b

/-- **FU--Xi-screw affine decomposition.** The central rectangular FU remainder is twice the
literal Xi-screw codiagonal plus twice an explicit Lerch Taylor defect.  Thus all arithmetic
prime--polar cancellation stays inside one unscalarized Xi-screw codiagonal; the chart-change
error is purely archimedean. -/
theorem ccmFUCentralRectangularAffineRemainder_eq_two_mul_xiScrewCodiagonal_add_lerchDefect
    {b t : ℝ} (hb : 0 < b) (hbt : b ≤ t) :
    ccmFUCentralRectangularAffineRemainder b t =
      2 * ccmGuinandWeilXiScrewCodiagonal b t +
        2 * ccmFUCentralGammaLerchAffineDefect b t := by
  rw [ccmFUCentralRectangularAffineRemainder,
    centralRectangularPrimePolarSource_eq_xiScrew_sub_gamma (hb.le.trans hbt),
    centralRectangularPrimePolarSource_eq_xiScrew_sub_gamma hb.le,
    rectangularGammaPolarCorrection_central_eq_screwLerch (hb.trans_le hbt),
    rectangularGammaPolarCorrection_central_eq_screwLerch hb,
    ccmGuinandWeilXiScrewCodiagonal,
    ccmGuinandWeilXiScrewRightSlope_eq_completedError_add_arch,
    suzukiPsi_eq_xiScrewDivisor_re (hb.le.trans hbt),
    suzukiPsi_eq_xiScrewDivisor_re hb.le]
  unfold ccmFUCentralGammaLerchAffineDefect
  ring

/-- The diagonal Gamma chart defect has at most linear growth from a fixed positive wall. -/
theorem abs_ccmFUCentralGammaLerchAffineDefect_le
    {b t : ℝ} (hb : 0 < b) (hbt : b ≤ t) :
    |ccmFUCentralGammaLerchAffineDefect b t| ≤
      2 * screwLerchConst + (t - b) * |screwLerchTail₁ b| := by
  have ht : 0 < t := hb.trans_le hbt
  have hbTail := abs_screwLerchTail_le_const hb
  have htTail := abs_screwLerchTail_le_const ht
  unfold ccmFUCentralGammaLerchAffineDefect
  calc
    |screwLerchTail t - screwLerchTail b -
        (t - b) * screwLerchTail₁ b| ≤
        |screwLerchTail t - screwLerchTail b| +
          |(t - b) * screwLerchTail₁ b| := abs_sub _ _
    _ ≤ (|screwLerchTail t| + |screwLerchTail b|) +
          |(t - b) * screwLerchTail₁ b| :=
      by
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_right (abs_sub (screwLerchTail t) (screwLerchTail b))
            |(t - b) * screwLerchTail₁ b|
    _ ≤ 2 * screwLerchConst + (t - b) * |screwLerchTail₁ b| := by
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hbt)]
      linarith

/-- The positive FU aperture density is dominated by the fixed inverse-quintic tail, uniformly
in the moving upper wall. -/
theorem ccmThirdGradeCesaroRectangularMixDensity_le_invPowFive
    {H t : ℝ} (hH : 0 < H) (ht : 0 < t) (_htH : t ≤ H) :
    ccmThirdGradeCesaroRectangularMixDensity H t ≤ 384 / t ^ 5 := by
  have hfrac : (2 * H - t) / H ≤ 2 := by
    apply (div_le_iff₀ hH).2
    linarith
  have ht5 : 0 < t ^ 5 := pow_pos ht 5
  unfold ccmThirdGradeCesaroRectangularMixDensity
  calc
    192 * (2 * H - t) / (H * t ^ 5) =
        (192 * ((2 * H - t) / H)) / t ^ 5 := by
      field_simp [hH.ne', ht.ne']
    _ ≤ (192 * 2) / t ^ 5 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfrac (by norm_num)) ht5.le
    _ = 384 / t ^ 5 := by ring

/-- After exact Gamma cancellation, every moving FU chart-error slice has an inverse-quartic
majorant independent of the upper wall. -/
theorem abs_rectangularMixDensity_mul_gammaLerchDefect_le
    {b H t : ℝ} (hb : 0 < b) (hbt : b ≤ t) (htH : t ≤ H) :
    |ccmThirdGradeCesaroRectangularMixDensity H t *
        ccmFUCentralGammaLerchAffineDefect b t| ≤
      (768 * screwLerchConst / b + 384 * |screwLerchTail₁ b|) *
        (1 / t ^ 4) := by
  have ht : 0 < t := hb.trans_le hbt
  have hH : 0 < H := ht.trans_le htH
  have hdensity0 := ccmThirdGradeCesaroRectangularMixDensity_nonneg hH ht htH
  have hdensity :=
    ccmThirdGradeCesaroRectangularMixDensity_le_invPowFive hH ht htH
  have hdef := abs_ccmFUCentralGammaLerchAffineDefect_le hb hbt
  have htail0 : 0 ≤ screwLerchConst := screwLerchConst_nonneg
  have hA0 : 0 ≤ |screwLerchTail₁ b| := abs_nonneg _
  have hdef' :
      |ccmFUCentralGammaLerchAffineDefect b t| ≤
        2 * screwLerchConst + t * |screwLerchTail₁ b| := by
    calc
      _ ≤ 2 * screwLerchConst + (t - b) * |screwLerchTail₁ b| := hdef
      _ ≤ 2 * screwLerchConst + t * |screwLerchTail₁ b| := by
        nlinarith
  calc
    |ccmThirdGradeCesaroRectangularMixDensity H t *
        ccmFUCentralGammaLerchAffineDefect b t| =
        ccmThirdGradeCesaroRectangularMixDensity H t *
          |ccmFUCentralGammaLerchAffineDefect b t| := by
      rw [abs_mul, abs_of_nonneg hdensity0]
    _ ≤ ccmThirdGradeCesaroRectangularMixDensity H t *
          (2 * screwLerchConst + t * |screwLerchTail₁ b|) :=
      mul_le_mul_of_nonneg_left hdef' hdensity0
    _ ≤ (384 / t ^ 5) *
          (2 * screwLerchConst + t * |screwLerchTail₁ b|) := by
      exact mul_le_mul_of_nonneg_right hdensity (by positivity)
    _ ≤ (768 * screwLerchConst / b + 384 * |screwLerchTail₁ b|) *
          (1 / t ^ 4) := by
      field_simp [hb.ne', ht.ne']
      nlinarith

/-- Positive marked FU mixture of the purely archimedean diagonal chart defect. -/
def ccmFUCentralGammaLerchAffineMixture (b H : ℝ) : ℝ :=
  (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
    ccmFUCentralGammaLerchAffineDefect b t) +
  (32 / H ^ 4) * ccmFUCentralGammaLerchAffineDefect b H

/-- **Uniform diagonal Gamma chart bound.** The entire Gamma/Lerch term created by transporting
the FU source into central Suzuki coordinates is uniformly bounded in the cofinal wall. Hence it
cannot carry the RH obstruction. -/
theorem exists_nonnegative_uniform_bound_ccmFUCentralGammaLerchAffineMixture
    {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, b < H →
      |ccmFUCentralGammaLerchAffineMixture b H| ≤ C := by
  let A : ℝ := |screwLerchTail₁ b|
  let K : ℝ := 768 * screwLerchConst / b + 384 * A
  let Bbulk : ℝ := K * (1 / (3 * b ^ 3))
  let Bend : ℝ := 64 * screwLerchConst / b ^ 4 + 32 * A / b ^ 3
  refine ⟨Bbulk + Bend, ?_, ?_⟩
  · have hA : 0 ≤ A := by
      dsimp only [A]
      exact abs_nonneg _
    have hK : 0 ≤ K := by
      dsimp only [K, A]
      exact add_nonneg
        (div_nonneg (mul_nonneg (by norm_num) screwLerchConst_nonneg) hb.le)
        (mul_nonneg (by norm_num) (abs_nonneg _))
    have hBbulk : 0 ≤ Bbulk := by
      dsimp only [Bbulk]
      exact mul_nonneg hK (by positivity)
    have hBend : 0 ≤ Bend := by
      dsimp only [Bend, A]
      exact add_nonneg
        (div_nonneg (mul_nonneg (by norm_num) screwLerchConst_nonneg)
          (pow_nonneg hb.le 4))
        (div_nonneg (mul_nonneg (by norm_num) (abs_nonneg _))
          (pow_nonneg hb.le 3))
    exact add_nonneg hBbulk hBend
  · intro H hbH
    have hbHle : b ≤ H := hbH.le
    have hH : 0 < H := hb.trans hbH
    have htailCont : ContinuousOn screwLerchTail (Set.Icc b H) := by
      intro t ht
      exact (hasDerivAt_screwLerchTail (hb.trans_le ht.1)).continuousAt.continuousWithinAt
    have hdefCont : ContinuousOn
        (ccmFUCentralGammaLerchAffineDefect b) (Set.Icc b H) := by
      unfold ccmFUCentralGammaLerchAffineDefect
      exact (htailCont.sub continuousOn_const).sub
        ((continuousOn_id.sub continuousOn_const).mul continuousOn_const)
    have hdensityCont : ContinuousOn
        (ccmThirdGradeCesaroRectangularMixDensity H) (Set.Icc b H) := by
      intro t ht
      have ht0 : t ≠ 0 := (hb.trans_le ht.1).ne'
      unfold ccmThirdGradeCesaroRectangularMixDensity
      exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
        (continuousAt_const.mul (continuousAt_id.pow 5))
        (mul_ne_zero hH.ne' (pow_ne_zero 5 ht0))).continuousWithinAt
    have hint : IntervalIntegrable
        (fun t => ccmThirdGradeCesaroRectangularMixDensity H t *
          ccmFUCentralGammaLerchAffineDefect b t) volume b H := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hbHle]
      exact hdensityCont.mul hdefCont
    have hK : 0 ≤ K := by
      dsimp only [K, A]
      exact add_nonneg
        (div_nonneg (mul_nonneg (by norm_num) screwLerchConst_nonneg) hb.le)
        (mul_nonneg (by norm_num) (abs_nonneg _))
    have hmajor : IntervalIntegrable (fun t : ℝ => K * (1 / t ^ 4)) volume b H := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hbHle]
      apply continuousOn_const.mul
      apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 4)
      intro t ht
      exact pow_ne_zero 4 (hb.trans_le ht.1).ne'
    have hbulk :
        |∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
            ccmFUCentralGammaLerchAffineDefect b t| ≤ Bbulk := by
      calc
        _ ≤ ∫ t in b..H,
            |ccmThirdGradeCesaroRectangularMixDensity H t *
              ccmFUCentralGammaLerchAffineDefect b t| :=
          intervalIntegral.abs_integral_le_integral_abs hbHle
        _ ≤ ∫ t in b..H, K * (1 / t ^ 4) := by
          apply intervalIntegral.integral_mono_on hbHle hint.abs hmajor
          intro t ht
          dsimp only [K, A]
          exact abs_rectangularMixDensity_mul_gammaLerchDefect_le
            hb ht.1 ht.2
        _ = K * (∫ t in b..H, 1 / t ^ 4) := by
          rw [intervalIntegral.integral_const_mul]
        _ ≤ K * (1 / (3 * b ^ 3)) := by
          exact mul_le_mul_of_nonneg_left
            (GaloisForLFunctions.HTGeometry.integral_one_div_pow_four_le hb hbHle) hK
        _ = Bbulk := by rfl
    have hdefH := abs_ccmFUCentralGammaLerchAffineDefect_le hb hbHle
    have hdefH' :
        |ccmFUCentralGammaLerchAffineDefect b H| ≤
          2 * screwLerchConst + H * A := by
      dsimp only [A]
      calc
        _ ≤ 2 * screwLerchConst + (H - b) * |screwLerchTail₁ b| := hdefH
        _ ≤ 2 * screwLerchConst + H * |screwLerchTail₁ b| := by
          nlinarith [abs_nonneg (screwLerchTail₁ b)]
    have hb3 : 0 < b ^ 3 := pow_pos hb 3
    have hb4 : 0 < b ^ 4 := pow_pos hb 4
    have hH3 : 0 < H ^ 3 := pow_pos hH 3
    have hH4 : 0 < H ^ 4 := pow_pos hH 4
    have hb3H3 : b ^ 3 ≤ H ^ 3 := pow_le_pow_left₀ hb.le hbHle 3
    have hb4H4 : b ^ 4 ≤ H ^ 4 := pow_le_pow_left₀ hb.le hbHle 4
    have hend :
        |(32 / H ^ 4) * ccmFUCentralGammaLerchAffineDefect b H| ≤ Bend := by
      calc
        _ = (32 / H ^ 4) * |ccmFUCentralGammaLerchAffineDefect b H| := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 32 / H ^ 4)]
        _ ≤ (32 / H ^ 4) * (2 * screwLerchConst + H * A) :=
          mul_le_mul_of_nonneg_left hdefH' (by positivity)
        _ = 64 * screwLerchConst / H ^ 4 + 32 * A / H ^ 3 := by
          field_simp [hH.ne']
          ring
        _ ≤ 64 * screwLerchConst / b ^ 4 + 32 * A / b ^ 3 := by
          apply add_le_add
          · exact div_le_div_of_nonneg_left
              (mul_nonneg (by norm_num) screwLerchConst_nonneg) hb4 hb4H4
          · exact div_le_div_of_nonneg_left
              (mul_nonneg (by norm_num) (abs_nonneg _)) hb3 hb3H3
        _ = Bend := by rfl
    unfold ccmFUCentralGammaLerchAffineMixture
    exact (abs_add_le _ _).trans (add_le_add hbulk hend)

/-- Positive marked FU mixture of the literal affine-normalized Xi-screw codiagonal. -/
def ccmFUCentralXiScrewCodiagonalMixture (b H : ℝ) : ℝ :=
  (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
    ccmGuinandWeilXiScrewCodiagonal b t) +
  (32 / H ^ 4) * ccmGuinandWeilXiScrewCodiagonal b H

/-- The full central rectangular mixture splits into a literal Xi-screw source mixture and the
bounded Gamma/Lerch chart term. No arithmetic positive/negative region is separated. -/
theorem ccmFUCentralRectangularAffineMixture_eq_two_mul_xiScrew_add_two_mul_gammaLerch
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmFUCentralRectangularAffineMixture b H =
      2 * ccmFUCentralXiScrewCodiagonalMixture b H +
        2 * ccmFUCentralGammaLerchAffineMixture b H := by
  have hcodCont : ContinuousOn
      (ccmGuinandWeilXiScrewCodiagonal b) (Set.Icc b H) := by
    unfold ccmGuinandWeilXiScrewCodiagonal
    exact (continuous_suzukiPsi.continuousOn.sub continuousOn_const).sub
      ((continuousOn_id.sub continuousOn_const).mul continuousOn_const)
  have htailCont : ContinuousOn screwLerchTail (Set.Icc b H) := by
    intro t ht
    exact (hasDerivAt_screwLerchTail (hb.trans_le ht.1)).continuousAt.continuousWithinAt
  have hdefCont : ContinuousOn
      (ccmFUCentralGammaLerchAffineDefect b) (Set.Icc b H) := by
    unfold ccmFUCentralGammaLerchAffineDefect
    exact (htailCont.sub continuousOn_const).sub
      ((continuousOn_id.sub continuousOn_const).mul continuousOn_const)
  have hH : 0 < H := hb.trans_le hbH
  have hdensityCont : ContinuousOn
      (ccmThirdGradeCesaroRectangularMixDensity H) (Set.Icc b H) := by
    intro t ht
    have ht0 : t ≠ 0 := (hb.trans_le ht.1).ne'
    unfold ccmThirdGradeCesaroRectangularMixDensity
    exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH.ne' (pow_ne_zero 5 ht0))).continuousWithinAt
  have hcodInt : IntervalIntegrable
      (fun t => ccmThirdGradeCesaroRectangularMixDensity H t *
        ccmGuinandWeilXiScrewCodiagonal b t) volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbH]
    exact hdensityCont.mul hcodCont
  have hdefInt : IntervalIntegrable
      (fun t => ccmThirdGradeCesaroRectangularMixDensity H t *
        ccmFUCentralGammaLerchAffineDefect b t) volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbH]
    exact hdensityCont.mul hdefCont
  have hbulk :
      (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
        ccmFUCentralRectangularAffineRemainder b t) =
        2 * (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
          ccmGuinandWeilXiScrewCodiagonal b t) +
        2 * (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
          ccmFUCentralGammaLerchAffineDefect b t) := by
    calc
      _ = ∫ t in b..H,
          (2 * (ccmThirdGradeCesaroRectangularMixDensity H t *
            ccmGuinandWeilXiScrewCodiagonal b t) +
           2 * (ccmThirdGradeCesaroRectangularMixDensity H t *
            ccmFUCentralGammaLerchAffineDefect b t)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hbH] at ht
        change ccmThirdGradeCesaroRectangularMixDensity H t *
            ccmFUCentralRectangularAffineRemainder b t =
          2 * (ccmThirdGradeCesaroRectangularMixDensity H t *
            ccmGuinandWeilXiScrewCodiagonal b t) +
          2 * (ccmThirdGradeCesaroRectangularMixDensity H t *
            ccmFUCentralGammaLerchAffineDefect b t)
        rw [ccmFUCentralRectangularAffineRemainder_eq_two_mul_xiScrewCodiagonal_add_lerchDefect
          hb ht.1]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hcodInt.const_mul 2) (hdefInt.const_mul 2),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hend :=
    ccmFUCentralRectangularAffineRemainder_eq_two_mul_xiScrewCodiagonal_add_lerchDefect
      hb hbH
  unfold ccmFUCentralRectangularAffineMixture
    ccmFUCentralXiScrewCodiagonalMixture
    ccmFUCentralGammaLerchAffineMixture
  rw [hbulk, hend]
  ring

/-- **Bounded-perturbation FU--Suzuki law.** The RH-bearing anchored FU moment is exactly the
negative Xi-screw codiagonal mixture, up to the uniformly bounded Gamma/Lerch chart term. -/
theorem ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_neg_xiScrewCodiagonalMixture_sub_gammaLerch
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H =
      -ccmFUCentralXiScrewCodiagonalMixture b H -
        ccmFUCentralGammaLerchAffineMixture b H := by
  rw [ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_neg_half_centralAffineMixture
      hb hbH,
    ccmFUCentralRectangularAffineMixture_eq_two_mul_xiScrew_add_two_mul_gammaLerch hb hbH]
  ring

/-- Uniform boundedness of the literal central Xi-screw codiagonal mixture. -/
def CCMFUCentralXiScrewCodiagonalMixtureBound (b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, b < H →
    |ccmFUCentralXiScrewCodiagonalMixture b H| ≤ C

/-- **Exact shared CCM-FU/Suzuki frontier.** Uniform boundedness of the completed triangular
prime--polar window is equivalent to uniform boundedness of one literal positive mixture of
affine-normalized Xi-screw codiagonals. The difference is the unconditionally bounded Gamma/Lerch
chart term proved above. -/
theorem ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_iff_xiScrewCodiagonalMixtureBound
    {b : ℝ} (hb : 0 < b) :
    CCMGuinandWeilThirdGradeCesaroAnchoredMomentBound b ↔
      CCMFUCentralXiScrewCodiagonalMixtureBound b := by
  obtain ⟨G, hG0, hG⟩ :=
    exists_nonnegative_uniform_bound_ccmFUCentralGammaLerchAffineMixture hb
  constructor
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C + G, add_nonneg hC0 hG0, ?_⟩
    intro H hbH
    have heq :=
      ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_neg_xiScrewCodiagonalMixture_sub_gammaLerch
        hb hbH.le
    have hrecover :
        ccmFUCentralXiScrewCodiagonalMixture b H =
          -ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H -
            ccmFUCentralGammaLerchAffineMixture b H := by
      linarith
    rw [hrecover]
    calc
      |-ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H -
          ccmFUCentralGammaLerchAffineMixture b H| ≤
          |ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H| +
            |ccmFUCentralGammaLerchAffineMixture b H| := by
        simpa only [abs_neg] using
          abs_sub (-ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment b H)
            (ccmFUCentralGammaLerchAffineMixture b H)
      _ ≤ C + G := add_le_add (hC H hbH) (hG H hbH)
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C + G, add_nonneg hC0 hG0, ?_⟩
    intro H hbH
    rw [ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_neg_xiScrewCodiagonalMixture_sub_gammaLerch
      hb hbH.le]
    calc
      |-ccmFUCentralXiScrewCodiagonalMixture b H -
          ccmFUCentralGammaLerchAffineMixture b H| ≤
          |ccmFUCentralXiScrewCodiagonalMixture b H| +
            |ccmFUCentralGammaLerchAffineMixture b H| := by
        simpa only [abs_neg] using
          abs_sub (-ccmFUCentralXiScrewCodiagonalMixture b H)
            (ccmFUCentralGammaLerchAffineMixture b H)
      _ ≤ C + G := add_le_add (hC H hbH) (hG H hbH)

/-- Uniform control of the literal Xi-screw codiagonal mixture closes CCM-FU and therefore forces
the Riemann hypothesis. -/
theorem riemannHypothesis_of_ccmFUCentralXiScrewCodiagonalMixtureBound
    {b : ℝ} (hb : 0 < b)
    (hbound : CCMFUCentralXiScrewCodiagonalMixtureBound b) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound hb
  exact
    (ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_iff_xiScrewCodiagonalMixtureBound hb).2
      hbound

end GaloisForLFunctions.RHTower

import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeRectangularPrimitiveCurrent
import GaloisForLFunctions.RHTower.CCMFirstClockVolterra
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularGammaPolarSourceLaw
import GaloisForLFunctions.RHTower.CCMGuinandWeilXiScrewGreenConnection

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

end GaloisForLFunctions.RHTower

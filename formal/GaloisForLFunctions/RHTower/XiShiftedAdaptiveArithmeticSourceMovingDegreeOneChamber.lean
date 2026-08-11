import GaloisForLFunctions.RHTower.XiShiftedAdaptiveArithmeticSourceFarRightPositivity

/-!
# Moving degree-one chamber of the adaptive arithmetic source

Fixed amplitudes have a positive far-right source horizon.  This module proves that no such
horizon is uniform even over monic degree-one amplitudes.  The moving family

`A(R,w) = X - C (R / w^2)`

tracks the anisotropic moment dilation.  Its literal completed arithmetic source has an exact
quadratic recession constant.  At `R = 5/4` that constant is negative, so coefficient conditioning
alone carries a negative source cofinally; degree escape is unnecessary.

The positive survivor is an admission law: one must constrain the scaled root `w^2 r`, not only
degree or monicity.
-/

open Filter Polynomial Topology

namespace RHTower

noncomputable section

/-- Monic degree-one amplitude with root on the natural inverse-square mass scale. -/
def xiShiftedAdaptiveScaledDegreeOneAmplitude (R w : ℝ) : Polynomial ℝ :=
  X - C (R / w ^ 2)

/-- Exact adaptive shear polynomial of the scaled degree-one amplitude. -/
theorem xiShiftedBoundaryAdaptiveShearPolynomial_scaledDegreeOne (R w : ℝ) :
    xiShiftedBoundaryAdaptiveShearPolynomial
        (xiShiftedAdaptiveScaledDegreeOneAmplitude R w) =
      (2 : ℝ) • X ^ 4 - (3 * (R / w ^ 2)) • X ^ 3 +
        ((R / w ^ 2) ^ 2) • X ^ 2 := by
  simp [xiShiftedBoundaryAdaptiveShearPolynomial,
    xiShiftedAdaptiveScaledDegreeOneAmplitude,
    xiShiftedBoundaryShiftedEuler, Polynomial.smul_eq_C_mul,
    map_mul, map_pow]
  rw [Polynomial.C_ofNat 2, Polynomial.C_ofNat 3]
  ring

/-- The literal arithmetic source is the corresponding three-moment combination. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_scaledDegreeOne
    {R w : ℝ} (hw : 1 / 2 < w) :
    xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (xiShiftedAdaptiveScaledDegreeOneAmplitude R w) =
      4 * (xiShiftedReciprocalMoment (w ^ 2) 4).re -
        6 * (R / w ^ 2) * (xiShiftedReciprocalMoment (w ^ 2) 3).re +
        2 * (R / w ^ 2) ^ 2 * (xiShiftedReciprocalMoment (w ^ 2) 2).re := by
  rw [← two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource hw]
  change 2 * HTGeometry.momentFunctional
    (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re)
    (xiShiftedBoundaryAdaptiveShearPolynomial
      (xiShiftedAdaptiveScaledDegreeOneAmplitude R w)) = _
  rw [xiShiftedBoundaryAdaptiveShearPolynomial_scaledDegreeOne]
  simp only [HTGeometry.momentFunctional_add, HTGeometry.momentFunctional_sub,
    HTGeometry.momentFunctional_smul, HTGeometry.momentFunctional_X_pow]
  ring

/-- **Moving degree-one source chamber.**  The scaled root `R` sees the exact quadratic arcsine
recession constant `(24R² - 60R + 35)/64`. -/
theorem tendsto_scaled_xiShiftedAdaptiveDegreeOneArithmeticSource (R : ℝ) :
    Tendsto
      (fun w : ℝ => w ^ 9 / Real.log w *
        xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (xiShiftedAdaptiveScaledDegreeOneAmplitude R w))
      atTop
      (nhds ((24 * R ^ 2 - 60 * R + 35) / 64)) := by
  have h2 :=
    (tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam 2).const_mul (R ^ 2)
  have h3 :=
    (tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam 3).const_mul (-3 * R)
  have h4 :=
    (tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam 4).const_mul 2
  have h := (h2.add h3).add h4
  have hlim :
      R ^ 2 * GaloisForLFunctions.HTGeometry.normalizedCentralBinom 2 +
          (-3 * R) * GaloisForLFunctions.HTGeometry.normalizedCentralBinom 3 +
          2 * GaloisForLFunctions.HTGeometry.normalizedCentralBinom 4 =
        (24 * R ^ 2 - 60 * R + 35) / 64 := by
    norm_num [GaloisForLFunctions.HTGeometry.normalizedCentralBinom,
      Nat.centralBinom, Nat.choose]
    ring
  rw [hlim] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  rw [xiShiftedAdaptiveMixedCompletedArithmeticSource_scaledDegreeOne
    (by linarith : 1 / 2 < w)]
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  have hlog : Real.log w ≠ 0 := ne_of_gt (Real.log_pos hw)
  field_simp [hw0, hlog]
  ring

/-- At the explicit scaled root `5/4`, the moving monic degree-one source is eventually strictly
negative.  This unconditionally refutes every degree-only uniform positivity horizon. -/
theorem xiShiftedAdaptiveMovingDegreeOneArithmeticSource_eventually_neg :
    ∀ᶠ w : ℝ in atTop,
      xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (xiShiftedAdaptiveScaledDegreeOneAmplitude (5 / 4) w) < 0 := by
  have hlim : ((24 * (5 / 4 : ℝ) ^ 2 - 60 * (5 / 4 : ℝ) + 35) / 64) =
      -5 / 128 := by norm_num
  have h := tendsto_scaled_xiShiftedAdaptiveDegreeOneArithmeticSource (5 / 4)
  rw [hlim] at h
  have hlimit : (-5 / 128 : ℝ) < 0 := by norm_num
  have hscaled := h.eventually (Iio_mem_nhds hlimit)
  filter_upwards [hscaled, eventually_gt_atTop (1 : ℝ)] with w hs hw
  have hscale : 0 < w ^ 9 / Real.log w :=
    div_pos (pow_pos (lt_trans zero_lt_one hw) _) (Real.log_pos hw)
  rcases mul_neg_iff.mp hs with hneg | hneg
  · exact hneg.2
  · exact (not_lt_of_ge hscale.le hneg.1).elim

end

end RHTower

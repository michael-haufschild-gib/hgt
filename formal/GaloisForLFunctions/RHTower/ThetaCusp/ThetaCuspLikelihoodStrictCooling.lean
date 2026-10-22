import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedLikelihoodCumulantObstruction
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Strict cooling of the theta-cusp likelihood state

Strict Hankel positivity makes the total tilted likelihood variance positive at every positive
temperature.  The exact mean derivative is therefore strictly negative.  Modular reflection fixes
the initial mean at the seam, giving a source-wide calibrated upper bound.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- The zeroth tilted likelihood moment is the higher-tail spectral response. -/
theorem thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response
  {B : ℝ} (hB : 0 < B) :
    thetaCuspHigherLikelihoodSpectralMoment B 0 =
      thetaCuspHigherLikelihoodSpectralResponse B := by
  rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
  simp only [pow_zero, one_mul]
  exact integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB

/-- Every tilted likelihood moment is nonnegative. -/
theorem thetaCuspHigherLikelihoodSpectralMoment_nonneg
    {B : ℝ} (m : ℕ) :
    0 ≤ thetaCuspHigherLikelihoodSpectralMoment B m := by
  rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
  apply integral_nonneg_of_ae
  filter_upwards
    [ae_nonneg_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
  exact mul_nonneg (pow_nonneg ht _) (Real.exp_pos _).le

/-- Every positive-temperature first tilted moment is strictly positive. -/
theorem thetaCuspHigherLikelihoodSpectralMoment_one_pos
    {B : ℝ} (hB : 0 < B) :
    0 < thetaCuspHigherLikelihoodSpectralMoment B 1 := by
  have hdet := det_thetaCuspHigherLikelihoodSpectralMoment_hankel_pos hB 2
  have hdet' :
      0 <
        thetaCuspHigherLikelihoodSpectralMoment B 0 *
            thetaCuspHigherLikelihoodSpectralMoment B 2 -
          thetaCuspHigherLikelihoodSpectralMoment B 1 *
            thetaCuspHigherLikelihoodSpectralMoment B 1 := by
    simpa [HTGeometry.momentHankelMatrix, Matrix.det_fin_two] using hdet
  have hM0 := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := B) 0
  have hM2 : 0 < thetaCuspHigherLikelihoodSpectralMoment B 2 := by
    by_contra h
    have hM2nonpos :
        thetaCuspHigherLikelihoodSpectralMoment B 2 ≤ 0 := le_of_not_gt h
    have hprod :
        thetaCuspHigherLikelihoodSpectralMoment B 0 *
            thetaCuspHigherLikelihoodSpectralMoment B 2 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hM0 hM2nonpos
    nlinarith [sq_nonneg (thetaCuspHigherLikelihoodSpectralMoment B 1)]
  have hM1nonneg :=
    thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := B) 1
  exact lt_of_le_of_ne hM1nonneg fun hM1zero => by
    have hzero :
        thetaCuspHigherLikelihoodSpectralMoment B 1 = 0 :=
      hM1zero.symm
    have hInt :
        Integrable
          (fun t : ℝ => t ^ (1 : ℕ) * Real.exp (-B * t))
          thetaCuspHigherLikelihoodSpectralMeasure :=
      integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1 hB
    have hae :
        (fun t : ℝ => t ^ (1 : ℕ) * Real.exp (-B * t)) =ᵐ[
          thetaCuspHigherLikelihoodSpectralMeasure] 0 := by
      apply (integral_eq_zero_iff_of_nonneg_ae
        (by
          filter_upwards
            [ae_nonneg_thetaCuspHigherLikelihoodSpectralMeasure] with t ht
          exact mul_nonneg (pow_nonneg ht _) (Real.exp_pos _).le)
        hInt).mp
      simpa [thetaCuspHigherLikelihoodSpectralMoment_eq_integral] using hzero
    have hM2zero :
        thetaCuspHigherLikelihoodSpectralMoment B 2 = 0 := by
      rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
      apply integral_eq_zero_of_ae
      filter_upwards [hae] with t ht
      simpa [pow_two] using congrArg (fun z : ℝ => t * z) ht
    linarith

/-- The likelihood partition is one plus the zeroth tilted moment. -/
theorem thetaCuspLikelihoodPartition_eq_one_add_moment_zero
    {B : ℝ} (hB : 0 < B) :
    thetaCuspLikelihoodPartition B =
      1 + thetaCuspHigherLikelihoodSpectralMoment B 0 := by
  rw [thetaCuspLikelihoodPartition,
    thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response hB]

/-- The total likelihood variance, including the atom at spectral coordinate zero, is strictly
positive at every positive temperature. -/
theorem thetaCuspLikelihoodVariance_pos
    {B : ℝ} (hB : 0 < B) :
    0 < thetaCuspLikelihoodVariance B := by
  have hdet := det_thetaCuspHigherLikelihoodSpectralMoment_hankel_pos hB 2
  have hdet' :
      0 <
        thetaCuspHigherLikelihoodSpectralMoment B 0 *
            thetaCuspHigherLikelihoodSpectralMoment B 2 -
          thetaCuspHigherLikelihoodSpectralMoment B 1 *
            thetaCuspHigherLikelihoodSpectralMoment B 1 := by
    simpa [HTGeometry.momentHankelMatrix, Matrix.det_fin_two] using hdet
  have hM2 := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := B) 2
  have hpart := thetaCuspLikelihoodPartition_pos hB
  have hpartEq := thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB
  unfold thetaCuspLikelihoodVariance thetaCuspLikelihoodMean
  have hid :
      thetaCuspHigherLikelihoodSpectralMoment B 2 /
            thetaCuspLikelihoodPartition B -
          (thetaCuspHigherLikelihoodSpectralMoment B 1 /
            thetaCuspLikelihoodPartition B) ^ (2 : ℕ) =
        (thetaCuspLikelihoodPartition B *
              thetaCuspHigherLikelihoodSpectralMoment B 2 -
            thetaCuspHigherLikelihoodSpectralMoment B 1 ^ (2 : ℕ)) /
          thetaCuspLikelihoodPartition B ^ (2 : ℕ) := by
    field_simp [hpart.ne']
  rw [hid]
  apply div_pos
  · rw [hpartEq]
    nlinarith
  · exact sq_pos_of_pos hpart

/-- The total likelihood mean is strictly positive at positive temperature. -/
theorem thetaCuspLikelihoodMean_pos
    {B : ℝ} (hB : 0 < B) :
    0 < thetaCuspLikelihoodMean B := by
  unfold thetaCuspLikelihoodMean
  exact div_pos
    (thetaCuspHigherLikelihoodSpectralMoment_one_pos hB)
    (thetaCuspLikelihoodPartition_pos hB)

/-- **Strict likelihood cooling.**  Increasing intrinsic temperature strictly decreases the
theta-cusp likelihood mean. -/
theorem strictAntiOn_thetaCuspLikelihoodMean :
    StrictAntiOn thetaCuspLikelihoodMean (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro B hB
    exact (hasDerivAt_thetaCuspLikelihoodMean hB).continuousAt.continuousWithinAt
  · intro B hB
    have hBpos : 0 < B := by
      simpa only [interior_Ioi, mem_Ioi] using hB
    rw [(hasDerivAt_thetaCuspLikelihoodMean hBpos).deriv]
    exact neg_neg_of_pos (thetaCuspLikelihoodVariance_pos hBpos)

/-- Exact modular calibration of the likelihood mean. -/
theorem two_pi_mul_thetaCuspLikelihoodMean_seam :
    2 * Real.pi *
        thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate 0) =
      thetaCuspFirstAtomBoundaryLogSlope := by
  have hB0 : 0 < thetaCuspLikelihoodCoordinate 0 := by
    exact thetaCuspLikelihoodCoordinate_pos (by norm_num)
  have hpart := thetaCuspLikelihoodPartition_pos hB0
  have hpartEq :=
    thetaCuspLikelihoodPartition_eq_one_add_moment_zero hB0
  unfold thetaCuspLikelihoodMean
  rw [show
    2 * Real.pi *
        (thetaCuspHigherLikelihoodSpectralMoment
          (thetaCuspLikelihoodCoordinate 0) 1 /
            thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate 0)) =
      (2 * Real.pi *
        thetaCuspHigherLikelihoodSpectralMoment
          (thetaCuspLikelihoodCoordinate 0) 1) /
            thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate 0) by ring]
  apply (div_eq_iff hpart.ne').2
  rw [hpartEq]
  exact thetaCuspHigherLikelihoodSpectralMoment_seam_barycenter

/-- On the nonnegative source half-line, the modular seam is the exact maximum of the calibrated
likelihood mean. -/
theorem two_pi_mul_thetaCuspLikelihoodMean_coordinate_le_boundarySlope
    {x : ℝ} (hx : 0 ≤ x) :
    2 * Real.pi *
        thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) ≤
      thetaCuspFirstAtomBoundaryLogSlope := by
  have hB0 : 0 < thetaCuspLikelihoodCoordinate 0 :=
    thetaCuspLikelihoodCoordinate_pos (by norm_num)
  have hBx : 0 < thetaCuspLikelihoodCoordinate x :=
    thetaCuspLikelihoodCoordinate_pos hx
  have hcoord :
      thetaCuspLikelihoodCoordinate 0 ≤ thetaCuspLikelihoodCoordinate x := by
    have he : 1 ≤ Real.exp x := Real.one_le_exp hx
    have hesq : 1 ≤ Real.exp x ^ (2 : ℕ) := by
      nlinarith [Real.exp_pos x]
    unfold thetaCuspLikelihoodCoordinate
    norm_num
    nlinarith [Real.pi_pos]
  have hmean :
      thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) ≤
        thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate 0) :=
    strictAntiOn_thetaCuspLikelihoodMean.antitoneOn
      hB0 hBx hcoord
  have hpi : 0 < 2 * Real.pi := by positivity
  nlinarith [two_pi_mul_thetaCuspLikelihoodMean_seam,
    mul_nonneg hpi.le (sub_nonneg.mpr hmean)]

/-- Away from the modular seam, strict cooling makes the calibrated mean strictly smaller than
the boundary slope. -/
theorem two_pi_mul_thetaCuspLikelihoodMean_coordinate_lt_boundarySlope
    {x : ℝ} (hx : 0 < x) :
    2 * Real.pi *
        thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) <
      thetaCuspFirstAtomBoundaryLogSlope := by
  have hB0 : 0 < thetaCuspLikelihoodCoordinate 0 :=
    thetaCuspLikelihoodCoordinate_pos (by norm_num)
  have hBx : 0 < thetaCuspLikelihoodCoordinate x :=
    thetaCuspLikelihoodCoordinate_pos hx.le
  have hcoord :
      thetaCuspLikelihoodCoordinate 0 < thetaCuspLikelihoodCoordinate x := by
    have he : 1 < Real.exp x := by
      simpa using (Real.exp_lt_exp.mpr hx : Real.exp 0 < Real.exp x)
    have hesq : 1 < Real.exp x ^ (2 : ℕ) := by
      nlinarith [Real.exp_pos x]
    unfold thetaCuspLikelihoodCoordinate
    norm_num
    nlinarith [Real.pi_pos]
  have hmean :
      thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x) <
        thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate 0) :=
    strictAntiOn_thetaCuspLikelihoodMean hB0 hBx hcoord
  have hpi : 0 < 2 * Real.pi := by positivity
  nlinarith [two_pi_mul_thetaCuspLikelihoodMean_seam,
    mul_pos hpi (sub_pos.mpr hmean)]

end

end RHTower

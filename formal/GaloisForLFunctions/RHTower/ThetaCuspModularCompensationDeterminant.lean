import GaloisForLFunctions.RHTower.ThetaCuspModularRatioUpperBarrier
import GaloisForLFunctions.RHTower.ThetaCuspEvenCompactSourceCoordinates

/-!
# A complete-source determinant comparison retaining the modular ratio defect

The global source bounds place `J` in `[0, 1)`. Keeping `J` in the center
inequality yields a lower compensation polynomial whose concavity contributes
an explicit nonnegative reserve. All seven moments are the actual native
moments in the modular coordinates. The final theorem transfers the reserve
to the rank-four determinant with the fixed coefficient `10^12`.
Positivity of the resulting lower expression remains unproved.
-/

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open GaloisForLFunctions.HTGeometry

/-- The common factor in the actual source and its first derivative. -/
def sourceAmplitude (x : ℝ) : ℝ := Bottcher.completedThetaProfile x * t x / 12

/-- The first source derivative polynomial with a free ratio-defect coordinate. -/
def sourceFirstPolynomial (x j : ℝ) : ℝ :=
  u x*(1/6-2*k x)*(k x-1/6)+2*(k x+1/3)*j

/-- The full-source compensation lower polynomial retaining the defect. -/
def compensationPolynomial (x j : ℝ) : ℝ :=
  3*(k x-1/6)^2+((u x*(k x-2/3)-j)/2)*(k x-1/6)*sourceFirstPolynomial x j

/-- The endpoint chord of the compensation polynomial on the proved defect interval. -/
def compensationChord (x : ℝ) : ℝ :=
  (1-J x)*compensationPolynomial x 0+J x*compensationPolynomial x 1

/-- The concavity reserve on the actual defect interval. -/
def compensationReserve (x : ℝ) : ℝ :=
  (k x-1/6)*(k x+1/3)*J x*(1-J x)

theorem gap_eq_ratio_coordinates {x : ℝ} (hx : 0 ≤ x) :
    A x = (4/3)*t x*(k x+1/3) := by
  have ht := (t_pos hx).ne'
  dsimp [k]
  field_simp [ht]
  ring

theorem source_eq_ratio_coordinates {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullSource x = sourceAmplitude x*(k x-1/6) := by
  rw [thetaCuspFullSource_eq_compactSourceZero]
  change Bottcher.completedThetaProfile x*HTGeometry.oddCompactSourceZero (u x) (A x) = _
  rw [gap_eq_ratio_coordinates hx]
  dsimp [HTGeometry.oddCompactSourceZero, sourceAmplitude, t]
  ring

theorem source_deriv_eq_ratio_coordinates {x : ℝ} (hx : 0 ≤ x) :
    deriv thetaCuspFullSource x = sourceAmplitude x*sourceFirstPolynomial x (J x) := by
  rw [deriv_thetaCuspFullSource_eq_compactSourceFirst]
  change Bottcher.completedThetaProfile x*HTGeometry.oddCompactSourceFirst (u x) (A x) (w x) = _
  have hw : w x = u x*k x-J x := by dsimp [J]; ring
  rw [gap_eq_ratio_coordinates hx, hw]
  dsimp [HTGeometry.oddCompactSourceFirst, sourceAmplitude, sourceFirstPolynomial, t]
  ring

theorem sourceFirstPolynomial_upper {x : ℝ} (hx : 0 ≤ x) :
    sourceFirstPolynomial x (J x) ≤ -u x*(5*k x/6+25/36) := by
  have hw := thetaCuspModularMassDrift_le_shear hx
  have hj : J x ≤ u x*(k x-1) := by dsimp [J]; nlinarith only [hw]
  have hk := k_gt hx
  have hm := mul_le_mul_of_nonneg_left hj (show 0 ≤ 2*(k x+1/3) by linarith only [hk])
  dsimp [sourceFirstPolynomial]
  nlinarith only [hm]

theorem sourceFirstPolynomial_nonpos {x : ℝ} (hx : 0 ≤ x) :
    sourceFirstPolynomial x (J x) ≤ 0 := by
  have hu := thetaCuspModularMassDrift_nonneg hx
  have hk := k_gt hx
  exact (sourceFirstPolynomial_upper hx).trans
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) (by linarith only [hk]))

theorem center_le_retained_ratio {x : ℝ} (hx : 0 ≤ x) :
    4*x ≤ u x*(k x-2/3)-J x := by
  have h := thetaCuspModularTransverseShear_lower hx
  dsimp [J]
  nlinarith only [h]

theorem compensation_source_eq_ratio {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspCenterCompensationSource x = sourceAmplitude x^2*
      (3*(k x-1/6)^2+2*x*(k x-1/6)*sourceFirstPolynomial x (J x)) := by
  unfold thetaCuspCenterCompensationSource
  rw [source_eq_ratio_coordinates hx, source_deriv_eq_ratio_coordinates hx]
  ring

theorem compensation_source_lower {x : ℝ} (hx : 0 ≤ x) :
    sourceAmplitude x^2*compensationPolynomial x (J x) ≤
      thetaCuspCenterCompensationSource x := by
  have hk := k_gt hx
  have hp := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ k x-1/6 by linarith only [hk])
    (sourceFirstPolynomial_nonpos hx)
  have hc : 2*x ≤ (u x*(k x-2/3)-J x)/2 := by
    linarith only [center_le_retained_ratio hx]
  have hm := mul_le_mul_of_nonpos_right hc hp
  have ha := mul_le_mul_of_nonneg_left hm (sq_nonneg (sourceAmplitude x))
  rw [compensation_source_eq_ratio hx]
  dsimp [compensationPolynomial]
  nlinarith only [ha]

theorem compensationPolynomial_eq_chord_add_reserve (x : ℝ) :
    compensationPolynomial x (J x) = compensationChord x+compensationReserve x := by
  dsimp [compensationPolynomial, compensationChord, compensationReserve, sourceFirstPolynomial]
  ring

theorem compensationReserve_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ compensationReserve x := by
  have hk := k_gt hx
  have hj := J_nonneg hx
  have hJ := J_lt_one hx
  dsimp [compensationReserve]
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (by linarith only [hk]) (by linarith only [hk])) hj) (by linarith only [hJ])

theorem compensation_source_chord_with_reserve_lower {x : ℝ} (hx : 0 ≤ x) :
    sourceAmplitude x^2*compensationChord x + sourceAmplitude x^2*compensationReserve x ≤
      thetaCuspCenterCompensationSource x := by
  have h := compensation_source_lower hx
  rw [compensationPolynomial_eq_chord_add_reserve, mul_add] at h
  exact h

/-- Each of the seven native moments in the actual modular ratio coordinates. -/
def evenMoment (x : ℝ) (n : Fin 7) : ℝ :=
  HTGeometry.evenCompactSignedMoment n (u x) ((4/3)*t x*(k x+1/3)) (u x*k x-J x)

/-- The finite determinant lower model; its sign is still an open problem. -/
def evenLowerDet (x : ℝ) : ℝ :=
  hankelFourDet (evenMoment x 0) (evenMoment x 1) (evenMoment x 2)
    (evenMoment x 3) (evenMoment x 4) (evenMoment x 5)
    (evenMoment x 6+1000000000000*(t x/12)^2*compensationChord x)

theorem evenMoment_eq_native {x : ℝ} (hx : 0 ≤ x) (n : Fin 7) :
    (-1 : ℝ)^n.val*thetaCuspNativeReflectionJet (2*n.val) x =
      Bottcher.completedThetaProfile x^2*evenMoment x n := by
  have h := thetaCuspNativeEvenJet_eq_compactScalar n x
  change _ = Bottcher.completedThetaProfile x^2*
    HTGeometry.evenCompactSignedMoment n (u x) (A x) (w x) at h
  have hw : w x = u x*k x-J x := by dsimp [J]; ring
  rw [gap_eq_ratio_coordinates hx, hw] at h
  exact h

private theorem head_det_eq (x : ℝ) :
    (thetaCuspNativeEvenHead x).det =
      thetaCuspNativeReflectionJet 0 x*thetaCuspNativeReflectionJet 4 x*thetaCuspNativeReflectionJet 8 x-
      thetaCuspNativeReflectionJet 0 x*(-thetaCuspNativeReflectionJet 6 x)^2-
      (-thetaCuspNativeReflectionJet 2 x)^2*thetaCuspNativeReflectionJet 8 x+
      2*(-thetaCuspNativeReflectionJet 2 x)*thetaCuspNativeReflectionJet 4 x*(-thetaCuspNativeReflectionJet 6 x)-
      thetaCuspNativeReflectionJet 4 x^3 := by
  norm_num [thetaCuspNativeEvenHead, finiteHankelMatrix, Matrix.det_fin_three]
  ring

theorem compensated_det_eq (C x : ℝ) :
    (thetaCuspNativeEvenFourCompensated C x).det =
      thetaCuspNativeEvenFourDet x+C*thetaCuspCenterCompensationSource x*(thetaCuspNativeEvenHead x).det := by
  have he : thetaCuspNativeEvenFourCompensated C x =
      !![thetaCuspNativeReflectionJet 0 x, -thetaCuspNativeReflectionJet 2 x,
          thetaCuspNativeReflectionJet 4 x, -thetaCuspNativeReflectionJet 6 x;
        -thetaCuspNativeReflectionJet 2 x, thetaCuspNativeReflectionJet 4 x,
          -thetaCuspNativeReflectionJet 6 x, thetaCuspNativeReflectionJet 8 x;
        thetaCuspNativeReflectionJet 4 x, -thetaCuspNativeReflectionJet 6 x,
          thetaCuspNativeReflectionJet 8 x, -thetaCuspNativeReflectionJet 10 x;
        -thetaCuspNativeReflectionJet 6 x, thetaCuspNativeReflectionJet 8 x,
          -thetaCuspNativeReflectionJet 10 x,
          thetaCuspNativeReflectionJet 12 x+C*thetaCuspCenterCompensationSource x] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [thetaCuspNativeEvenFourCompensated]
  rw [he, det_hankelFour, hankelFourDet_last_add, thetaCuspNativeEvenFourDet_eq, head_det_eq]

theorem evenLowerDet_scaled_eq {x : ℝ} (hx : 0 ≤ x) :
    Bottcher.completedThetaProfile x^8*evenLowerDet x =
      thetaCuspNativeEvenFourDet x+
        1000000000000*sourceAmplitude x^2*compensationChord x*(thetaCuspNativeEvenHead x).det := by
  have h0 := evenMoment_eq_native hx 0
  have h1 := evenMoment_eq_native hx 1
  have h2 := evenMoment_eq_native hx 2
  have h3 := evenMoment_eq_native hx 3
  have h4 := evenMoment_eq_native hx 4
  have h5 := evenMoment_eq_native hx 5
  have h6 := evenMoment_eq_native hx 6
  norm_num at h0 h1 h2 h3 h4 h5 h6
  rw [thetaCuspNativeEvenFourDet_eq, head_det_eq, h0, h1, h2, h3, h4, h5, h6]
  unfold evenLowerDet hankelFourDet sourceAmplitude
  ring

/-- The actual fixed-coefficient determinant retains the complete positive reserve. -/
theorem compensated_det_lower {x : ℝ} (hx : 0 ≤ x) :
    Bottcher.completedThetaProfile x^8*evenLowerDet x+
      1000000000000*sourceAmplitude x^2*compensationReserve x*(thetaCuspNativeEvenHead x).det ≤
        (thetaCuspNativeEvenFourCompensated 1000000000000 x).det := by
  have hhead := (thetaCuspNativeEvenHead_posDef hx).det_pos
  have hm := mul_le_mul_of_nonneg_right (compensation_source_chord_with_reserve_lower hx)
    (show 0 ≤ 1000000000000*(thetaCuspNativeEvenHead x).det by positivity)
  rw [compensated_det_eq, evenLowerDet_scaled_eq hx]
  nlinarith only [hm]

/-- The retained determinant reserve is nonnegative on the entire actual half-orbit. -/
theorem determinant_reserve_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 1000000000000*sourceAmplitude x^2*compensationReserve x*(thetaCuspNativeEvenHead x).det := by
  have hhead := (thetaCuspNativeEvenHead_posDef hx).det_pos
  have hres := compensationReserve_nonneg hx
  positivity

end
end RHTower.ThetaCuspModularRatio

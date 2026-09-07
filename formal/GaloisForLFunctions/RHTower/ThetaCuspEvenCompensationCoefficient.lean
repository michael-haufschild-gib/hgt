import GaloisForLFunctions.RHTower.ThetaCuspEvenSeamDeterminant
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenSeamReserves
import GaloisForLFunctions.RHTower.ThetaCuspModularEnergyBounds

/-! # Unconditional rational bounds for the literal even compensation coefficient -/
namespace RHTower
noncomputable section

private abbrev X := thetaCuspSelfDualModularScale^2
private abbrev M := thetaCuspSelfDualThetaMass
private abbrev d := HTGeometry.modularThetaEvenSeamHeadPolynomial X
private abbrev e := HTGeometry.modularThetaEvenSeamFourPolynomial X
private abbrev q := HTGeometry.modularThetaEvenSeamMomentPolynomial 0 X

private theorem mass_pos : 0 < M := by
  have h := thetaCuspSelfDualThetaMass_gt_five_thousand_four_hundred_thirty_one_div_five_thousand
  dsimp [M]
  linarith

private theorem source_zero_sq : thetaCuspFullSource 0^2 = M^2*q := by
  simpa [thetaCuspNativeReflectionJet, M, q, X, pow_two] using
    thetaCuspNativeEvenMoment_zero_eq_polynomial (0 : Fin 7)

private theorem head_poly_pos : 0 < d := by
  have h := thetaCuspNativeEvenHead_zero_posDef.det_pos
  rw [thetaCuspNativeEvenHead_zero_det_eq_polynomial] at h
  exact (mul_pos_iff_of_pos_left (pow_pos mass_pos 6)).mp h

private theorem source_poly_pos : 0 < q := by
  have h := sq_pos_of_pos (thetaCuspFullSource_pos_all 0)
  rw [source_zero_sq] at h
  exact (mul_pos_iff_of_pos_left (pow_pos mass_pos 2)).mp h

/-- The literal Schur coordinate divided by source mass is an exact rational modular function. -/
theorem thetaCuspNativeEvenFourSchur_zero_div_source_sq :
    thetaCuspNativeEvenFourSchur 0 / thetaCuspFullSource 0^2 =
      HTGeometry.modularThetaEvenSeamFourPolynomial (thetaCuspSelfDualModularScale^2) /
        (HTGeometry.modularThetaEvenSeamHeadPolynomial (thetaCuspSelfDualModularScale^2) *
          HTGeometry.modularThetaEvenSeamMomentPolynomial 0 (thetaCuspSelfDualModularScale^2)) := by
  have hd := thetaCuspNativeEvenFourDet_eq_head_mul_schur (x := 0) le_rfl
  rw [thetaCuspNativeEvenFourDet_zero_eq_polynomial,
    thetaCuspNativeEvenHead_zero_det_eq_polynomial] at hd
  have hc : M^6*(M^2*e) = M^6*(d*thetaCuspNativeEvenFourSchur 0) := by
    convert hd using 1 <;> ring
  have hc' := mul_left_cancel₀ (pow_ne_zero 6 mass_pos.ne') hc
  have hs : thetaCuspNativeEvenFourSchur 0 = M^2*e/d := by
    apply (eq_div_iff head_poly_pos.ne').mpr
    nlinarith only [hc']
  rw [hs, source_zero_sq]
  change M^2*e/d/(M^2*q) = e/(d*q)
  field_simp [mass_pos.ne', head_poly_pos.ne', source_poly_pos.ne']

/-- The uncorrected even rank-four seam determinant is strictly negative for the actual source. -/
theorem thetaCuspNativeEvenFourDet_zero_neg : thetaCuspNativeEvenFourDet 0 < 0 := by
  have h := HTGeometry.modularThetaEvenSeamFour_lower_reserve
    thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le
  have hden := mul_pos head_poly_pos source_poly_pos
  have he : e < 0 := by dsimp [e, d, q, X] at hden ⊢; nlinarith
  rw [thetaCuspNativeEvenFourDet_zero_eq_polynomial]
  exact mul_neg_of_pos_of_neg (pow_pos mass_pos 8) he

/-- The exact new native scalar is negative at the seam, despite the strict leading head. -/
theorem thetaCuspNativeEvenFourSchur_zero_neg : thetaCuspNativeEvenFourSchur 0 < 0 := by
  have hd := thetaCuspNativeEvenFourDet_eq_head_mul_schur (x := 0) le_rfl
  by_contra hn
  have h := mul_nonneg thetaCuspNativeEvenHead_zero_posDef.det_pos.le (le_of_not_gt hn)
  rw [← hd] at h
  exact (not_lt_of_ge h) thetaCuspNativeEvenFourDet_zero_neg

/-- The source mass cancels completely from the canonical even compensation coefficient. -/
theorem thetaCuspNativeEvenCompensationCoefficient_eq_modularRatio :
    thetaCuspNativeEvenCompensationCoefficient = 1 -
      HTGeometry.modularThetaEvenSeamFourPolynomial (thetaCuspSelfDualModularScale^2) /
        (HTGeometry.modularThetaEvenSeamHeadPolynomial (thetaCuspSelfDualModularScale^2) *
          HTGeometry.modularThetaEvenSeamMomentPolynomial 0 (thetaCuspSelfDualModularScale^2)) := by
  rw [← thetaCuspNativeEvenFourSchur_zero_div_source_sq]
  unfold thetaCuspNativeEvenCompensationCoefficient
  rw [abs_of_neg thetaCuspNativeEvenFourSchur_zero_neg]
  field_simp [(thetaCuspFullSource_pos_all 0).ne']
  ring

/-- Exact rational coefficient band, derived from the complete modular source and polynomial reserves. -/
theorem thetaCuspNativeEvenCompensationCoefficient_bounds :
    1000000000000 < thetaCuspNativeEvenCompensationCoefficient ∧
      thetaCuspNativeEvenCompensationCoefficient < 3000000000000 := by
  have hl := HTGeometry.modularThetaEvenSeamFour_lower_reserve
    thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le
  have hu := HTGeometry.modularThetaEvenSeamFour_upper_reserve
    thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le
    thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths.le
  have hden : 0 < d*q := mul_pos head_poly_pos source_poly_pos
  have hlo : (1000000000000 : ℝ) < -e/(d*q) := by
    apply (lt_div_iff₀ hden).mpr
    dsimp [d, e, q, X]
    nlinarith only [hl]
  have hhi : -e/(d*q) < (3000000000000 : ℝ)-1 := by
    apply (div_lt_iff₀ hden).mpr
    dsimp [d, e, q, X]
    nlinarith only [hu]
  have heq : thetaCuspNativeEvenCompensationCoefficient = 1+(-e)/(d*q) := by
    rw [thetaCuspNativeEvenCompensationCoefficient_eq_modularRatio]
    change 1-e/(d*q) = 1+(-e)/(d*q)
    ring
  constructor <;> nlinarith only [hlo, hhi, heq]

/-- Every coefficient above the rational lower endpoint strictly repairs the actual seam. -/
theorem thetaCuspNativeEvenFourCompensated_zero_posDef_of_coefficient_lower
    {C : ℝ} (hC : 1000000000000 ≤ C) :
    (thetaCuspNativeEvenFourCompensated C 0).PosDef := by
  rw [thetaCuspNativeEvenFourCompensated_posDef_iff le_rfl]
  have hp := sq_pos_of_pos (thetaCuspFullSource_pos_all 0)
  have hupper := mul_lt_mul_of_pos_right thetaCuspNativeEvenCompensationCoefficient_bounds.2 hp
  have hCmul := mul_le_mul_of_nonneg_right hC hp.le
  have hid : thetaCuspNativeEvenCompensationCoefficient*thetaCuspFullSource 0^2 =
      -thetaCuspNativeEvenFourSchur 0 + thetaCuspFullSource 0^2 := by
    unfold thetaCuspNativeEvenCompensationCoefficient
    rw [abs_of_neg thetaCuspNativeEvenFourSchur_zero_neg]
    field_simp [(thetaCuspFullSource_pos_all 0).ne']
  norm_num [thetaCuspCenterCompensationSource]
  nlinarith only [hp, hupper, hCmul, hid]

end
end RHTower

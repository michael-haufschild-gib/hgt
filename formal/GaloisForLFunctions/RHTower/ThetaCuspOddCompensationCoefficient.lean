import GaloisForLFunctions.RHTower.ThetaCuspNativeOddSchurCompensation

/-!
# Exact bounds on the source-selected odd compensation coefficient

The literal seam mass cancels from the canonical coefficient. Two symbolic
polynomial reserves on the proved modular scale interval give unconditional
rational bounds, without numerical source evaluation.
-/

namespace RHTower
noncomputable section

/-- The source at the self-dual seam is mass times the positive normalized coordinate. -/
theorem thetaCuspFullSource_zero_eq_modularScale :
    thetaCuspFullSource 0 = thetaCuspSelfDualThetaMass *
      ((thetaCuspSelfDualModularScale^(2 : ℕ)-6)/16) := by
  have h := ofReal_thetaCuspFullSource_eq_modularMass_mul_sourcePositiveQ 0
  have hQ := congrFun thetaCuspModularSourcePositiveState_zero_eq_seam
    HTGeometry.ModularThetaSourcePositiveState.Q
  rw [hQ, thetaCuspModularODEState_H_eq_completedThetaProfile] at h
  apply Complex.ofReal_injective
  simpa [HTGeometry.modularThetaSourcePositiveSeamState,
    Bottcher.completedThetaProfile, thetaCuspSelfDualThetaMass] using h

/-- Existing second--sixth closure is exactly the leading odd determinant. -/
theorem thetaCuspNativeOddHeadDet_zero_eq_modularClosure :
    thetaCuspNativeOddHeadDet 0 = 4*thetaCuspSelfDualThetaMass^(4 : ℕ) *
      thetaCuspReflectedSixthSeamModularPolynomial (thetaCuspSelfDualModularScale^(2 : ℕ)) := by
  have heq : thetaCuspNativeOddHeadDet 0 =
      thetaCuspFullSourceReflectionSecondSixthCurvature 0 := by
    unfold thetaCuspNativeOddHeadDet
    rw [thetaCuspNativeReflectionJet_two, thetaCuspNativeReflectionJet_four,
      thetaCuspNativeReflectionJet_six]
    unfold thetaCuspSourceReflectionJetTwo thetaCuspSourceReflectionJetFour
      thetaCuspSourceReflectionJetSix thetaCuspFullSourceReflectionSecondSixthCurvature
      HilbertMetric.reflectedProductSecondJet HilbertMetric.reflectedProductFourthJet
    simp only [iteratedDeriv_zero, neg_mul_neg]
  rw [heq, thetaCuspFullSourceReflectionSecondSixthCurvature_zero_eq,
    thetaCuspReflectedSixthSeamModularClosureValue]
  ring

/-- The canonical correction is an exact rational function of the squared seam scale. -/
theorem thetaCuspNativeOddCompensationCoefficient_eq_modularRatio :
    thetaCuspNativeOddCompensationCoefficient =
      -HTGeometry.modularThetaReflectedTenthSeamPolynomial (thetaCuspSelfDualModularScale^(2 : ℕ)) /
        (thetaCuspReflectedSixthSeamModularPolynomial (thetaCuspSelfDualModularScale^(2 : ℕ)) *
          (thetaCuspSelfDualModularScale^(2 : ℕ)-6)^(2 : ℕ) / 64) := by
  have hm : thetaCuspSelfDualThetaMass ≠ 0 := by
    have := thetaCuspSelfDualThetaMass_gt_five_thousand_four_hundred_thirty_one_div_five_thousand
    linarith
  unfold thetaCuspNativeOddCompensationCoefficient
  rw [thetaCuspNativeOddHankelThreeDet_zero_eq_modularClosure,
    thetaCuspNativeOddHeadDet_zero_eq_modularClosure,
    thetaCuspFullSource_zero_eq_modularScale]
  field_simp
  ring

/-- Exact positive reserve for the lower coefficient bound on the physical scale box. -/
private theorem compensationSeam_lower_reserve
    {X : ℝ} (hlo : (191/10 : ℝ) ≤ X) (hhi : X ≤ 20) :
    0 < -HTGeometry.modularThetaReflectedTenthSeamPolynomial X - 1000000000*(thetaCuspReflectedSixthSeamModularPolynomial X * (X-6)^(2 : ℕ) / 64) := by
  let y := X - (191/10 : ℝ)
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hy1 : y ≤ 1 := by dsimp [y]; linarith
  have hp (n : ℕ) : 0 ≤ 1-y^n := sub_nonneg.mpr (pow_le_one₀ hy hy1)
  have hp10 := hp 10
  have hp11 := hp 11
  have hp12 := hp 12
  have hp13 := hp 13
  have hp14 := hp 14
  have hp15 := hp 15
  have hid : -HTGeometry.modularThetaReflectedTenthSeamPolynomial X - 1000000000*(thetaCuspReflectedSixthSeamModularPolynomial X * (X-6)^(2 : ℕ) / 64) =
    (964765569005248220537824180103039457303 / 879609302220800000000000) +
    (186056763894955114473665587353297944079 / 87960930222080000000000) * y^(1 : ℕ) +
    (9182153562111083510655837131584954431 / 8796093022208000000000) * y^(2 : ℕ) +
    (228456610449591613874923703900801943 / 879609302220800000000) * y^(3 : ℕ) +
    (3490883916071068548312242882094531 / 87960930222080000000) * y^(4 : ℕ) +
    (35731731697136122123552042590939 / 8796093022208000000) * y^(5 : ℕ) +
    (254769014602413306612905628123 / 879609302220800000) * y^(6 : ℕ) +
    (1272386417027346239933284947 / 87960930222080000) * y^(7 : ℕ) +
    (4276923902873393345054181 / 8796093022208000) * y^(8 : ℕ) +
    (8086692510190312679757 / 879609302220800) * y^(9 : ℕ) +
    (1421652024369451011 / 87960930222080) * (1-y^(10 : ℕ)) +
    (59484862171607931 / 8796093022208) * (1-y^(11 : ℕ)) +
    (930978403404795 / 4398046511104) * (1-y^(12 : ℕ)) +
    (7596952502175 / 2199023255552) * (1-y^(13 : ℕ)) +
    (33695674875 / 1099511627776) * (1-y^(14 : ℕ)) +
    (64029375 / 549755813888) * (1-y^(15 : ℕ)) := by
    dsimp [y, HTGeometry.modularThetaReflectedTenthSeamPolynomial,
      thetaCuspReflectedSixthSeamModularPolynomial]
    ring
  rw [hid]
  positivity

/-- Exact positive reserve for the upper coefficient bound on the physical scale box. -/
private theorem compensationSeam_upper_reserve
    {X : ℝ} (hlo : (191/10 : ℝ) ≤ X) (hhi : X ≤ 20) :
    0 < 3000000000*(thetaCuspReflectedSixthSeamModularPolynomial X * (X-6)^(2 : ℕ) / 64) + HTGeometry.modularThetaReflectedTenthSeamPolynomial X := by
  let y := X - (191/10 : ℝ)
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hy1 : y ≤ 1 := by dsimp [y]; linarith
  have hp (n : ℕ) : 0 ≤ 1-y^n := sub_nonneg.mpr (pow_le_one₀ hy hy1)
  have hp2 := hp 2
  have hp3 := hp 3
  have hp4 := hp 4
  have hp5 := hp 5
  have hp6 := hp 6
  have hp7 := hp 7
  have hp8 := hp 8
  have hp9 := hp 9
  have hid : 3000000000*(thetaCuspReflectedSixthSeamModularPolynomial X * (X-6)^(2 : ℕ) / 64) + HTGeometry.modularThetaReflectedTenthSeamPolynomial X =
    (2562161187190397827928668433894930946597 / 879609302220800000000000) +
    (19687594619393634849373132646702055921 / 87960930222080000000000) * y^(1 : ℕ) +
    (4903033628103560447165277131584954431 / 8796093022208000000000) * (1-y^(2 : ℕ)) +
    (179131600238193667220203703900801943 / 879609302220800000000) * (1-y^(3 : ℕ)) +
    (3153047628950508973272242882094531 / 87960930222080000000) * (1-y^(4 : ℕ)) +
    (34406844521950714123552042590939 / 8796093022208000000) * (1-y^(5 : ℕ)) +
    (252624961456219386612905628123 / 879609302220800000) * (1-y^(6 : ℕ)) +
    (1276631397312786239933284947 / 87960930222080000) * (1-y^(7 : ℕ)) +
    (4304175891353393345054181 / 8796093022208000) * (1-y^(8 : ℕ)) +
    (8135783070190312679757 / 879609302220800) * (1-y^(9 : ℕ)) +
    (1390932024369451011 / 87960930222080) * y^(10 : ℕ) +
    (59484862171607931 / 8796093022208) * y^(11 : ℕ) +
    (930978403404795 / 4398046511104) * y^(12 : ℕ) +
    (7596952502175 / 2199023255552) * y^(13 : ℕ) +
    (33695674875 / 1099511627776) * y^(14 : ℕ) +
    (64029375 / 549755813888) * y^(15 : ℕ) := by
    dsimp [y, HTGeometry.modularThetaReflectedTenthSeamPolynomial,
      thetaCuspReflectedSixthSeamModularPolynomial]
    ring
  rw [hid]
  positivity

/-- Unconditional rational bounds on the literal source-selected compensation coefficient. -/
theorem thetaCuspNativeOddCompensationCoefficient_bounds :
    1000000000 < thetaCuspNativeOddCompensationCoefficient ∧
      thetaCuspNativeOddCompensationCoefficient < 3000000000 := by
  have hlo := thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le
  have hhi := thetaCuspSelfDualModularScale_sq_lt_twenty.le
  have hs : 0 < thetaCuspSelfDualModularScale^(2 : ℕ)-6 := by linarith
  have hd : 0 < thetaCuspReflectedSixthSeamModularPolynomial
      (thetaCuspSelfDualModularScale^(2 : ℕ)) * (thetaCuspSelfDualModularScale^(2 : ℕ)-6)^(2 : ℕ) / 64 :=
    div_pos (mul_pos thetaCuspReflectedSixthSeamModularPolynomial_source_pos
      (sq_pos_of_pos hs)) (by norm_num)
  have hl := compensationSeam_lower_reserve hlo hhi
  have hu := compensationSeam_upper_reserve hlo hhi
  rw [thetaCuspNativeOddCompensationCoefficient_eq_modularRatio]
  constructor
  · apply (lt_div_iff₀ hd).2
    linarith
  · apply (div_lt_iff₀ hd).2
    linarith

end
end RHTower

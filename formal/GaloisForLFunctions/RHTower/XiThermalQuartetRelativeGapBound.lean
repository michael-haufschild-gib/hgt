import GaloisForLFunctions.RHTower.PrimeArchExactOffLineQuartetAccretivity

/-!
# Four-orbit sharpening of the Xi thermal source gap

The transverse reciprocal-square coordinate vanishes identically on the critical line.  Hence its
relative thermal estimate only needs a height bound on off-line atoms.  Charging all four distinct
functional-equation--Schwarz copies improves the relevant height floor from
`C⁻¹ - 1` to `4 * C⁻¹ - 1`.  The exact source-dependent orientation factor becomes

`16 * C * (4 - C) / (16 - 5 * C)^(2 : ℕ)`,

which is strictly below `1 / 84` under the certified endpoint bound `C < 93 / 2000`.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The exact orientation factor after the off-line FE--Schwarz quartet is charged as one orbit. -/
def xiThermalQuartetRelativeOrientationFactor : ℝ :=
  16 * xiEndpointCompletedCurvature * (4 - xiEndpointCompletedCurvature) /
    (16 - 5 * xiEndpointCompletedCurvature) ^ (2 : ℕ)

theorem xiThermalQuartetRelativeOrientationFactor_eq_boundaryRatio :
    xiThermalQuartetRelativeOrientationFactor =
      ((4 - xiEndpointCompletedCurvature) / xiEndpointCompletedCurvature) /
        ((4 - xiEndpointCompletedCurvature) / xiEndpointCompletedCurvature - 1 / 4) ^ (2 : ℕ) := by
  have hCne := xiEndpointCompletedCurvature_pos.ne'
  unfold xiThermalQuartetRelativeOrientationFactor
  field_simp [hCne]
  ring

theorem xiThermalQuartetRelativeOrientationFactor_nonneg :
    0 ≤ xiThermalQuartetRelativeOrientationFactor := by
  unfold xiThermalQuartetRelativeOrientationFactor
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) xiEndpointCompletedCurvature_pos.le)
      (sub_nonneg.mpr (by
        exact xiEndpointCompletedCurvature_lt_one_half.le.trans (by norm_num))))
    (sq_nonneg _)

/-- The quartet-selected factor is below one eighty-fourth. -/
theorem xiThermalQuartetRelativeOrientationFactor_lt_one_eightyFourth :
    xiThermalQuartetRelativeOrientationFactor < 1 / 84 := by
  let c : ℝ := xiEndpointCompletedCurvature
  let c₀ : ℝ := 93 / 2000
  have hc0 : 0 < c := by simpa only [c] using xiEndpointCompletedCurvature_pos
  have hc : c < c₀ := by
    simpa only [c, c₀] using
      xiEndpointCompletedCurvature_lt_ninetyThree_over_twoThousand
  have hden : 0 < 16 - 5 * c := by
    dsimp only [c₀] at hc
    nlinarith
  have hgap : 0 < c₀ - c := sub_pos.mpr hc
  have hlinear : 0 < 5536 - 1369 * (c₀ + c) := by
    dsimp only [c₀] at hc ⊢
    nlinarith
  have hproduct : 0 < (c₀ - c) * (5536 - 1369 * (c₀ + c)) :=
    mul_pos hgap hlinear
  have hbase : 0 < 256 - 5536 * c₀ + 1369 * c₀ ^ (2 : ℕ) := by
    dsimp only [c₀]
    norm_num
  have hpoly : 0 < 256 - 5536 * c + 1369 * c ^ (2 : ℕ) := by
    nlinarith [hproduct, hbase]
  unfold xiThermalQuartetRelativeOrientationFactor
  change 16 * c * (4 - c) / (16 - 5 * c) ^ (2 : ℕ) < 1 / 84
  rw [div_lt_iff₀ (sq_pos_of_pos hden)]
  nlinarith

theorem xiThermalQuartetRelativeOrientationFactor_lt_one :
    xiThermalQuartetRelativeOrientationFactor < 1 :=
  xiThermalQuartetRelativeOrientationFactor_lt_one_eightyFourth.trans (by norm_num)

/-- **Quartet atomwise orientation estimate.**  On-line atoms contribute zero transverse energy;
off-line atoms obey the four-charge height floor. -/
theorem xiThermalOrientationTerm_le_quartetRelativeFactor_node_sq (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ (2 : ℕ) ≤
      xiThermalQuartetRelativeOrientationFactor * xiThermalNode q ^ (2 : ℕ) := by
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have hfactor := xiThermalQuartetRelativeOrientationFactor_nonneg
    rw [xiZeroCopyReciprocalSquare_im_formula, hon]
    norm_num
    exact mul_nonneg hfactor (sq_nonneg (xiThermalNode q))
  let c : ℝ := xiEndpointCompletedCurvature
  let a : ℝ := (4 - c) / c
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)
  let v : ℝ := (q.1 : ℂ).im ^ (2 : ℕ)
  let D : ℝ := (u + v) ^ (2 : ℕ)
  have hc0 : 0 < c := by simpa only [c] using xiEndpointCompletedCurvature_pos
  have hc : c < 93 / 2000 := by
    simpa only [c] using
      xiEndpointCompletedCurvature_lt_ninetyThree_over_twoThousand
  have ha : 1 / 4 < a := by
    dsimp [a]
    rw [lt_div_iff₀ hc0]
    nlinarith
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu : u ≤ 1 / 4 :=
    (xi_divisor_support_centered_re_sq_lt_quarter q.1).le
  have hv : a ≤ v := by
    have hfour :=
      four_le_endpointCurvature_mul_one_add_im_sq_of_offLine q hon
    dsimp [a, c, v]
    rw [div_le_iff₀ hc0]
    nlinarith
  have hD : 0 < D := by
    dsimp [D, u, v]
    positivity
  have hratio :=
    four_mul_u_mul_v_le_boundary_ratio hu0 hu ha hv
  rw [xiThermalNode, xiZeroCopyReciprocalSquare_re_formula,
    xiZeroCopyReciprocalSquare_im_formula]
  change (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im /
        (((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ)) ^ (2 : ℕ)) ^ (2 : ℕ) ≤
    xiThermalQuartetRelativeOrientationFactor *
      (((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) /
        (((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ)) ^ (2 : ℕ)) ^ (2 : ℕ)
  rw [show ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) = u by rfl,
    show (q.1 : ℂ).im ^ (2 : ℕ) = v by rfl,
    show (u + v) ^ (2 : ℕ) = D by rfl,
    xiThermalQuartetRelativeOrientationFactor_eq_boundaryRatio]
  change (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im / D) ^ (2 : ℕ) ≤
    (a / (a - 1 / 4) ^ (2 : ℕ)) * ((v - u) / D) ^ (2 : ℕ)
  rw [div_pow, div_pow]
  rw [show (a / (a - 1 / 4) ^ (2 : ℕ)) * ((v - u) ^ (2 : ℕ) / D ^ (2 : ℕ)) =
      ((a / (a - 1 / 4) ^ (2 : ℕ)) * (v - u) ^ (2 : ℕ)) / D ^ (2 : ℕ) by ring]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hD)).2
  calc
    (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) = 4 * u * v := by
      dsimp [u, v]
      ring
    _ ≤ (a / (a - 1 / 4) ^ (2 : ℕ)) * (v - u) ^ (2 : ℕ) := hratio

/-- The global thermal orientation energy obeys the exact four-orbit factor. -/
theorem xiThermalOrientationEnergy_le_quartetRelativeFactor_secondMoment :
    xiThermalOrientationEnergy ≤
      xiThermalQuartetRelativeOrientationFactor * xiThermalSecondMoment := by
  rw [xiThermalOrientationEnergy, xiThermalSecondMoment, ← tsum_mul_left]
  exact summable_xiThermalOrientationTerm.tsum_le_tsum
    (fun q => xiThermalOrientationTerm_le_quartetRelativeFactor_node_sq q)
    (summable_xiThermalNode_sq.mul_left xiThermalQuartetRelativeOrientationFactor)

/-- **One-eighty-fourth transverse-energy theorem.** -/
theorem xiThermalOrientationEnergy_lt_one_eightyFourth_secondMoment :
    xiThermalOrientationEnergy < (1 / 84 : ℝ) * xiThermalSecondMoment := by
  exact xiThermalOrientationEnergy_le_quartetRelativeFactor_secondMoment.trans_lt
    (mul_lt_mul_of_pos_right
      xiThermalQuartetRelativeOrientationFactor_lt_one_eightyFourth
      xiThermalSecondMoment_pos)

/-- The explicit prime--archimedean source retains more than `83 / 84` of the thermal mass. -/
theorem eightyThree_over_eightyFour_thermalSecondMoment_lt_source :
    (83 / 84 : ℝ) * xiThermalSecondMoment < normalizedPrimeArchMoment 1 := by
  have hgap := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  have horientation := xiThermalOrientationEnergy_lt_one_eightyFourth_secondMoment
  nlinarith

/-- The positive thermal moment lies within the strict factor `84 / 83` of the source value. -/
theorem xiThermalSecondMoment_lt_eightyFour_over_eightyThree_source :
    xiThermalSecondMoment < (84 / 83 : ℝ) * normalizedPrimeArchMoment 1 := by
  nlinarith [eightyThree_over_eightyFour_thermalSecondMoment_lt_source]

theorem eightyThree_over_eightyFour_thermalSecondMoment_lt_bornWittenSource :
    (83 / 84 : ℝ) * xiThermalSecondMoment <
      thetaCuspBornWittenQuadraticSource := by
  rw [← normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource]
  exact eightyThree_over_eightyFour_thermalSecondMoment_lt_source

theorem xiThermalSecondMoment_lt_eightyFour_over_eightyThree_bornWittenSource :
    xiThermalSecondMoment <
      (84 / 83 : ℝ) * thetaCuspBornWittenQuadraticSource := by
  rw [← normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource]
  exact xiThermalSecondMoment_lt_eightyFour_over_eightyThree_source

end

end RHTower

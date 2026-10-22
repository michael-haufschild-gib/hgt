import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenCompactSourceCoordinates
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactDeterminant
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenFourExplicitTail

/-! # Explicit complete-source even rank-four positivity through the energy interval -/
namespace RHTower
noncomputable section
open Set

private abbrev u := thetaCuspModularMassDrift
private abbrev a := thetaCuspModularGapAmplitude
private abbrev w := thetaCuspModularTransverseShear
private abbrev M := Bottcher.completedThetaProfile

/-- The full native determinant with its exact correction cofactor has a positive compact reserve. -/
theorem thetaCuspNativeEvenFourCompensated_compact_reserve {C x : ℝ}
    (hC : 1000000000000 ≤ C) (hx : x ∈ Icc (0 : ℝ) (8/95)) :
    1000000000000000000000*M x^8 ≤ thetaCuspNativeEvenFourDet x+
      C*thetaCuspCenterCompensationSource x*(thetaCuspNativeEvenHead x).det := by
  obtain ⟨t, v, ht, hv, ha, hw⟩ := exists_thetaCuspModularState_even_unit_coordinates hx
  change a x = HTGeometry.evenCompactUnitGap (u x^2) t at ha
  have hb := thetaCuspModularState_energy_box hx
  have hu2 : u x^2 ≤ 1 := by nlinarith [hb.1, hb.2.1]
  have hp := HTGeometry.evenCompactUnitDet_lower (sq_nonneg (u x)) hu2 ht.1 ht.2 hv.1 hv.2
  rw [thetaCuspEvenCompactUnitDet_eq_source_ratio ha hw] at hp
  have hden : 0 < (100 : ℝ)^12*M x^8 := by
    have hm := thetaCuspCompletedThetaProfile_pos x
    positivity
  have hl := (le_div_iff₀ hden).mp hp
  norm_num at hl
  have hQ : HTGeometry.oddCompactSourceZero (u x) (a x) =
      HTGeometry.evenCompactUnitSourceZero (u x^2) t := by
    rw [ha]
    rfl
  have hg := thetaCuspCenterCompensationSource_even_compact_lower hx
  rw [hQ] at hg
  change M x^2*HTGeometry.evenCompactUnitCorrection (u x^2) t ≤
    thetaCuspCenterCompensationSource x at hg
  have hh := (thetaCuspNativeEvenHead_posDef hx.1).det_pos
  have hfixed := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ (1000000000000 : ℝ)*(thetaCuspNativeEvenHead x).det by positivity)
  have hG : 0 ≤ thetaCuspCenterCompensationSource x :=
    (sq_nonneg (M x)).trans (thetaCuspCenterCompensationSource_ge_mass_sq_on_energy_interval hx)
  have hcoeff := mul_le_mul_of_nonneg_right hC
    (mul_nonneg hG hh.le)
  nlinarith only [hl, hfixed, hcoeff]

/-- Every coefficient at least one trillion repairs the full even block through eight ninety-fifths. -/
theorem thetaCuspNativeEvenFourCompensated_posDef_on_energy_interval {C x : ℝ}
    (hC : 1000000000000 ≤ C) (hx : x ∈ Icc (0 : ℝ) (8/95)) :
    (thetaCuspNativeEvenFourCompensated C x).PosDef := by
  have hr := thetaCuspNativeEvenFourCompensated_compact_reserve hC hx
  have hm := thetaCuspCompletedThetaProfile_pos x
  have hp : 0 < thetaCuspNativeEvenFourDet x+
      C*thetaCuspCenterCompensationSource x*(thetaCuspNativeEvenHead x).det :=
    (by positivity : 0 < 1000000000000000000000*M x^8).trans_le hr
  rw [thetaCuspNativeEvenFourDet_eq_head_mul_schur hx.1] at hp
  have hh := (thetaCuspNativeEvenHead_posDef hx.1).det_pos
  apply (thetaCuspNativeEvenFourCompensated_posDef_iff hx.1 C).mpr
  apply (mul_pos_iff_of_pos_left hh).mp
  nlinarith only [hp]

/-- Both physical center endpoints are explicit for the entire proved rational coefficient band. -/
theorem thetaCuspNativeEvenFourCompensated_posDef_outside_explicit_gap {C x : ℝ}
    (hCL : 1000000000000 ≤ C) (hCU : C ≤ 3000000000000) (hx : 0 ≤ x)
    (h : x ≤ 8/95 ∨ 6/5 ≤ x) :
    (thetaCuspNativeEvenFourCompensated C x).PosDef := by
  rcases h with h | h
  · exact thetaCuspNativeEvenFourCompensated_posDef_on_energy_interval hCL ⟨hx, h⟩
  · exact thetaCuspNativeEvenFourCompensated_posDef_on_explicit_tail (by linarith) hCU h

/-- Closed canonical source positivity outside the explicitly bounded remaining interior. -/
theorem thetaCuspNativeEvenFourCanonical_posDef_outside_explicit_gap :
    ∀ x : ℝ, 0 ≤ x → (x ≤ 8/95 ∨ 6/5 ≤ x) →
      (thetaCuspNativeEvenFourCompensated thetaCuspNativeEvenCompensationCoefficient x).PosDef := by
  intro x hx h
  exact thetaCuspNativeEvenFourCompensated_posDef_outside_explicit_gap
    thetaCuspNativeEvenCompensationCoefficient_bounds.1.le
    thetaCuspNativeEvenCompensationCoefficient_bounds.2.le hx h

/-- The actual weighted source has the same explicit compact gap at every positive aperture. -/
theorem thetaCuspCenterCorrectedEvenFourCanonical_posDef_outside_explicit_gap :
    ∀ a r : ℝ, 0 < a → 0 < r → (r ≤ 16/95 ∨ 12/5 ≤ r) →
      (thetaCuspCenterCorrectedEvenFour a thetaCuspNativeEvenCompensationCoefficient r).PosDef := by
  intro a r ha hr h
  apply thetaCuspCenterCorrectedEvenFour_posDef_of_source ha
    thetaCuspNativeEvenCompensationCoefficient_pos.le hr
  apply thetaCuspNativeEvenFourCanonical_posDef_outside_explicit_gap (r/2) (by positivity)
  rcases h with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

end
end RHTower

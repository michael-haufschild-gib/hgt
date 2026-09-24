import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactDeterminant
import GaloisForLFunctions.RHTower.ThetaCuspEvenCompactSourceCoordinates
import GaloisForLFunctions.RHTower.ThetaCuspEvenCompactCorrection
import GaloisForLFunctions.RHTower.ThetaCuspEvenFourMiddle

open Set
namespace RHTower
noncomputable section

/-- The literal compact modular source has a strict rank-four completion at the fixed coefficient. -/
theorem thetaCuspNativeEvenFourFixed_posDef_of_compact {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (8 / 95)) :
    (thetaCuspNativeEvenFourCompensated 1000000000000 x).PosDef := by
  let u := thetaCuspModularMassDrift x
  let M := Bottcher.completedThetaProfile x
  obtain ⟨t, v, ht, hv, ha, hw⟩ :=
    exists_thetaCuspModularState_even_unit_coordinates hx
  have hstate := thetaCuspModularState_coupled_even_tube hx
  have hu0 : 0 ≤ u := hstate.1
  have hu1 : u ≤ 1 := hstate.2.1
  have hr0 : 0 ≤ u ^ (2 : ℕ) := sq_nonneg _
  have hr1 : u ^ (2 : ℕ) ≤ 1 := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  have ha' : thetaCuspModularGapAmplitude x =
      HTGeometry.evenCompactUnitGap (u ^ (2 : ℕ)) t := by
    simpa [HTGeometry.evenCompactUnitGap, u] using ha
  have hw' : thetaCuspModularTransverseShear x = u * (1 + v / 4) := hw
  have hdet := HTGeometry.evenCompactUnitDet_lower hr0 hr1 ht.1 ht.2 hv.1 hv.2
  have hratio := thetaCuspEvenCompactUnitDet_eq_source_ratio ha' hw'
  have hq : HTGeometry.oddCompactSourceZero u
      (thetaCuspModularGapAmplitude x) =
        HTGeometry.evenCompactUnitSourceZero (u ^ (2 : ℕ)) t := by
    rw [ha']
    unfold HTGeometry.oddCompactSourceZero HTGeometry.evenCompactUnitSourceZero
    ring
  have hG0 := thetaCuspCenterCompensationSource_even_compact_lower hx
  have hG : M ^ (2 : ℕ) *
      HTGeometry.evenCompactUnitCorrection (u ^ (2 : ℕ)) t ≤
        thetaCuspCenterCompensationSource x := by
    rw [hq] at hG0
    simpa only [HTGeometry.evenCompactUnitCorrection, M, u] using hG0
  have hM : 0 < M := by simpa only [M] using thetaCuspCompletedThetaProfile_pos x
  have hden : 0 < (100 : ℝ) ^ (12 : ℕ) * M ^ (8 : ℕ) := by positivity
  have hhead : 0 < (thetaCuspNativeEvenHead x).det :=
    (thetaCuspNativeEvenHead_posDef hx.1).det_pos
  have hnum : 0 < thetaCuspNativeEvenFourDet x +
      1000000000000 * M ^ (2 : ℕ) *
        HTGeometry.evenCompactUnitCorrection (u ^ (2 : ℕ)) t *
          (thetaCuspNativeEvenHead x).det := by
    rw [hratio] at hdet
    have hp : 0 < (thetaCuspNativeEvenFourDet x +
        1000000000000 * M ^ (2 : ℕ) *
          HTGeometry.evenCompactUnitCorrection (u ^ (2 : ℕ)) t *
            (thetaCuspNativeEvenHead x).det) /
              ((100 : ℝ) ^ (12 : ℕ) * M ^ (8 : ℕ)) := by
      exact (by norm_num : (0 : ℝ) < 1 / 1000).trans_le hdet
    exact (div_pos_iff_of_pos_right hden).mp hp
  have hmon : 1000000000000 * M ^ (2 : ℕ) *
      HTGeometry.evenCompactUnitCorrection (u ^ (2 : ℕ)) t *
        (thetaCuspNativeEvenHead x).det ≤
          1000000000000 * thetaCuspCenterCompensationSource x *
            (thetaCuspNativeEvenHead x).det := by
    have hh := mul_le_mul_of_nonneg_right hG
      (show 0 ≤ (1000000000000 : ℝ) * (thetaCuspNativeEvenHead x).det by positivity)
    nlinarith only [hh]
  have hnum' : 0 < thetaCuspNativeEvenFourDet x +
      1000000000000 * thetaCuspCenterCompensationSource x *
        (thetaCuspNativeEvenHead x).det :=
    lt_of_lt_of_le hnum (by nlinarith only [hmon])
  rw [thetaCuspNativeEvenFourDet_eq_head_mul_schur hx.1] at hnum'
  have hprod : 0 < (thetaCuspNativeEvenHead x).det *
      (thetaCuspNativeEvenFourSchur x +
        1000000000000 * thetaCuspCenterCompensationSource x) := by
    nlinarith only [hnum']
  have hs : 0 < thetaCuspNativeEvenFourSchur x +
      1000000000000 * thetaCuspCenterCompensationSource x :=
    (mul_pos_iff_of_pos_left hhead).mp hprod
  rw [thetaCuspNativeEvenFourCompensated_posDef_iff hx.1]
  exact hs

/-- The fixed zero-flux compensation is positive at every nonnegative source center. -/
theorem thetaCuspNativeEvenFourFixed_posDef {x : ℝ} (hx : 0 ≤ x) :
    (thetaCuspNativeEvenFourCompensated 1000000000000 x).PosDef := by
  by_cases hsmall : x ≤ 8 / 95
  · exact thetaCuspNativeEvenFourFixed_posDef_of_compact ⟨hx, hsmall⟩
  · exact thetaCuspNativeEvenFourFixed_posDef_of_twelfth_le
      (by linarith : (1 / 12 : ℝ) ≤ x)

end
end RHTower

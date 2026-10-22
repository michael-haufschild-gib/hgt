import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactDeterminant
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenCompactSourceCoordinates
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenCompactCorrection
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenFourMiddle
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenFourCenterIntegration
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedSixthRank
import GaloisForLFunctions.HTGeometry.PSDMatrixSpectralHankel

open MeasureTheory Set Matrix
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

/-- The zero-flux fixed compensation makes the actual even rank-seven block
positive semidefinite after center integration. -/
theorem thetaCuspCenterMixedSignedHankel_seven_even_posSemidef
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ((thetaCuspCenterMixedSignedHankel a 7).submatrix
      (fun i : Fin 4 => (⟨2 * i.val, by omega⟩ : Fin 7))
      (fun i : Fin 4 => (⟨2 * i.val, by omega⟩ : Fin 7))).PosSemidef := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let K : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun r =>
    if 0 < r then thetaCuspCenterCorrectedEvenFour a 1000000000000 r else 0
  have hEntry : ∀ i j, Integrable (fun r => K r i j) μ := by
    intro i j
    apply (integrableOn_thetaCuspCenterCorrectedEvenFour ha0.le ha 1000000000000 i j).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    change 0 < r at hr
    simp [K, hr]
  have hK : ∀ r, (K r).PosSemidef := by
    intro r
    by_cases hr : 0 < r
    · simpa only [K, if_pos hr] using
        (thetaCuspCenterCorrectedEvenFour_posDef_of_source ha0
        (by positivity) hr
        (thetaCuspNativeEvenFourFixed_posDef (by linarith : 0 ≤ r / 2))).posSemidef
    · simpa only [K, if_neg hr] using
        (Matrix.PosSemidef.zero : (0 : Matrix (Fin 4) (Fin 4) ℝ).PosSemidef)
  have hIntegral := HTGeometry.integralMatrixKernel_posSemidef μ K hEntry hK
  have hBlock : HTGeometry.integralMatrixKernel μ K =
      (thetaCuspCenterMixedSignedHankel a 7).submatrix
        (fun i : Fin 4 => (⟨2 * i.val, by omega⟩ : Fin 7))
        (fun i : Fin 4 => (⟨2 * i.val, by omega⟩ : Fin 7)) := by
    ext i j
    have hEntryEq : (∫ r : ℝ in Ioi 0, K r i j) =
        ∫ r : ℝ in Ioi 0,
          thetaCuspCenterCorrectedEvenFour a 1000000000000 r i j := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      change 0 < r at hr
      simp [K, hr]
    change (∫ r : ℝ in Ioi 0, K r i j) =
      thetaCuspCenterMixedSignedJet a (2 * i.val + 2 * j.val)
    rw [hEntryEq, integral_thetaCuspCenterCorrectedEvenFour ha0.le ha]
    rw [show 2 * i.val + 2 * j.val = 2 * (i.val + j.val) by omega,
      thetaCuspCenterMixedSignedJet_even]
  rw [hBlock] at hIntegral
  exact hIntegral

/-- The actual seventh signed center-mixed Hankel section is nonnegative at every
critical aperture. The even block uses fixed-source zero-flux compensation;
the odd block is inherited from the strict sixth section. -/
theorem thetaCuspCenterMixedSignedHankel_seven_posSemidef
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    (thetaCuspCenterMixedSignedHankel a 7).PosSemidef := by
  let e : Fin 4 → Fin 7 := fun i => ⟨2 * i.val, by omega⟩
  let o : Fin 3 → Fin 7 := fun i => ⟨2 * i.val + 1, by omega⟩
  let o6 : Fin 3 → Fin 6 := fun i => ⟨2 * i.val + 1, by omega⟩
  have hEven : ((thetaCuspCenterMixedSignedHankel a 7).submatrix e e).PosSemidef :=
    thetaCuspCenterMixedSignedHankel_seven_even_posSemidef ha0 ha
  have ho6inj : Function.Injective o6 := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    simp only [o6] at h
    omega
  have hOdd6 : ((thetaCuspCenterMixedSignedHankel a 6).submatrix o6 o6).PosDef :=
    (thetaCuspCenterMixedSignedHankel_six_posDef ha0 ha).submatrix ho6inj
  have hOddEq : (thetaCuspCenterMixedSignedHankel a 7).submatrix o o =
      (thetaCuspCenterMixedSignedHankel a 6).submatrix o6 o6 := by
    ext i j
    rfl
  have hOdd : ((thetaCuspCenterMixedSignedHankel a 7).submatrix o o).PosSemidef := by
    rw [hOddEq]
    exact hOdd6.posSemidef
  have hHerm : (thetaCuspCenterMixedSignedHankel a 7).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [thetaCuspCenterMixedSignedHankel, add_comm]
  have ho0 := thetaCuspCenterMixedSignedJet_odd a 0
  have ho1 := thetaCuspCenterMixedSignedJet_odd a 1
  have ho2 := thetaCuspCenterMixedSignedJet_odd a 2
  have ho3 := thetaCuspCenterMixedSignedJet_odd a 3
  have ho4 := thetaCuspCenterMixedSignedJet_odd a 4
  have ho5 := thetaCuspCenterMixedSignedJet_odd a 5
  norm_num at ho0 ho1 ho2 ho3 ho4 ho5
  have hSplit (v : Fin 7 → ℝ) :
      star v ⬝ᵥ (thetaCuspCenterMixedSignedHankel a 7 *ᵥ v) =
        star (v ∘ e) ⬝ᵥ
          ((thetaCuspCenterMixedSignedHankel a 7).submatrix e e *ᵥ (v ∘ e)) +
        star (v ∘ o) ⬝ᵥ
          ((thetaCuspCenterMixedSignedHankel a 7).submatrix o o *ᵥ (v ∘ o)) := by
    simp [dotProduct, mulVec, Fin.sum_univ_succ,
      thetaCuspCenterMixedSignedHankel, e, o, ho0, ho1, ho2, ho3, ho4, ho5] <;> ring
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro v
  rw [hSplit]
  exact add_nonneg (hEven.dotProduct_mulVec_nonneg (v ∘ e))
    (hOdd.dotProduct_mulVec_nonneg (v ∘ o))

end
end RHTower

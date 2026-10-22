import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenFourEffectiveReserve
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenSeamDeterminant

/-! # An explicit complete-source Schur margin on the physical scale-thirty ray -/
namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry

private theorem head_det_eq (x : ℝ) :
    (thetaCuspNativeEvenHead x).det =
      thetaCuspNativeReflectionJet 0 x*thetaCuspNativeReflectionJet 4 x*thetaCuspNativeReflectionJet 8 x-
      thetaCuspNativeReflectionJet 0 x*(-thetaCuspNativeReflectionJet 6 x)^(2 : ℕ)-
      (-thetaCuspNativeReflectionJet 2 x)^(2 : ℕ)*thetaCuspNativeReflectionJet 8 x+
      2*(-thetaCuspNativeReflectionJet 2 x)*thetaCuspNativeReflectionJet 4 x*(-thetaCuspNativeReflectionJet 6 x)-
      thetaCuspNativeReflectionJet 4 x^(3 : ℕ) := by
  norm_num [thetaCuspNativeEvenHead, finiteHankelMatrix, Matrix.det_fin_three]
  ring

/-- Exact normalization of the reserved determinant retains the actual head cofactor. -/
theorem thetaCuspNativeEvenTailBalancedDet_eq_reserved_ratio {x : ℝ} (hx : 0 < x) :
    thetaCuspNativeEvenTailBalancedDet x =
      (thetaCuspNativeEvenFourDet x-
        100000000*thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)*
          (thetaCuspNativeEvenHead x).det) /
        ((32 : ℝ)^(12 : ℕ)*thetaCuspSourceTerm x 1^(8 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(12 : ℕ)) := by
  have hf := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))).ne'
  have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  rw [thetaCuspNativeEvenFourDet_eq, head_det_eq]
  norm_num [thetaCuspNativeEvenTailBalancedDet, thetaCuspNativeEvenTailBalanced,
    thetaCuspNativeScaledEvenJet]
  unfold hankelFourDet
  field_simp [hf, hq]
  ring

/-- The actual complete twelfth-entry Schur coordinate exceeds one hundred million in Gaussian units. -/
theorem thetaCuspNativeEvenFourSchur_effective_normalized_lower {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    100000000 < thetaCuspNativeEvenFourSchur x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)) := by
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hd : 0 < (32 : ℝ)^(12 : ℕ)*thetaCuspSourceTerm x 1^(8 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(12 : ℕ) := by positivity
  have hhead := (thetaCuspNativeEvenHead_posDef hx.le).det_pos
  have hr := thetaCuspNativeEvenTailBalancedDet_lower hq
  have hp : 0 < thetaCuspNativeEvenTailBalancedDet x := by linarith
  rw [thetaCuspNativeEvenTailBalancedDet_eq_reserved_ratio hx] at hp
  have hn := (lt_div_iff₀ hd).mp hp
  simp only [zero_mul] at hn
  rw [thetaCuspNativeEvenFourDet_eq_head_mul_schur hx.le] at hn
  have hs : 0 < thetaCuspNativeEvenFourSchur x-
      100000000*thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ) := by
    apply (mul_pos_iff_of_pos_left hhead).mp
    nlinarith only [hn]
  apply (lt_div_iff₀ (by positivity : 0 < thetaCuspSourceTerm x 1^(2 : ℕ)*
    thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ))).mpr
  nlinarith only [hs]

end
end RHTower

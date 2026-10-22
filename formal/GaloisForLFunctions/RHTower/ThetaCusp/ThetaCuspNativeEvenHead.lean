import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNativeEvenFourTail
import GaloisForLFunctions.HTGeometry.HankelSuccessorSchur

/-! # Strict even rank-three head, including the self-dual seam -/
open Filter Topology Matrix
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section

/-- The actual leading even block of the next signed source section. -/
def thetaCuspNativeEvenHead (x : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteHankelMatrix (fun k => (-1 : ℝ)^k*thetaCuspNativeReflectionJet (2*k) x) 3

theorem thetaCuspNativeEvenHead_isHermitian (x : ℝ) : (thetaCuspNativeEvenHead x).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [thetaCuspNativeEvenHead, finiteHankelMatrix, add_comm]

theorem continuous_thetaCuspNativeEvenHead : Continuous thetaCuspNativeEvenHead := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_thetaCuspNativeReflectionJet (2*(i.val+j.val))).const_mul _

/-- Positive-center head strictness is inherited from the proved native five-point section. -/
theorem thetaCuspNativeEvenHead_posDef_of_pos {x : ℝ} (hx : 0 < x) :
    (thetaCuspNativeEvenHead x).PosDef := by
  let e : Fin 3 → Fin 5 := fun i => ⟨2*i.val, by omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have := congrArg Fin.val hij
    dsimp [e] at this
    omega
  let D : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1,-1,1]
  have hD : Function.Injective D.mulVec := by
    intro v w hvw
    funext i
    have hi := congrFun hvw i
    fin_cases i <;> simpa [D, Matrix.mulVec_diagonal] using hi
  have h := ((thetaCuspNativeFivePointJet_posDef hx).submatrix he).conjTranspose_mul_mul_same hD
  convert h using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [thetaCuspNativeEvenHead, finiteHankelMatrix, e, D, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, HilbertMetric.fivePointJetMatrix]

/-- At the seam the head remains strict: a positive determinant upgrades the one-sided PSD limit. -/
theorem thetaCuspNativeEvenHead_zero_posDef : (thetaCuspNativeEvenHead 0).PosDef := by
  have hp : (thetaCuspNativeEvenHead 0).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (thetaCuspNativeEvenHead_isHermitian 0)
    intro v
    have hc : Continuous (fun x : ℝ => star v ⬝ᵥ (thetaCuspNativeEvenHead x).mulVec v) := by
      have hM := continuous_thetaCuspNativeEvenHead
      fun_prop
    have ht := (hc.continuousAt (x := 0)).tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp
      (thetaCuspNativeEvenHead_posDef_of_pos hx).posSemidef).2 v
  have hd : (thetaCuspNativeEvenHead 0).det =
      thetaCuspFullSourceReflectionEighthHankelCurvature 0 := by
    norm_num [thetaCuspNativeEvenHead, finiteHankelMatrix, Matrix.det_fin_three]
    rw [thetaCuspNativeReflectionJet_zero, thetaCuspNativeReflectionJet_two,
      thetaCuspNativeReflectionJet_four, thetaCuspNativeReflectionJet_six,
      thetaCuspNativeReflectionJet_eight]
    simp only [thetaCuspFullSourceReflectionEighthHankelCurvature,
      thetaCuspSourceReflectionJetZero, thetaCuspSourceReflectionJetTwo,
      thetaCuspSourceReflectionJetFour, thetaCuspSourceReflectionJetSix,
      thetaCuspSourceReflectionJetEight, HilbertMetric.reflectedProductSecondJet,
      HilbertMetric.reflectedProductFourthJet, HilbertMetric.signedEvenHankelThreeDet,
      iteratedDeriv_zero]
    ring
  apply hp.posDef_iff_det_ne_zero.mpr
  rw [hd]
  exact thetaCuspFullSourceReflectionEighthHankelCurvature_zero_pos.ne'

/-- No missing invertibility premise remains anywhere on the nonnegative source ray. -/
theorem thetaCuspNativeEvenHead_posDef {x : ℝ} (hx : 0 ≤ x) :
    (thetaCuspNativeEvenHead x).PosDef := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]
    exact thetaCuspNativeEvenHead_zero_posDef
  · exact thetaCuspNativeEvenHead_posDef_of_pos h

end
end RHTower

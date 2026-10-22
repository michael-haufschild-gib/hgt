import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourDiagonalTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCoupledOddTransportSchur

namespace RHTower.ThetaCuspOddDirectionTransport
noncomputable section
set_option autoImplicit false
open Filter Topology Matrix

def schurGapFrame (t : ℝ) : Matrix (Fin 4) (Fin 3) ℝ :=
  !![1,0,0; 0,1,0; 0,0,-t; 0,0,1]

theorem schurGapFrame_injective (t : ℝ) : Function.Injective (schurGapFrame t).mulVec := by
  intro v w hvw
  have h0 := congrFun hvw 0
  have h1 := congrFun hvw 1
  have h3 := congrFun hvw 3
  norm_num [schurGapFrame,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
    Matrix.cons_val_two,Matrix.cons_val_three] at h0 h1 h3
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h3

private theorem compression_det (a b c d e f g L t : ℝ) :
    ((schurGapFrame t).conjTranspose * !![a,b,c,d; b,c,d,e; c,d,e,f; d,e,f,g+L] *
      schurGapFrame t).det =
      (a*c*g-a*e^2-b^2*g+2*b*d*e-c*d^2)+L*(a*c-b^2)+
      (a*c*e-a*d^2-b^2*e+2*b*c*d-c^3)*t^2-
      2*(a*c*f-a*d*e-b^2*f+b*c*e+b*d^2-c^2*d)*t := by
  norm_num [schurGapFrame,Matrix.det_fin_three,Matrix.mul_apply,
    Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.conjTranspose_apply]
  ring

theorem schurGap_eq_compression_det (C x t : ℝ) :
    schurGap C x t =
      ((schurGapFrame t).conjTranspose * thetaCuspNativeOddFourDiagonalLoaded C x *
        schurGapFrame t).det := by
  have hm : thetaCuspNativeOddFourDiagonalLoaded C x =
      !![moment 0 x,moment 1 x,moment 2 x,moment 3 x;
         moment 1 x,moment 2 x,moment 3 x,moment 4 x;
         moment 2 x,moment 3 x,moment 4 x,moment 5 x;
         moment 3 x,moment 4 x,moment 5 x,moment 6 x+C*thetaCuspCenterCompensationSource x] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [thetaCuspNativeOddFourDiagonalLoaded,thetaCuspNativeOddFourMatrix,moment]
  rw [hm,compression_det]
  unfold schurGap cofactorA cofactorB
  have hh : thetaCuspNativeOddHeadDet x=moment 0 x*moment 2 x-(moment 1 x)^2 := by
    norm_num [moment,thetaCuspNativeOddHeadDet]
  have hd : thetaCuspNativeOddHankelThreeDet x=
      moment 0 x*moment 2 x*moment 4 x-moment 0 x*(moment 3 x)^2-
        (moment 1 x)^2*moment 4 x+2*moment 1 x*moment 2 x*moment 3 x-(moment 2 x)^3 := by
    norm_num [moment,thetaCuspNativeOddHankelThreeDet,HilbertMetric.signedEvenHankelThreeDet]
  rw [hh,hd]
  ring

theorem eventually_all_schurGap_pos (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, 0 < schurGap C x t := by
  filter_upwards [thetaCuspNativeOddFourDiagonalLoaded_posDef_eventually C] with x hx
  intro t
  rw [schurGap_eq_compression_det]
  exact (hx.conjTranspose_mul_mul_same (schurGapFrame_injective t)).det_pos

theorem eventually_transported_determinant_pos (C : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      0 < (correctedMatrix C x (direction x) (deriv direction x)).det := by
  filter_upwards [eventually_all_schurGap_pos C,eventually_gt_atTop (0:ℝ)] with x hx hx0
  exact (determinant_direction_pos_iff C hx0.le).mpr (hx (direction x))

theorem exists_all_schurGap_pos_tail (C : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, R ≤ x → ∀ t : ℝ, 0 < schurGap C x t := by
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.mp (eventually_all_schurGap_pos C)
  exact ⟨max R 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun x hx => hR x ((le_max_left _ _).trans hx)⟩

end
end RHTower.ThetaCuspOddDirectionTransport

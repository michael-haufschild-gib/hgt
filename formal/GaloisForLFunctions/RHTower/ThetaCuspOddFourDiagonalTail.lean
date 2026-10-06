import GaloisForLFunctions.RHTower.ThetaCuspNativeOddFourCofinal
import GaloisForLFunctions.RHTower.ThetaCuspNativeTwelfthJetLimit

open Filter Topology Matrix RHTower.ThetaCuspOddFour GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section
set_option autoImplicit false

def thetaCuspNativeOddFourDiagonalLoaded (C x : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => thetaCuspNativeOddFourMatrix x i j +
    if i.val=3 ∧ j.val=3 then C*thetaCuspCenterCompensationSource x else 0

theorem thetaCuspCenterCompensationSource_fourteenth_scaled_tendsto_zero :
    Tendsto (fun x : ℝ => thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^7))
      atTop (𝓝 0) := by
  have h := thetaCuspCenterCompensationSource_twelfth_scaled_tendsto_zero.mul
    thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  convert h using 1
  · ext x
    simp only [pow_succ,div_mul_eq_div_mul_one_div,one_div]
    field_simp
  · norm_num

private def diagonalLoadedScaled (C x : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => thetaCuspNativeScaledEvenJet (i.val+j.val+1) x +
    if i.val=3 ∧ j.val=3 then C*(thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^7)) else 0

private theorem diagonalLoadedScaled_tendsto (C : ℝ) (i j : Fin 4) :
    Tendsto (fun x => diagonalLoadedScaled C x i j) atTop (𝓝 (gaussianOddFour i j)) := by
  have h1 := thetaCuspNativeScaledEvenJet_one_tendsto
  have h2 := thetaCuspNativeScaledEvenJet_two_tendsto
  have h3 := thetaCuspNativeScaledEvenJet_three_tendsto
  have h4 := thetaCuspNativeScaledEvenJet_four_tendsto
  have h5 := thetaCuspNativeScaledEvenJet_five_tendsto
  have h6 := thetaCuspNativeScaledEvenJet_six_tendsto
  have h7 := native_seven_scaled_tendsto
  have hC := thetaCuspCenterCompensationSource_fourteenth_scaled_tendsto_zero.const_mul C
  fin_cases i <;> fin_cases j <;>
    simpa [diagonalLoadedScaled,gaussianOddFour] using
      (by first | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 |
        simpa using h7.add hC)

theorem thetaCuspNativeOddFourDiagonalLoaded_posDef_eventually (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, (thetaCuspNativeOddFourDiagonalLoaded C x).PosDef := by
  have hHerm (x : ℝ) : (diagonalLoadedScaled C x).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [diagonalLoadedScaled,add_comm,and_comm]
  have hlim := posDef_eventually_of_tendsto gaussianOddFour_posDef
    (Filter.Eventually.of_forall hHerm) (diagonalLoadedScaled_tendsto C)
  filter_upwards [hlim,eventually_gt_atTop (0 : ℝ)] with x hx hx0
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let d : Fin 4 → ℝ := fun i => f*q^i.val
  let D : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal d
  have hqpos : 0 < q := by unfold q thetaCuspSingleAtomReflectionScale; positivity
  have hq : q ≠ 0 := hqpos.ne'
  have hf : f ≠ 0 :=
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx0 (by norm_num)).ne'
  have hq' : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := hq
  have hf' : thetaCuspSourceTerm x 1 ≠ 0 := hf
  have hD : Function.Injective D.mulVec := by
    intro v w hvw
    funext i
    have hi := congrFun hvw i
    simp only [D,Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (mul_ne_zero hf (pow_ne_zero _ hq)) hi
  have heq : thetaCuspNativeOddFourDiagonalLoaded C x =
      q • (Dᴴ * diagonalLoadedScaled C x * D) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [D,d,Matrix.mul_apply,Matrix.diagonal,Fin.sum_univ_succ,
        thetaCuspNativeOddFourDiagonalLoaded,thetaCuspNativeOddFourMatrix,
        diagonalLoadedScaled,thetaCuspNativeScaledEvenJet] <;>
      field_simp [hf',hq'] <;> ring
  rw [heq]
  exact (hx.conjTranspose_mul_mul_same hD).smul hqpos

end
end RHTower

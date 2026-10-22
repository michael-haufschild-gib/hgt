import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNativeFourteenthJetLimit
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# Literal native odd-four source positivity on a cofinal ray

The complete theta reflection moments through order fourteen converge in
Gaussian-balanced coordinates to the positive shifted rank-four matrix.
Diagonal congruence transfers this to the unnormalized literal source.
No flux correction or integrated sign is included in this statement.
-/

open Filter Topology Matrix RHTower.ThetaCuspOddFour GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section

def thetaCuspNativeOddFourScaledMatrix (x : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => thetaCuspNativeScaledEvenJet (i.val+j.val+1) x

private theorem odd_four_scaled_entry_tendsto (i j : Fin 4) :
    Tendsto (fun x : ℝ => thetaCuspNativeOddFourScaledMatrix x i j)
      atTop (𝓝 (gaussianOddFour i j)) := by
  have h1 := thetaCuspNativeScaledEvenJet_one_tendsto
  have h2 := thetaCuspNativeScaledEvenJet_two_tendsto
  have h3 := thetaCuspNativeScaledEvenJet_three_tendsto
  have h4 := thetaCuspNativeScaledEvenJet_four_tendsto
  have h5 := thetaCuspNativeScaledEvenJet_five_tendsto
  have h6 := thetaCuspNativeScaledEvenJet_six_tendsto
  have h7 := native_seven_scaled_tendsto
  fin_cases i <;> fin_cases j <;>
    simpa [thetaCuspNativeOddFourScaledMatrix, gaussianOddFour] using
      (by first | exact h1 | exact h2 | exact h3 | exact h4 |
        exact h5 | exact h6 | exact h7)

theorem thetaCuspNativeOddFourScaledMatrix_posDef_eventually :
    ∀ᶠ x : ℝ in atTop, (thetaCuspNativeOddFourScaledMatrix x).PosDef := by
  have hHerm (x : ℝ) : (thetaCuspNativeOddFourScaledMatrix x).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [thetaCuspNativeOddFourScaledMatrix, add_comm]
  exact posDef_eventually_of_tendsto gaussianOddFour_posDef
    (Filter.Eventually.of_forall hHerm) odd_four_scaled_entry_tendsto

def thetaCuspNativeOddFourMatrix (x : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (-1 : ℝ)^(i.val+j.val+1) *
    thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x

theorem thetaCuspNativeOddFourMatrix_posDef_eventually :
    ∀ᶠ x : ℝ in atTop, (thetaCuspNativeOddFourMatrix x).PosDef := by
  filter_upwards [thetaCuspNativeOddFourScaledMatrix_posDef_eventually,
    eventually_gt_atTop (0 : ℝ)] with x hx hx0
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let d : Fin 4 → ℝ := fun i => f*q^i.val
  let D : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal d
  have hqpos : 0 < q := by
    unfold q thetaCuspSingleAtomReflectionScale
    positivity
  have hq : q ≠ 0 := hqpos.ne'
  have hf : f ≠ 0 :=
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx0 (by norm_num)).ne'
  have hq' : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := hq
  have hf' : thetaCuspSourceTerm x 1 ≠ 0 := hf
  have hD : Function.Injective D.mulVec := by
    intro v w hvw
    funext i
    have hi := congrFun hvw i
    simp only [D, Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (mul_ne_zero hf (pow_ne_zero _ hq)) hi
  have heq : thetaCuspNativeOddFourMatrix x =
      q • (Dᴴ * thetaCuspNativeOddFourScaledMatrix x * D) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [D, d, Matrix.mul_apply, Matrix.diagonal,
        Fin.sum_univ_succ, thetaCuspNativeOddFourMatrix,
        thetaCuspNativeOddFourScaledMatrix, thetaCuspNativeScaledEvenJet] <;>
      field_simp [hf', hq'] <;> ring
  rw [heq]
  exact (hx.conjTranspose_mul_mul_same hD).smul hqpos

end
end RHTower

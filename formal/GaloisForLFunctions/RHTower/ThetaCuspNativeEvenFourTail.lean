import GaloisForLFunctions.RHTower.ThetaCuspNativeTwelfthJetLimit
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# Complete even rank-four source positivity on a cofinal ray

The exact Gaussian limit is strictly positive by an explicit sum of four squares.
Complete-source convergence preserves strictness. Every fixed center-flux correction
has the same limit, so only a bounded set of centers remains for each coefficient.
-/
open Filter Topology Matrix
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section

/-- The even Gaussian moment block governing the next source rank. -/
def thetaCuspEvenFourGaussianMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 8, 192, 7680;
     8, 192, 7680, 430080;
     192, 7680, 430080, 30965760;
     7680, 430080, 30965760, 2724986880]

/-- Exact Gaussian rank-four positivity, proved by a triangular sum of squares. -/
theorem thetaCuspEvenFourGaussianMatrix_posDef : thetaCuspEvenFourGaussianMatrix.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [thetaCuspEvenFourGaussianMatrix]
  · intro v hv
    have heq : star v ⬝ᵥ thetaCuspEvenFourGaussianMatrix.mulVec v =
        (v 0+8*v 1+192*v 2+7680*v 3)^(2 : ℕ) +
        128*(v 1+48*v 2+2880*v 3)^(2 : ℕ) +
        98304*(v 2+120*v 3)^(2 : ℕ) + 188743680*(v 3)^(2 : ℕ) := by
      simp [thetaCuspEvenFourGaussianMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
      ring
    rw [heq]
    have h0 := sq_nonneg (v 0+8*v 1+192*v 2+7680*v 3)
    have h1 := sq_nonneg (v 1+48*v 2+2880*v 3)
    have h2 := sq_nonneg (v 2+120*v 3)
    have h3 := sq_nonneg (v 3)
    by_contra h
    have hv3 : v 3 = 0 := by nlinarith
    have hv2 : v 2 = 0 := by nlinarith
    have hv1 : v 1 = 0 := by nlinarith
    have hv0 : v 0 = 0 := by nlinarith
    apply hv
    funext i
    fin_cases i <;> simp [hv0, hv1, hv2, hv3]

/-- Literal even source block through derivative twelve, with one center-flux correction. -/
def thetaCuspNativeEvenFourCompensated (C x : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x +
    if i.val = 3 ∧ j.val = 3 then C*thetaCuspCenterCompensationSource x else 0

private def scaledMatrix (C x : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => thetaCuspNativeScaledEvenJet (i.val+j.val) x +
    if i.val = 3 ∧ j.val = 3 then C*(thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ))) else 0

private theorem scaledMatrix_tendsto (C : ℝ) (i j : Fin 4) :
    Tendsto (fun x => scaledMatrix C x i j) atTop (𝓝 (thetaCuspEvenFourGaussianMatrix i j)) := by
  have h0 := thetaCuspNativeScaledEvenJet_zero_tendsto
  have h1 := thetaCuspNativeScaledEvenJet_one_tendsto
  have h2 := thetaCuspNativeScaledEvenJet_two_tendsto
  have h3 := thetaCuspNativeScaledEvenJet_three_tendsto
  have h4 := thetaCuspNativeScaledEvenJet_four_tendsto
  have h5 := thetaCuspNativeScaledEvenJet_five_tendsto
  have h6 := thetaCuspNativeScaledEvenJet_six_tendsto
  have hC := thetaCuspCenterCompensationSource_twelfth_scaled_tendsto_zero.const_mul C
  fin_cases i <;> fin_cases j <;>
    simpa [scaledMatrix, thetaCuspEvenFourGaussianMatrix] using
      (by first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | simpa using h6.add hC)

/-- Every fixed correction of the complete source is strictly positive past some center. -/
theorem thetaCuspNativeEvenFourCompensated_posDef_eventually (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, (thetaCuspNativeEvenFourCompensated C x).PosDef := by
  have hHerm (x : ℝ) : (scaledMatrix C x).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [scaledMatrix, add_comm, and_comm]
  have hlim := posDef_eventually_of_tendsto thetaCuspEvenFourGaussianMatrix_posDef
    (Filter.Eventually.of_forall hHerm) (scaledMatrix_tendsto C)
  filter_upwards [hlim, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  let d : Fin 4 → ℝ := fun i => thetaCuspSourceTerm x 1*thetaCuspSingleAtomReflectionScale 1 x^i.val
  let D : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal d
  have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hf : thetaCuspSourceTerm x 1 ≠ 0 :=
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx0 (by norm_num)).ne'
  have hD : Function.Injective D.mulVec := by
    intro v w hvw
    funext i
    have hi := congrFun hvw i
    simp only [D, Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (mul_ne_zero hf (pow_ne_zero _ hq)) hi
  have heq : thetaCuspNativeEvenFourCompensated C x = Dᴴ * scaledMatrix C x * D := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [D, d, Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_succ,
        thetaCuspNativeEvenFourCompensated, scaledMatrix, thetaCuspNativeScaledEvenJet] <;>
      field_simp [hf, hq] <;> ring
  rw [heq]
  exact hx.conjTranspose_mul_mul_same hD

/-- For every fixed coefficient, the remaining even rank-four source comparison is compact. -/
theorem exists_thetaCuspNativeEvenFourCompensated_posDef_tail (C : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, R ≤ x →
      (thetaCuspNativeEvenFourCompensated C x).PosDef := by
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
    (thetaCuspNativeEvenFourCompensated_posDef_eventually C)
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx => ?_⟩
  exact hR x ((le_max_left _ _).trans hx)

end
end RHTower

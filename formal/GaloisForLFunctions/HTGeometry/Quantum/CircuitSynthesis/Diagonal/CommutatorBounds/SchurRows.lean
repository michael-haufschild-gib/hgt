import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich

/-! # An operator norm bound for a Schur multiplier from its square-summable rows -/

open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis.CommutatorBounds
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Cauchy–Schwarz in each row leaves exactly one squared column norm
of the input matrix after summing over output indices. -/
theorem norm_schur_of_rows (S C : Matrix I I ℂ) {R : ℝ} (hR : 0≤R)
    (hs : ∀ i, ∑ j, ‖S i j‖^2 ≤ R^2) :
    ‖(Matrix.of fun i j => S i j*C i j : Matrix I I ℂ)‖≤R*‖C‖ := by
  let A : Matrix I I ℂ := Matrix.of fun i j => S i j*C i j
  change ‖A‖≤_
  rw [←Matrix.l2_opNorm_toEuclideanCLM A]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hR (norm_nonneg _))
  intro v
  have hrow (i : I) :
      ‖(A *ᵥ v.ofLp) i‖^2 ≤ R^2*∑ j, ‖C i j‖^2*‖v j‖^2 := by
    have htri : ‖(A *ᵥ v.ofLp) i‖ ≤ ∑ j, ‖S i j‖*(‖C i j‖*‖v j‖) := by
      simpa only [A,Matrix.mulVec,dotProduct,Matrix.of_apply,norm_mul,mul_assoc] using
        norm_sum_le Finset.univ (fun j => (S i j*C i j)*v j)
    refine (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans ?_
    have hcs := sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖S i j‖)
      (fun j => ‖C i j‖*‖v j‖)
    simp only [mul_pow] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_right (hs i) (sum_nonneg fun _ _ => by positivity))
  have hcol (j : I) : (∑ i, ‖C i j‖^2)≤‖C‖^2 := by
    letI : Nonempty I := ⟨j⟩
    exact sum_normSq_column_le_opNorm_sq C j
  have hsum : (∑ i, ‖(A *ᵥ v.ofLp) i‖^2)≤(R*‖C‖*‖v‖)^2 := calc
    _ ≤ ∑ i, R^2*∑ j, ‖C i j‖^2*‖v j‖^2 := sum_le_sum fun i _ => hrow i
    _ = R^2*∑ j, (∑ i, ‖C i j‖^2)*‖v j‖^2 := by rw [←mul_sum,sum_comm]; simp only [sum_mul]
    _ ≤ R^2*∑ j, ‖C‖^2*‖v j‖^2 := mul_le_mul_of_nonneg_left
      (sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _))
      (sq_nonneg R)
    _ = _ := by rw [←mul_sum,←EuclideanSpace.norm_sq_eq]; ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.norm_sq_eq]
  simpa only [Matrix.ofLp_toEuclideanCLM] using hsum

#print axioms norm_schur_of_rows
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis.CommutatorBounds

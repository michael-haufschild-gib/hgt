import GaloisForLFunctions.HTGeometry.Quantum.PositiveConstraintSupport
import GaloisForLFunctions.HTGeometry.GramRealizationFirewall

/-!
# Exact constraints on Gram realizations

Applying the positive-support principle to a Gram kernel turns a zero scalar
energy into actual linear relations among the realizing vectors. The ambient
Hilbert space may be infinite dimensional: only the observed family is finite.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Quantum

open Matrix

variable {ι κ σ E : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype σ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A row of coefficients represents a genuine vector relation in the Gram realization. -/
def gramConstraintVector (C : Matrix κ ι ℂ) (v : ι → E) (a : κ) : E :=
  ∑ i, star (C a i) • v i

/-- Squared constraint energy is the sum of the squared norms of its realized relations. -/
theorem constraintEnergy_innerGramMatrix (C : Matrix κ ι ℂ) (v : ι → E) :
    constraintEnergy C (innerGramMatrix v) = ∑ a, ‖gramConstraintVector C v a‖ ^ 2 := by
  unfold constraintEnergy
  rw [Matrix.trace, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  have h : (C * innerGramMatrix v * Cᴴ) a a =
      inner ℂ (gramConstraintVector C v a) (gramConstraintVector C v a) := by
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, innerGramMatrix_apply,
      gramConstraintVector, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      ← RCLike.star_def, star_star, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [Matrix.diag_apply, h, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Zero observed energy detects the actual Hilbert-space relations, in every dimension. -/
theorem constraintEnergy_innerGramMatrix_eq_zero_iff (C : Matrix κ ι ℂ) (v : ι → E) :
    constraintEnergy C (innerGramMatrix v) = 0 ↔
      ∀ a, gramConstraintVector C v a = 0 := by
  rw [constraintEnergy_innerGramMatrix,
    Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg ‖gramConstraintVector C v a‖)]
  simp only [Finset.mem_univ, forall_const, sq_eq_zero_iff, norm_eq_zero]

/-- The linear kernel of the Gram matrix is exactly the space of realized relations. -/
theorem mul_innerGramMatrix_eq_zero_iff (C : Matrix κ ι ℂ) (v : ι → E) :
    C * innerGramMatrix v = 0 ↔ ∀ a, gramConstraintVector C v a = 0 := by
  rw [← constraintEnergy_eq_zero_iff C (posSemidef_innerGramMatrix v),
    constraintEnergy_innerGramMatrix_eq_zero_iff]

/-- A single common-kernel energy certifies all relations in a finite family of observers. -/
theorem constraintHamiltonian_innerGramMatrix_eq_zero_iff
    (C : σ → Matrix κ ι ℂ) (v : ι → E) :
    (constraintHamiltonian C * innerGramMatrix v).trace.re = 0 ↔
      ∀ s a, gramConstraintVector (C s) v a = 0 := by
  rw [trace_constraintHamiltonian_eq_zero_iff C (posSemidef_innerGramMatrix v)]
  exact forall_congr' fun s => mul_innerGramMatrix_eq_zero_iff (C s) v

end GaloisForLFunctions.HTGeometry.Quantum

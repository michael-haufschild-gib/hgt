import GaloisForLFunctions.HTGeometry.PureReplicaCollectiveEnergyLaw

/-!
# Centralizer-residual replica energy law

Subtracting an exact centralizer component from a Hermitian observer leaves its commutator signal
unchanged.  On tensor replicas, the exact collective energy is therefore the original one-copy
signal times the replica number and the residual Hilbert--Schmidt mass to power `r - 1`.

This identifies a sharp obstruction to using centralizer removal alone as a mixing mechanism:
Bernoulli's inequality shows that a removed mass `delta` with replica budget `r * delta ≤ eta`
leaves at least `1 - eta` of the residual replica-mass factor.
-/

open Finset Matrix
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Subtracting an element of the centralizer preserves the exact commutator. -/
theorem ringCommutator_sub_right_of_eq_zero
    (G X C : Matrix n n ℂ) (hC : ringCommutator G C = 0) :
    ringCommutator G (X - C) = ringCommutator G X := by
  calc
    ringCommutator G (X - C) =
        ringCommutator G X - ringCommutator G C := by
      simp only [ringCommutator, Matrix.mul_sub, Matrix.sub_mul]
      abel
    _ = ringCommutator G X := by rw [hC, sub_zero]

/-- Vectorization preserves the centralizer-residual commutator identity. -/
theorem matrixCommutatorRepresentation_vec_sub_centralizer
    (G X C : Matrix n n ℂ) (hC : ringCommutator G C = 0) :
    matrixCommutatorRepresentation G *ᵥ Matrix.vec (X - C) =
      matrixCommutatorRepresentation G *ᵥ Matrix.vec X := by
  rw [matrixCommutatorRepresentation_mulVec_vec,
    matrixCommutatorRepresentation_mulVec_vec,
    ringCommutator_sub_right_of_eq_zero G X C hC]

/-- The one-copy Gram energy is invariant under exact centralizer subtraction. -/
theorem matrixCommutatorRepresentation_gram_energy_sub_centralizer
    (G X C : Matrix n n ℂ) (hC : ringCommutator G C = 0) :
    boundedReplicaThresholdProjectorQuadForm
        ((matrixCommutatorRepresentation G)ᴴ * matrixCommutatorRepresentation G)
        (Matrix.vec (X - C)) =
      boundedReplicaThresholdProjectorQuadForm
        ((matrixCommutatorRepresentation G)ᴴ * matrixCommutatorRepresentation G)
        (Matrix.vec X) := by
  rw [quadForm_conjTranspose_mul, quadForm_conjTranspose_mul]
  rw [matrixCommutatorRepresentation_vec_sub_centralizer G X C hC]

/-- Bernoulli obstruction: a small removed mass cannot create low-replica decay. -/
theorem one_sub_nat_mul_le_one_sub_pow
    (delta : ℝ) (hdelta : delta ≤ 1) (r : ℕ) :
    1 - (r : ℝ) * delta ≤ (1 - delta) ^ r := by
  have h := one_add_mul_le_pow (a := -delta) (by linarith) r
  simpa [sub_eq_add_neg] using h

/-- Budget form: if total removed replica mass is at most `eta`, at least `1 - eta` remains. -/
theorem one_sub_eta_le_residualReplicaMass_of_budget
    (delta eta : ℝ) (hdelta : delta ≤ 1) (r : ℕ)
    (hbudget : (r : ℝ) * delta ≤ eta) :
    1 - eta ≤ (1 - delta) ^ r := by
  exact le_trans (sub_le_sub_left hbudget 1)
    (one_sub_nat_mul_le_one_sub_pow delta hdelta r)

/-- **Centralizer-residual replica law.**  The collective energy keeps the original commutator
signal exactly; only the Hilbert--Schmidt mass of the residual is replicated. -/
theorem centralizerResidual_collectiveReplicaCommutator_energy
    (r : ℕ) (G X C : Matrix n n ℂ)
    (hX : Xᴴ = X) (hCstar : Cᴴ = C) (hC : ringCommutator G C = 0) :
    boundedReplicaThresholdProjectorQuadForm
        ((collectiveReplicaSlotOp r (matrixCommutatorRepresentation G))ᴴ *
          collectiveReplicaSlotOp r (matrixCommutatorRepresentation G))
        (replicaVector r (Matrix.vec (X - C))) =
      (r : ℂ) * boundedReplicaThresholdProjectorQuadForm
        ((matrixCommutatorRepresentation G)ᴴ *
          matrixCommutatorRepresentation G) (Matrix.vec X) *
        hermInner (Matrix.vec (X - C)) (Matrix.vec (X - C)) ^ (r - 1) := by
  rw [hermitian_collectiveReplicaCommutator_energy_unnormalized r G (X - C) (by
    simp [Matrix.conjTranspose_sub, hX, hCstar])]
  rw [matrixCommutatorRepresentation_gram_energy_sub_centralizer G X C hC]

end

end GaloisForLFunctions.HTGeometry

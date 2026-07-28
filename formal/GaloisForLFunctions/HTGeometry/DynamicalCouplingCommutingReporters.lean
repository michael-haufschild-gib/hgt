import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Dynamical coupling with commuting cross-sector reporters

Tensor-factor reporters commute exactly, but a single product interaction generator can have a
nonzero commutator response against each reporter.  These identities separate kinematic
cross-compatibility from dynamical coupling.  They make no claim that the matrices are complete
physical observables or that a finite tensor product is a quantum spacetime.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Kronecker

/-- Matrix commutator, used here only to express exact response identities. -/
def matrixResponseCommutator {K ι : Type*} [CommRing K] [Fintype ι]
    (A B : Matrix ι ι K) : Matrix ι ι K :=
  A * B - B * A

section CrossReporters

variable {K m n : Type*} [CommRing K]
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Reporters acting on separate tensor factors commute exactly. -/
theorem tensorFactorReporters_commute (A : Matrix m m K) (B : Matrix n n K) :
    (A ⊗ₖ (1 : Matrix n n K)) * ((1 : Matrix m m K) ⊗ₖ B) =
      ((1 : Matrix m m K) ⊗ₖ B) * (A ⊗ₖ (1 : Matrix n n K)) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

end CrossReporters

section CausalResponse

variable {K m n : Type*} [CommRing K]
variable [Fintype m] [Fintype n] [DecidableEq n]

/-- A product interaction responds against the left-factor reporter by the left commutator. -/
theorem productInteraction_left_response
    (A C : Matrix m m K) (D : Matrix n n K) :
    matrixResponseCommutator (C ⊗ₖ D) (A ⊗ₖ (1 : Matrix n n K)) =
      matrixResponseCommutator C A ⊗ₖ D := by
  rw [matrixResponseCommutator, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  ext i j
  simp [matrixResponseCommutator, Matrix.kroneckerMap_apply]
  ring

end CausalResponse

section InternalResponse

variable {K m n : Type*} [CommRing K]
variable [Fintype m] [Fintype n] [DecidableEq m]

/-- A product interaction responds against the right-factor reporter by the right commutator. -/
theorem productInteraction_right_response
    (B D : Matrix n n K) (C : Matrix m m K) :
    matrixResponseCommutator (C ⊗ₖ D) ((1 : Matrix m m K) ⊗ₖ B) =
      C ⊗ₖ matrixResponseCommutator D B := by
  rw [matrixResponseCommutator, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  ext i j
  simp [matrixResponseCommutator, Matrix.kroneckerMap_apply]
  ring

end InternalResponse

section CouplingPackage

variable {K m n : Type*} [CommRing K]
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Commuting-reporter coupling package.**  Cross-factor reporters commute, while one product
generator has exact response identities in both factors.  This is the formal positive survivor of
the failed identification of interaction with cross-reporter incompatibility. -/
theorem commutingReporters_productInteraction_responses
    (A C : Matrix m m K) (B D : Matrix n n K) :
    ((A ⊗ₖ (1 : Matrix n n K)) * ((1 : Matrix m m K) ⊗ₖ B) =
        ((1 : Matrix m m K) ⊗ₖ B) * (A ⊗ₖ (1 : Matrix n n K))) ∧
      (matrixResponseCommutator (C ⊗ₖ D) (A ⊗ₖ (1 : Matrix n n K)) =
        matrixResponseCommutator C A ⊗ₖ D) ∧
      (matrixResponseCommutator (C ⊗ₖ D) ((1 : Matrix m m K) ⊗ₖ B) =
        C ⊗ₖ matrixResponseCommutator D B) := by
  exact ⟨tensorFactorReporters_commute A B,
    productInteraction_left_response A C D,
    productInteraction_right_response B D C⟩

end CouplingPackage

end GaloisForLFunctions.HTGeometry

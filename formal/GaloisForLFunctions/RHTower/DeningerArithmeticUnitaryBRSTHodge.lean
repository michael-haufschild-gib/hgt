import GaloisForLFunctions.HTGeometry.BRSTHodgeConstraint

/-!
# Unitary BRST--Hodge descent for Deninger's centered transfers

A unitary chain symmetry automatically commutes with the adjoint differential and
therefore with the BRST--Hodge Hamiltonian.  Thus finite harmonic cohomology needs
no independent Laplacian-equivariance axiom.
-/

namespace RHTower

section

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/--
A two-sided unitary that commutes with a bounded differential also commutes with
its Hilbert adjoint.
-/
theorem deningerUnitary_commutes_adjoint_of_commutes
    (U Q : E →L[𝕜] E)
    (hUUadjoint : U * U.adjoint = 1)
    (hadjointU : U.adjoint * U = 1)
    (hUQ : U * Q = Q * U) :
    U * Q.adjoint = Q.adjoint * U := by
  have hadjoint :
      Q.adjoint * U.adjoint = U.adjoint * Q.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint hUQ
    simpa [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.adjoint_comp] using h
  calc
    U * Q.adjoint =
        (U * Q.adjoint) * (U.adjoint * U) := by
          rw [hadjointU, mul_one]
    _ = U * (Q.adjoint * U.adjoint) * U := by
      simp only [mul_assoc]
    _ = U * (U.adjoint * Q.adjoint) * U := by rw [hadjoint]
    _ = (U * U.adjoint) * Q.adjoint * U := by
      simp only [mul_assoc]
    _ = Q.adjoint * U := by rw [hUUadjoint, one_mul]

/--
A unitary chain symmetry commutes with the BRST--Hodge Hamiltonian.
-/
theorem deningerUnitary_commutes_brstHodgeHamiltonian
    (U Q : E →L[𝕜] E)
    (hUUadjoint : U * U.adjoint = 1)
    (hadjointU : U.adjoint * U = 1)
    (hUQ : U * Q = Q * U) :
    U * HTGeometry.brstHodgeHamiltonian Q =
      HTGeometry.brstHodgeHamiltonian Q * U := by
  have hUQadjoint :
      U * Q.adjoint = Q.adjoint * U :=
    deningerUnitary_commutes_adjoint_of_commutes
      U Q hUUadjoint hadjointU hUQ
  rw [HTGeometry.brstHodgeHamiltonian_eq_adjoint_mul_add_mul_adjoint,
    mul_add, add_mul]
  congr 1
  · calc
      U * (Q.adjoint * Q) = (U * Q.adjoint) * Q := by
        rw [mul_assoc]
      _ = (Q.adjoint * U) * Q := by rw [hUQadjoint]
      _ = Q.adjoint * (U * Q) := by rw [mul_assoc]
      _ = Q.adjoint * (Q * U) := by rw [hUQ]
      _ = (Q.adjoint * Q) * U := by rw [mul_assoc]
  · calc
      U * (Q * Q.adjoint) = (U * Q) * Q.adjoint := by
        rw [mul_assoc]
      _ = (Q * U) * Q.adjoint := by rw [hUQ]
      _ = Q * (U * Q.adjoint) := by rw [mul_assoc]
      _ = Q * (Q.adjoint * U) := by rw [hUQadjoint]
      _ = (Q * Q.adjoint) * U := by rw [mul_assoc]

/--
Every unitary chain symmetry preserves the finite harmonic sector.
-/
theorem deningerUnitary_maps_brstHarmonic_to_brstHarmonic
    (U Q : E →L[𝕜] E)
    (hUUadjoint : U * U.adjoint = 1)
    (hadjointU : U.adjoint * U = 1)
    (hUQ : U * Q = Q * U)
    {x : E}
    (hx : HTGeometry.brstHodgeHamiltonian Q x = 0) :
    HTGeometry.brstHodgeHamiltonian Q (U x) = 0 := by
  have hcomm :
      U * HTGeometry.brstHodgeHamiltonian Q =
        HTGeometry.brstHodgeHamiltonian Q * U :=
    deningerUnitary_commutes_brstHodgeHamiltonian
      U Q hUUadjoint hadjointU hUQ
  have happly := LinearMap.congr_fun
    (congrArg ContinuousLinearMap.toLinearMap hcomm) x
  simpa [hx] using happly.symm

end

end RHTower

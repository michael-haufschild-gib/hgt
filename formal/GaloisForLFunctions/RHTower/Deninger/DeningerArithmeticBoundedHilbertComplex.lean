import GaloisForLFunctions.HTGeometry.BRSTHodgeConstraint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Bounded Hilbert-complex Hodge decomposition for Deninger cohomology

For a bounded differential `Q` on a Hilbert space, reduced cohomology is represented by
simultaneously `Q`-closed and `Q†`-closed vectors.  This file proves the exact orthogonal
submodule decomposition needed by a bounded realization of Deninger's derived coefficient
complex.

The result is pure Hilbert-space algebra.  It assumes no arithmetic realization, spectral
identification, positivity conjecture, zeta-zero statement, or Riemann hypothesis.
-/

noncomputable section

namespace RHTower

section BoundedHilbertComplex

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Harmonic vectors of a bounded Hilbert differential. -/
def deningerBoundedHarmonic (Q : E →L[𝕜] E) : Submodule 𝕜 E :=
  Q.ker ⊓ Q.adjoint.ker

omit [CompleteSpace E] in
/-- Nilpotence puts every boundary in the cocycle subspace. -/
theorem deningerBoundedHilbertComplex_range_le_ker
    (Q : E →L[𝕜] E) (hQ : Q * Q = 0) :
    Q.range ≤ Q.ker := by
  rintro _ ⟨x, rfl⟩
  have hx := DFunLike.congr_fun hQ x
  simpa [ContinuousLinearMap.mul_def] using hx

omit [CompleteSpace E] in
/-- The closure of the boundary subspace remains inside the cocycle subspace. -/
theorem deningerBoundedHilbertComplex_closure_range_le_ker
    (Q : E →L[𝕜] E) (hQ : Q * Q = 0) :
    Q.range.topologicalClosure ≤ Q.ker :=
  Q.range.topologicalClosure_minimal
    (deningerBoundedHilbertComplex_range_le_ker Q hQ)
    Q.isClosed_ker

/-- Harmonic vectors are cocycles orthogonal to the completed boundary subspace. -/
theorem deningerBoundedHarmonic_eq_orthogonalClosureRange_inf_ker
    (Q : E →L[𝕜] E) :
    deningerBoundedHarmonic Q =
      Q.range.topologicalClosureᗮ ⊓ Q.ker := by
  simp only [deningerBoundedHarmonic, Submodule.orthogonal_closure,
    Q.orthogonal_range, inf_comm]

/-- The BRST--Hodge Hamiltonian has exactly the harmonic vectors as its kernel. -/
theorem deningerBoundedHarmonic_eq_ker_brstHodgeHamiltonian
    (Q : E →L[𝕜] E) :
    deningerBoundedHarmonic Q =
      (HTGeometry.brstHodgeHamiltonian Q).ker := by
  ext x
  simp only [deningerBoundedHarmonic, Submodule.mem_inf,
    LinearMap.mem_ker]
  exact (HTGeometry.brstHodgeHamiltonian_apply_eq_zero_iff Q x).symm

/--
Reduced Hodge decomposition: cocycles are the orthogonal sum of completed boundaries and
harmonic vectors.
-/
theorem deningerBoundedHilbertComplex_ker_eq_closureRange_sup_harmonic
    (Q : E →L[𝕜] E) (hQ : Q * Q = 0) :
    Q.ker =
      Q.range.topologicalClosure ⊔ deningerBoundedHarmonic Q := by
  rw [deningerBoundedHarmonic_eq_orthogonalClosureRange_inf_ker]
  exact
    (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
      (deningerBoundedHilbertComplex_closure_range_le_ker Q hQ)).symm

/--
Full weak Hodge decomposition into completed boundaries, harmonic vectors, and completed
coboundaries.
-/
theorem deningerBoundedHilbertComplex_full_hodge
    (Q : E →L[𝕜] E) (hQ : Q * Q = 0) :
    (Q.range.topologicalClosure ⊔ deningerBoundedHarmonic Q) ⊔
        Q.adjoint.range.topologicalClosure = ⊤ := by
  rw [← deningerBoundedHilbertComplex_ker_eq_closureRange_sup_harmonic Q hQ,
    ← Q.orthogonal_ker]
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

end BoundedHilbertComplex

end RHTower

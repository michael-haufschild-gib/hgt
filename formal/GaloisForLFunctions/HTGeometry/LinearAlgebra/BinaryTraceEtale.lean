import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinaryTraceCorrection
import GaloisForLFunctions.HTGeometry.FiniteFreeDiscriminant

/-!
# Étaleness detected by the alternating trace pairing

For finite commutative binary algebras, the corrected trace pairing is
nondegenerate exactly when the algebra is étale and its dimension is even.
The trace discriminant detects formal unramifiedness, and over a field finite
algebras are flat and finitely presented.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix Module
variable (A : Type*) [CommRing A] [Algebra (ZMod 2) A] [Module.Finite (ZMod 2) A]

/-- The alternating trace pairing is nondegenerate precisely for unramified algebras
of even dimension. -/
theorem binaryTraceForm_nondegenerate_iff_formallyUnramified :
    (binaryTraceForm A).Nondegenerate ↔
      Algebra.FormallyUnramified (ZMod 2) A ∧ finrank (ZMod 2) A % 2 = 0 := by
  classical
  rw [binaryTraceForm_nondegenerate_iff]
  constructor
  · rintro ⟨hnd, he⟩
    refine ⟨?_, he⟩
    let b := Module.finBasis (ZMod 2) A
    apply Algebra.formallyUnramified_of_isUnit_discr b
    rw [Algebra.discr_def, Algebra.traceMatrix_of_basis, isUnit_iff_ne_zero]
    exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  · rintro ⟨hA, he⟩
    letI := hA
    exact ⟨Algebra.traceForm_nondegenerate_of_formallyUnramified_field (ZMod 2) A, he⟩

/-- A finite binary algebra has nondegenerate alternating trace pairing exactly when
it is étale and has even dimension. -/
theorem binaryTraceForm_nondegenerate_iff_etale :
    (binaryTraceForm A).Nondegenerate ↔
      Algebra.Etale (ZMod 2) A ∧ finrank (ZMod 2) A % 2 = 0 := by
  rw [binaryTraceForm_nondegenerate_iff_formallyUnramified]
  constructor
  · rintro ⟨hA, he⟩
    letI := hA
    letI : Algebra.FinitePresentation (ZMod 2) A := by
      rw [← Algebra.FinitePresentation.of_finiteType]
      infer_instance
    exact ⟨Algebra.Etale.of_formallyUnramified_of_flat, he⟩
  · rintro ⟨hA, he⟩
    letI := hA
    exact ⟨inferInstance, he⟩

#print axioms binaryTraceForm_nondegenerate_iff_formallyUnramified
#print axioms binaryTraceForm_nondegenerate_iff_etale
end GaloisForLFunctions.HTGeometry.LinearAlgebra

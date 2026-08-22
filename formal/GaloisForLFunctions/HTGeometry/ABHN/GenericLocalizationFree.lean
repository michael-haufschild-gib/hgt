import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Free

/-!
# Spreading generic freeness to a principal open set

A finitely presented module whose generic fiber over a fraction field is free
is free after inverting one nonzero base element.  This supplies the finite
projective/free ingredient in the Azumaya-locus construction for a CSA order.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- A finitely presented module over a domain is free on a nonempty principal open set whenever
its fraction-field scalar extension is a vector space. -/
theorem exists_nonzero_away_free_of_fractionField_baseChange
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K] [Algebra R K]
    [IsFractionRing R K]
    (M : Type w) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] :
    ∃ r : R, r ≠ 0 ∧ Module.Free (Localization (Submonoid.powers r))
      (LocalizedModule.Away r M) := by
  let S := nonZeroDivisors R
  let mM := LocalizedModule.mkLinearMap S M
  let tM := TensorProduct.mk R K M 1
  letI : IsLocalizedModule S tM := inferInstance
  obtain ⟨r, hr, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers (M' := K ⊗[R] M) S tM K
  exact ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, hfree⟩

end GaloisForLFunctions.HTGeometry.ABHN

import GaloisForLFunctions.HTGeometry.TensorProductCharZeroReduced
import GaloisForLFunctions.HTGeometry.DifferenceSigmaSimple
import GaloisForLFunctions.HTGeometry.PointsSeparate

/-!
# The Galois-group coordinate algebra is reduced, and its points separate

The Galois correspondence of difference Picard--Vessiot theory identifies the coordinate algebra of
the Galois group with the constants of the tensor square `R ⊗_K R`, and it needs the points of that
algebra to separate its elements.  Over an algebraically closed constant field that is the
Nullstellensatz together with reducedness, and reducedness is now unconditional in characteristic
zero: a `σ`-simple ring is reduced, and in characteristic zero the tensor square of a reduced
algebra is reduced.
-/

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

noncomputable section

/-- **The tensor square of a `σ`-simple difference ring over a characteristic-zero field is
reduced.** -/
theorem isReduced_tensorSquare_of_isSigmaSimple
    {K R : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R] [Nontrivial R]
    {σ : R ≃+* R} (hσ : IsSigmaSimple σ) : IsReduced (R ⊗[K] R) := by
  haveI : IsReduced R := isReduced_of_isSigmaSimple hσ
  exact isReduced_tensorProduct_of_charZero

/-- Any subalgebra of the tensor square of a `σ`-simple difference ring is reduced. -/
theorem isReduced_subalgebra_tensorSquare
    {K R C : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R] [Nontrivial R]
    [CommRing C] [Algebra C (R ⊗[K] R)]
    {σ : R ≃+* R} (hσ : IsSigmaSimple σ) (E : Subalgebra C (R ⊗[K] R)) : IsReduced ↥E := by
  haveI := isReduced_tensorSquare_of_isSigmaSimple (K := K) hσ
  exact isReduced_of_injective E.subtype Subtype.val_injective

/-- **Points of the Galois-group coordinate algebra separate.**  An element of a finitely generated
subalgebra of the tensor square killed by every point of that subalgebra over an algebraically
closed constant field is zero. -/
theorem eq_zero_of_forall_algHom_eq_zero_tensorSquare
    {K R C : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R] [Nontrivial R]
    [Field C] [IsAlgClosed C] [Algebra C (R ⊗[K] R)]
    {σ : R ≃+* R} (hσ : IsSigmaSimple σ) (E : Subalgebra C (R ⊗[K] R))
    [Algebra.FiniteType C ↥E] {x : ↥E} (h : ∀ χ : ↥E →ₐ[C] C, χ x = 0) : x = 0 := by
  haveI : IsReduced ↥E := isReduced_subalgebra_tensorSquare (K := K) hσ E
  exact eq_zero_of_forall_algHom_eq_zero h

end

end GaloisForLFunctions.HTGeometry

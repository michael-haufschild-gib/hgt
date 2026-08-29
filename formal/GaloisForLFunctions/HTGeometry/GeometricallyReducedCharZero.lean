import GaloisForLFunctions.HTGeometry.AdjoinRootTensorBaseChange

/-!
# Geometric reducedness in characteristic zero

Mathlib has the class `Algebra.IsGeometricallyReduced` but **no instance for a perfect base field**:
nothing there says that a reduced algebra over a field of characteristic zero stays reduced after
base change to the algebraic closure.  That statement is supplied here.

The proof is the standard filtered argument.  A finitely generated subalgebra `B` of the algebraic
closure is finite over `k`, hence a field, hence — by the primitive element theorem, available
because characteristic zero makes every algebraic extension separable — of the form
`AdjoinRoot (minpoly k α)` with `minpoly k α` monic and separable.  Base change along such a
polynomial preserves reducedness (`isReduced_adjoinRoot_tensor_of_separable`), and mathlib's
`IsReduced.tensorProduct_of_flat_of_forall_fg` assembles the finitely generated pieces.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial TensorProduct

/-- **A reduced algebra stays reduced after base change to a finite separable extension.** -/
theorem isReduced_tensor_of_finiteDimensional
    {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A] [IsReduced A]
    {L : Type*} [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L] :
    IsReduced (A ⊗[k] L) := by
  classical
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k L
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  have hmonic : (minpoly k α).Monic := minpoly.monic hint
  have hsep : (minpoly k α).Separable := Algebra.IsSeparable.isSeparable k α
  -- `L` is the root algebra of the minimal polynomial
  have heq : AdjoinRoot (minpoly k α) ≃ₐ[k] L :=
    (IntermediateField.adjoinRootEquivAdjoin k hint).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)
  haveI : IsReduced (AdjoinRoot (minpoly k α) ⊗[k] A) :=
    isReduced_adjoinRoot_tensor_of_separable hmonic hsep
  have hequiv : (A ⊗[k] L) ≃+* (AdjoinRoot (minpoly k α) ⊗[k] A) :=
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (A₁ := A)) heq.symm).trans
      (Algebra.TensorProduct.comm k A (AdjoinRoot (minpoly k α)))).toRingEquiv
  exact isReduced_of_injective hequiv.toRingHom hequiv.injective

/-- **Geometric reducedness in characteristic zero.**  A reduced algebra over a field of
characteristic zero stays reduced after base change to the algebraic closure. -/
instance isGeometricallyReduced_of_charZero
    (k : Type*) [Field k] [CharZero k] (A : Type*) [CommRing A] [Algebra k A] [IsReduced A] :
    Algebra.IsGeometricallyReduced k A := by
  classical
  rw [Algebra.isGeometricallyReduced_field_iff]
  have hcomm : (AlgebraicClosure k ⊗[k] A) ≃+* (A ⊗[k] AlgebraicClosure k) :=
    (Algebra.TensorProduct.comm k (AlgebraicClosure k) A).toRingEquiv
  haveI : IsReduced (A ⊗[k] AlgebraicClosure k) := by
    refine IsReduced.tensorProduct_of_flat_of_forall_fg (R := k) (C := A)
      (A := AlgebraicClosure k) ?_
    intro B hB
    haveI : Algebra.FiniteType k B := ⟨(Subalgebra.fg_top B).mpr hB⟩
    haveI : Algebra.IsIntegral k B := by
      refine ⟨fun x => ?_⟩
      have hx : IsIntegral k ((B.val) x) :=
        Algebra.IsIntegral.isIntegral (R := k) ((B.val) x)
      exact (isIntegral_algHom_iff B.val Subtype.val_injective).mp hx
    haveI : Module.Finite k B := Algebra.IsIntegral.finite
    haveI : FiniteDimensional k B := inferInstance
    let F : IntermediateField k (AlgebraicClosure k) :=
      B.toIntermediateField (fun x _ => Algebra.IsIntegral.inv_mem (by assumption))
    haveI : FiniteDimensional k F := ‹FiniteDimensional k B›
    haveI : Algebra.IsSeparable k F := inferInstance
    exact isReduced_tensor_of_finiteDimensional (k := k) (A := A) (L := F)
  exact isReduced_of_injective hcomm.toRingHom hcomm.injective

end GaloisForLFunctions.HTGeometry

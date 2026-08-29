import GaloisForLFunctions.HTGeometry.TensorFractionRingDomain

/-!
# Reducedness of a tensor product over a field of characteristic zero

The two halves built so far — the algebraic step
(`isReduced_adjoinRoot_of_separable`, `isReduced_tensor_of_finiteDimensional`) and the purely
transcendental step (`isDomain_tensor_of_isFractionRing`) — combine through a transcendence basis
into the field case:

> for `k` of characteristic zero and `F`, `L` field extensions of `k`, `F ⊗[k] L` is reduced.

This is the statement mathlib is missing and that the difference-Galois torsor needs: the constants
algebra `E` sits inside `R ⊗_K R`, so reducedness of the tensor square of the Picard--Vessiot ring
is exactly what makes the Galois correspondence's separation argument available.
-/

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

/-- **A reduced algebra stays reduced after base change to an algebraic field extension**, in
characteristic zero. -/
theorem isReduced_tensor_of_isAlgebraic
    {k : Type*} [Field k] [CharZero k] {A : Type*} [CommRing A] [Algebra k A] [IsReduced A]
    {L : Type*} [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] :
    IsReduced (A ⊗[k] L) := by
  classical
  refine IsReduced.tensorProduct_of_flat_of_forall_fg (R := k) (C := A) (A := L) ?_
  intro B hB
  haveI : Algebra.FiniteType k B := ⟨(Subalgebra.fg_top B).mpr hB⟩
  haveI : Algebra.IsIntegral k B := by
    refine ⟨fun x => ?_⟩
    have hx : IsIntegral k ((B.val) x) := Algebra.IsIntegral.isIntegral (R := k) ((B.val) x)
    exact (isIntegral_algHom_iff B.val Subtype.val_injective).mp hx
  haveI : Module.Finite k B := Algebra.IsIntegral.finite
  haveI : FiniteDimensional k B := inferInstance
  let G : IntermediateField k L :=
    B.toIntermediateField (fun x _ => Algebra.IsIntegral.inv_mem (by assumption))
  haveI : FiniteDimensional k G := ‹FiniteDimensional k B›
  haveI : Algebra.IsSeparable k G := inferInstance
  exact isReduced_tensor_of_finiteDimensional (k := k) (A := A) (L := G)

/-- The assembly step, with the intermediate field kept abstract (an `IntermediateField`
coercion produces a scalar-action diamond that blocks the nested tensor's ring instance). -/
theorem isReduced_tensor_of_algebraic_over_domain
    {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F]
    {L : Type*} [Field L] [Algebra k L]
    (M : Type*) [Field M] [CharZero M] [Algebra k M] [Algebra M L] [IsScalarTower k M L]
    [Algebra.IsAlgebraic M L] [IsDomain (M ⊗[k] F)] :
    IsReduced (F ⊗[k] L) := by
  haveI : IsReduced (M ⊗[k] F) := by
    constructor
    rintro x ⟨n, hn⟩
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [pow_zero] at hn
      exact absurd hn one_ne_zero
    · exact (pow_eq_zero_iff hpos.ne').mp hn
  haveI : IsReduced ((M ⊗[k] F) ⊗[M] L) :=
    isReduced_tensor_of_isAlgebraic (k := M) (A := M ⊗[k] F) (L := L)
  have hswap : (L ⊗[M] (M ⊗[k] F)) ≃+* ((M ⊗[k] F) ⊗[M] L) :=
    (Algebra.TensorProduct.comm M L (M ⊗[k] F)).toRingEquiv
  haveI : IsReduced (L ⊗[M] (M ⊗[k] F)) :=
    isReduced_of_injective hswap.toRingHom hswap.injective
  have hcancel : (L ⊗[k] F) ≃+* (L ⊗[M] (M ⊗[k] F)) :=
    (Algebra.TensorProduct.cancelBaseChange k M M L F).symm.toRingEquiv
  haveI : IsReduced (L ⊗[k] F) :=
    isReduced_of_injective hcancel.toRingHom hcancel.injective
  have hfin : (F ⊗[k] L) ≃+* (L ⊗[k] F) := (Algebra.TensorProduct.comm k F L).toRingEquiv
  exact isReduced_of_injective hfin.toRingHom hfin.injective

/-- **The field case.**  Over a field of characteristic zero the tensor product of two field
extensions is reduced. -/
theorem isReduced_tensor_field_of_charZero
    {k : Type*} [Field k] [CharZero k] {F : Type*} [Field F] [Algebra k F]
    {L : Type*} [Field L] [Algebra k L] :
    IsReduced (F ⊗[k] L) := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k L
  set M : IntermediateField k L := IntermediateField.adjoin k (Set.range (Subtype.val : s → L))
    with hM
  -- the purely transcendental part is a domain after base change
  have hQdom : IsDomain (F ⊗[k] (FractionRing (MvPolynomial s k))) := by
    haveI : IsDomain (F ⊗[k] MvPolynomial s k) := by
      have e : (F ⊗[k] MvPolynomial s k) ≃+* MvPolynomial s F :=
        (MvPolynomial.algebraTensorAlgEquiv k F).toRingEquiv
      exact e.toMulEquiv.isDomain _
    exact isDomain_tensor_of_isFractionRing (k := k) (P := MvPolynomial s k)
      (Q := FractionRing (MvPolynomial s k)) (F := F)
  have hequiv : (F ⊗[k] (FractionRing (MvPolynomial s k))) ≃+* (F ⊗[k] M) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := k) (A₁ := F))
      hs.1.aevalEquivField).toRingEquiv
  haveI : IsDomain (F ⊗[k] M) := hequiv.symm.toMulEquiv.isDomain _
  haveI : IsDomain ((M : Type _) ⊗[k] F) :=
    (Algebra.TensorProduct.comm k M F).toRingEquiv.toMulEquiv.isDomain _
  haveI : CharZero (M : Type _) := charZero_of_injective_algebraMap (algebraMap k M).injective
  haveI : Algebra.IsAlgebraic (M : Type _) L := by
    haveI halg : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range (Subtype.val : s → L))) L :=
      hs.isAlgebraic
    have hle : Algebra.adjoin k (Set.range (Subtype.val : s → L)) ≤ M.toSubalgebra :=
      IntermediateField.algebra_adjoin_le_adjoin k _
    refine ⟨fun x => ?_⟩
    have h0 : IsAlgebraic (Algebra.adjoin k (Set.range (Subtype.val : s → L))) x :=
      Algebra.IsAlgebraic.isAlgebraic x
    exact h0.tower_top_of_subalgebra_le hle
  exact isReduced_tensor_of_algebraic_over_domain (k := k) (F := F) (L := L) (M : Type _)

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.TensorReducedCharZero

/-!
# Reducedness of an arbitrary tensor product over a field of characteristic zero

`isReduced_tensor_field_of_charZero` handles two field extensions.  A Noetherian reduced ring
embeds into the finite product of its minimal quotients, and finite products commute with the
tensor product, so the field case propagates to arbitrary reduced algebras; mathlib's
`IsReduced.tensorProduct_of_flat_of_forall_fg` reduces the general case to finitely generated —
hence Noetherian — subalgebras.

The conclusion is the statement the difference-Galois torsor needs: for a Picard--Vessiot ring `R`
over a base of characteristic zero, `R ⊗_K R` is reduced, hence so is the constants algebra `E`
inside it.
-/

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

/-- A reduced ring embeds into the product of its quotients by the minimal primes. -/
theorem injective_toPi_minimalPrimes {B : Type*} [CommRing B] [IsReduced B]
    (s : Set (Ideal B)) (hs : ∀ p ∈ minimalPrimes B, p ∈ s) (hsp : ∀ p ∈ s, p.IsPrime) :
    Function.Injective (fun b : B => fun p : s => Ideal.Quotient.mk (p : Ideal B) b) := by
  intro a b hab
  have hmem : ∀ p ∈ s, a - b ∈ p := by
    intro p hp
    have h1 : Ideal.Quotient.mk (p : Ideal B) a = Ideal.Quotient.mk (p : Ideal B) b :=
      congrFun hab ⟨p, hp⟩
    have h0 : Ideal.Quotient.mk (p : Ideal B) (a - b) = 0 := by
      rw [map_sub, h1, sub_self]
    exact (Ideal.Quotient.eq_zero_iff_mem).mp h0
  have hnil : a - b ∈ nilradical B := by
    rw [nilradical_eq_sInf]
    refine Submodule.mem_sInf.mpr ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    haveI := hp
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := p) bot_le
    exact hqp (hmem q (hs q hq))
  rw [nilradical_eq_zero B] at hnil
  have hz : a - b = 0 := by simpa using hnil
  exact sub_eq_zero.mp hz

/-- **Base change of a Noetherian reduced ring**, given the minimal quotients. -/
theorem isReduced_tensor_of_isNoetherianRing
    {k : Type*} [Field k] {C : Type*} [CommRing C] [Algebra k C]
    {B : Type*} [CommRing B] [Algebra k B] [IsReduced B] [IsNoetherianRing B]
    (h : ∀ p : Ideal B, p ∈ minimalPrimes B → IsReduced (C ⊗[k] (B ⧸ p))) :
    IsReduced (C ⊗[k] B) := by
  classical
  haveI hfin : Fintype ↥(minimalPrimes B) :=
    (minimalPrimes.finite_of_isNoetherianRing B).fintype
  set ι := ↥(minimalPrimes B) with hι
  set Pi₀ : Type _ := ∀ p : ι, B ⧸ (p : Ideal B) with hPi
  have hprime : ∀ p : ι, (p : Ideal B).IsPrime := fun p => p.2.1.1
  haveI : ∀ p : ι, IsReduced (C ⊗[k] (B ⧸ (p : Ideal B))) := fun p => h _ p.2
  haveI : IsReduced (∀ p : ι, C ⊗[k] (B ⧸ (p : Ideal B))) := inferInstance
  -- the product of the minimal quotients
  let f : B →ₐ[k] Pi₀ := Pi.algHom _ _ (fun p => Ideal.Quotient.mkₐ k (p : Ideal B))
  have hfinj : Function.Injective f :=
    injective_toPi_minimalPrimes (minimalPrimes B) (fun _ hp => hp) (fun p hp => hp.1.1)
  have hCinj : Function.Injective
      (LinearMap.lTensor C f.toLinearMap) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hfinj
  have hmap : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id k C) f) := by
    have hfun : ⇑(Algebra.TensorProduct.map (AlgHom.id k C) f)
        = ⇑(LinearMap.lTensor C f.toLinearMap) := by
      funext ξ
      induction ξ using TensorProduct.induction_on with
      | zero => simp
      | tmul a p => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [hfun]; exact hCinj
  have hpi : (C ⊗[k] Pi₀) ≃+* (∀ p : ι, C ⊗[k] (B ⧸ (p : Ideal B))) :=
    (Algebra.TensorProduct.piRight k k C (fun p : ι => B ⧸ (p : Ideal B))).toRingEquiv
  haveI : IsReduced (C ⊗[k] Pi₀) := isReduced_of_injective hpi.toRingHom hpi.injective
  exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id k C) f).toRingHom hmap

/-- **A field extension tensored with any reduced algebra is reduced**, in characteristic zero. -/
theorem isReduced_tensor_field_algebra_of_charZero
    {k : Type*} [Field k] [CharZero k] {L : Type*} [Field L] [Algebra k L]
    {B : Type*} [CommRing B] [Algebra k B] [IsReduced B] :
    IsReduced (L ⊗[k] B) := by
  classical
  refine IsReduced.tensorProduct_of_flat_of_forall_fg (R := k) (C := L) (A := B) ?_
  intro B₀ hB₀
  haveI : Algebra.FiniteType k B₀ := ⟨(Subalgebra.fg_top B₀).mpr hB₀⟩
  haveI : IsNoetherianRing B₀ := Algebra.FiniteType.isNoetherianRing k B₀
  haveI : IsReduced B₀ := isReduced_of_injective B₀.val Subtype.val_injective
  refine isReduced_tensor_of_isNoetherianRing (k := k) (C := L) (B := B₀) ?_
  intro p hp
  haveI : p.IsPrime := hp.1.1
  haveI : IsReduced (L ⊗[k] (FractionRing (B₀ ⧸ p))) :=
    isReduced_tensor_field_of_charZero (k := k) (F := L) (L := FractionRing (B₀ ⧸ p))
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id k L)
        (IsScalarTower.toAlgHom k (B₀ ⧸ p) (FractionRing (B₀ ⧸ p)))) := by
    have hb : Function.Injective (algebraMap (B₀ ⧸ p) (FractionRing (B₀ ⧸ p))) :=
      IsFractionRing.injective _ _
    have hlin : Function.Injective (LinearMap.lTensor L
        (IsScalarTower.toAlgHom k (B₀ ⧸ p) (FractionRing (B₀ ⧸ p))).toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hb
    have hfun : ⇑(Algebra.TensorProduct.map (AlgHom.id k L)
          (IsScalarTower.toAlgHom k (B₀ ⧸ p) (FractionRing (B₀ ⧸ p))))
        = ⇑(LinearMap.lTensor L
          (IsScalarTower.toAlgHom k (B₀ ⧸ p) (FractionRing (B₀ ⧸ p))).toLinearMap) := by
      funext ξ
      induction ξ using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [hfun]; exact hlin
  exact isReduced_of_injective _ hinj

/-- **The tensor product of two reduced algebras over a field of characteristic zero is
reduced.**  This is the statement mathlib is missing. -/
private theorem isReduced_tensorProduct_of_charZero
    {k : Type*} [Field k] [CharZero k]
    {A : Type*} [CommRing A] [Algebra k A] [IsReduced A]
    {B : Type*} [CommRing B] [Algebra k B] [IsReduced B] :
    IsReduced (A ⊗[k] B) := by
  classical
  refine IsReduced.tensorProduct_of_flat_of_forall_fg (R := k) (C := A) (A := B) ?_
  intro B₀ hB₀
  haveI : Algebra.FiniteType k B₀ := ⟨(Subalgebra.fg_top B₀).mpr hB₀⟩
  haveI : IsNoetherianRing B₀ := Algebra.FiniteType.isNoetherianRing k B₀
  haveI : IsReduced B₀ := isReduced_of_injective B₀.val Subtype.val_injective
  refine isReduced_tensor_of_isNoetherianRing (k := k) (C := A) (B := B₀) ?_
  intro p hp
  haveI : p.IsPrime := hp.1.1
  haveI : IsReduced (A ⊗[k] (FractionRing (B₀ ⧸ p))) := by
    have hcomm : (A ⊗[k] (FractionRing (B₀ ⧸ p))) ≃+* ((FractionRing (B₀ ⧸ p)) ⊗[k] A) :=
      (Algebra.TensorProduct.comm k A (FractionRing (B₀ ⧸ p))).toRingEquiv
    haveI : IsReduced ((FractionRing (B₀ ⧸ p)) ⊗[k] A) :=
      isReduced_tensor_field_algebra_of_charZero (k := k) (L := FractionRing (B₀ ⧸ p)) (B := A)
    exact isReduced_of_injective hcomm.toRingHom hcomm.injective
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id k A)
        (IsScalarTower.toAlgHom k (B₀ ⧸ p) (FractionRing (B₀ ⧸ p)))) := by
    have hb : Function.Injective (algebraMap (B₀ ⧸ p) (FractionRing (B₀ ⧸ p))) :=
      IsFractionRing.injective _ _
    have hlin : Function.Injective (LinearMap.lTensor A
        (IsScalarTower.toAlgHom k (B₀ ⧸ p) (FractionRing (B₀ ⧸ p))).toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hb
    have hfun : ⇑(Algebra.TensorProduct.map (AlgHom.id k A)
          (IsScalarTower.toAlgHom k (B₀ ⧸ p) (FractionRing (B₀ ⧸ p))))
        = ⇑(LinearMap.lTensor A
          (IsScalarTower.toAlgHom k (B₀ ⧸ p) (FractionRing (B₀ ⧸ p))).toLinearMap) := by
      funext ξ
      induction ξ using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [hfun]; exact hlin
  exact isReduced_of_injective _ hinj

/-- **The tensor square of a reduced algebra over a characteristic-zero field is reduced.** -/
theorem isReduced_tensorSquare_of_charZero
    {k : Type*} [Field k] [CharZero k] {R : Type*} [CommRing R] [Algebra k R] [IsReduced R] :
    IsReduced (R ⊗[k] R) :=
  isReduced_tensorProduct_of_charZero

/-- **Every subalgebra of the tensor square is reduced.**  This is the form the difference-Galois
torsor consumes: the constants algebra `E` sits inside `R ⊗_K R`, and its reducedness is the one
instance hypothesis the Galois correspondence's separation argument carries. -/
theorem isReduced_subalgebra_tensorSquare_of_charZero
    {k : Type*} [Field k] [CharZero k] {R : Type*} [CommRing R] [Algebra k R] [IsReduced R]
    (E : Subalgebra k (R ⊗[k] R)) : IsReduced E := by
  haveI : IsReduced (R ⊗[k] R) := isReduced_tensorSquare_of_charZero
  exact isReduced_of_injective E.val Subtype.val_injective

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.RootFieldTransport
import Mathlib.FieldTheory.Normal.Closure

/-!
# Splitting fields under base-field equivalence

This module supplies three transport facts used when a concrete extension is identified with a
generic polynomial model:

* a splitting-field structure transports across an equivalence of base fields;
* a normal closure of a simple extension is a splitting field of the generator's minimal
  polynomial;
* automorphism groups over equivalent base fields are canonically equivalent.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

/-- A splitting-field structure transports across an equivalence of base fields when the two
scalar maps into the ambient field agree. -/
theorem isSplittingField_map_algEquiv_of_algebraMap_eq
    {F A L : Type*} [Field F] [Field A] [Field L]
    [Algebra F L] [Algebra A L]
    (e : F ≃+* A)
    (hAlg : algebraMap F L = (algebraMap A L).comp e.toRingHom)
    (p : Polynomial F)
    [Polynomial.IsSplittingField A L (p.map e.toRingHom)] :
    Polynomial.IsSplittingField F L p := by
  let C := Algebra.adjoin F (p.rootSet L)
  have hpoly :
      Polynomial.map (algebraMap A L) (p.map e.toRingHom) =
        Polynomial.map (algebraMap F L) p := by
    rw [Polynomial.map_map, hAlg]
  have hroot : (p.map e.toRingHom).rootSet L = p.rootSet L := by
    simp only [Polynomial.rootSet, Polynomial.aroots, hpoly]
  constructor
  · have h := Polynomial.IsSplittingField.splits L (p.map e.toRingHom)
    rwa [hpoly] at h
  · have hA (a : A) : algebraMap A L a ∈ C := by
      have hmem := C.algebraMap_mem (e.symm a)
      rw [hAlg, RingHom.comp_apply] at hmem
      simpa using hmem
    let D : Subalgebra A L :=
      { carrier := C
        mul_mem' := C.mul_mem
        add_mem' := C.add_mem
        algebraMap_mem' := hA }
    have hle : Algebra.adjoin A ((p.map e.toRingHom).rootSet L) ≤ D := by
      rw [Algebra.adjoin_le_iff]
      intro x hx
      change x ∈ C
      rw [hroot] at hx
      exact Algebra.subset_adjoin hx
    have htop : D = ⊤ := by
      have hgen : Algebra.adjoin A ((p.map e.toRingHom).rootSet L) = ⊤ :=
        Polynomial.IsSplittingField.adjoin_rootSet'
      rw [hgen] at hle
      exact top_unique hle
    apply le_antisymm le_top
    intro x _
    have hx : x ∈ D := by rw [htop]; trivial
    exact hx

/-- The normal closure of a simple algebraic extension is the splitting field of the minimal
polynomial of its chosen generator. -/
theorem isSplittingField_minpoly_of_isNormalClosure_of_adjoin_singleton_eq_top
    {F S L : Type*} [Field F] [Field S] [Field L]
    [Algebra F S] [Algebra F L]
    [Algebra.IsAlgebraic F S] [Algebra.IsAlgebraic F L]
    [IsNormalClosure F S L]
    (a : S) (ha : IsIntegral F a)
    (hgen : IntermediateField.adjoin F {a} = ⊤) :
    Polynomial.IsSplittingField F L (minpoly F a) := by
  let p := minpoly F a
  have hroot (f : S →ₐ[F] L) : f a ∈ p.rootSet L := by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero ha, ?_⟩
    calc
      Polynomial.aeval (f a) p = f (Polynomial.aeval a p) := by
        simp [Polynomial.aeval_algHom_apply]
      _ = 0 := by rw [minpoly.aeval F a, map_zero]
  have hle : IntermediateField.normalClosure F S L ≤ rootField F (L := L) p := by
    rw [normalClosure_le_iff]
    intro f
    rintro _ ⟨x, rfl⟩
    let C := IntermediateField.comap f (rootField F (L := L) p)
    have haC : a ∈ C :=
      IntermediateField.subset_adjoin F (p.rootSet L) (hroot f)
    have htopC : C = ⊤ := by
      apply top_unique
      rw [← hgen, IntermediateField.adjoin_le_iff]
      intro y hy
      simpa only [Set.mem_singleton_iff] using hy ▸ haC
    have hxC : x ∈ C := by rw [htopC]; trivial
    exact hxC
  have hnormalTop : IntermediateField.normalClosure F S L = ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff.mp
      (inferInstance : IsNormalClosure F S L)).2
  have hrootTop : rootField F (L := L) p = ⊤ := by
    apply top_unique
    rw [← hnormalTop]
    exact hle
  constructor
  · exact (inferInstance : IsNormalClosure F S L).splits a
  · have halg : ∀ x ∈ p.rootSet L, IsAlgebraic F x := by
      intro x hx
      rw [Polynomial.mem_rootSet] at hx
      exact ⟨p, hx.1, hx.2⟩
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
    rw [show IntermediateField.adjoin F (p.rootSet L) = ⊤ from hrootTop]
    exact IntermediateField.top_toSubalgebra

/-- Automorphisms fixing one base field are the same as automorphisms fixing an equivalent base
field with the same image in the ambient extension. -/
noncomputable def autEquivOfBaseEquiv
    {F A L : Type*} [Field F] [Field A] [Field L]
    [Algebra F L] [Algebra A L]
    (e : F ≃+* A)
    (hAlg : algebraMap F L = (algebraMap A L).comp e.toRingHom) :
    (L ≃ₐ[F] L) ≃* (L ≃ₐ[A] L) where
  toFun σ :=
    { toRingEquiv := σ.toRingEquiv
      commutes' := fun a => by
        have h := σ.commutes (e.symm a)
        rw [hAlg, RingHom.comp_apply] at h
        simpa using h }
  invFun τ :=
    { toRingEquiv := τ.toRingEquiv
      commutes' := fun x => by
        rw [hAlg, RingHom.comp_apply]
        exact τ.commutes (e x) }
  left_inv σ := by ext x; rfl
  right_inv τ := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

end

end GaloisForLFunctions.HTGeometry

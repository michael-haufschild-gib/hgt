import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Set.Card

/-! The image of a finite field in another field is the full root set
of `X^q - X` for its cardinality `q`. Equal cardinalities therefore
identify embedded residue fields by an equivalence over the ambient field. -/

noncomputable section

open Polynomial

namespace GlobalTheory.Reciprocity

private theorem range_eq_fixed_points_card {F S : Type*} [Field F] [Field S] [Finite F]
    (f : F →+* S) : (f.range : Set S) = {x | x ^ Nat.card F = x} := by
  classical
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  letI : Fintype F := Fintype.ofFinite F
  let P : S[X] := X ^ q - X
  have hpD : P.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq S hq
  have hp0 : P ≠ 0 := fun h => by rw [h, natDegree_zero] at hpD; omega
  have hsub : (f.range : Set S) ⊆ ({x | x ∈ P.roots.toFinset} : Set S) := by
    rintro _ ⟨x, rfl⟩
    rw [Set.mem_setOf_eq, Multiset.mem_toFinset, mem_roots hp0, IsRoot.def,
      eval_sub, eval_pow, eval_X, ← map_pow]
    have hx : x ^ q = x := by
      rw [show q = Fintype.card F from Nat.card_eq_fintype_card]
      exact FiniteField.pow_card x
    rw [hx, sub_self]
  have hrange : (f.range : Set S).ncard = q := by
    rw [RingHom.coe_range, ← Set.image_univ, Set.ncard_image_of_injective _ f.injective,
      Set.ncard_univ]
  have hcard : ({x | x ∈ P.roots.toFinset} : Set S).ncard ≤ (f.range : Set S).ncard := by
    rw [hrange]
    change (↑P.roots.toFinset : Set S).ncard ≤ q
    rw [Set.ncard_coe_finset, ← hpD]
    exact (Multiset.toFinset_card_le _).trans (card_roots' P)
  have hset : (f.range : Set S) = (↑P.roots.toFinset : Set S) :=
    Set.eq_of_subset_of_ncard_le hsub hcard (Finset.finite_toSet _)
  rw [hset]
  ext x
  rw [Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset, mem_roots hp0, IsRoot.def,
    eval_sub, eval_pow, eval_X, sub_eq_zero]

theorem exists_ringEquiv_of_same_finite_image_card {F F' S : Type*}
    [Field F] [Field F'] [Field S] [Finite F] [Finite F']
    (f : F →+* S) (f' : F' →+* S) (h : Nat.card F = Nat.card F') :
    ∃ e : F ≃+* F', ∀ x : F, f' (e x) = f x := by
  have hr : f.range = f'.range := SetLike.coe_injective (by
    rw [range_eq_fixed_points_card, range_eq_fixed_points_card, h])
  let e := RingEquiv.ofBijective f.rangeRestrict ⟨f.rangeRestrict.injective, f.rangeRestrict_surjective⟩
  let e' := RingEquiv.ofBijective f'.rangeRestrict ⟨f'.rangeRestrict.injective, f'.rangeRestrict_surjective⟩
  refine ⟨(e.trans (RingEquiv.subringCongr hr)).trans e'.symm, fun x => ?_⟩
  have he (z : f'.range) : f' (e'.symm z) = (z : S) :=
    congrArg Subtype.val (e'.apply_symm_apply z)
  exact he (RingEquiv.subringCongr hr (e x))

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_ringEquiv_of_same_finite_image_card

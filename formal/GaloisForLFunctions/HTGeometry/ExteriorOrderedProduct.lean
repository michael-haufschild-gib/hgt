import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.Data.Finset.Sort

/-!
# Ordered wedges and Plücker expansions in an exterior algebra

For a linearly ordered index set, the increasing wedge of a finite index set is the product of the
generators taken in increasing order.  It agrees with the canonical `Finset`-indexed basis of the
exterior algebra of a free module, and an ordered product of factors `1 + c_i e_i` expands into the
sum of its Plücker coordinates:

```text
∏_{i ∈ S}^∧ (1 + c_i e_i) = ∑_{T ⊆ S} (∏_{i ∈ T} c_i) e_T.
```

Adjoining a new largest index multiplies the wedge on the right, so no permutation sign ever
appears.
-/

open scoped BigOperators

namespace HTGeometry

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder I]

/-- The wedge of the generators indexed by a finite set, taken in increasing order. -/
def orderedWedge (v : I → M) (T : Finset I) : ExteriorAlgebra R M :=
  ((T.sort (· ≤ ·)).map fun i => ExteriorAlgebra.ι R (v i)).prod

@[simp] theorem orderedWedge_empty (v : I → M) : orderedWedge (R := R) v ∅ = 1 := by
  rw [orderedWedge]
  simp

/-- Adjoining a largest element appends it to the sorted list. -/
theorem sort_insert_of_forall_lt [DecidableEq I] {T : Finset I} {a : I} (h : ∀ x ∈ T, x < a) :
    (insert a T).sort (· ≤ ·) = T.sort (· ≤ ·) ++ [a] := by
  have ha : a ∉ T := fun hmem => lt_irrefl a (h a hmem)
  have hperm : ((insert a T).sort (· ≤ ·)).Perm (T.sort (· ≤ ·) ++ [a]) := by
    have hcons : ((insert a T).sort (· ≤ ·)).Perm (a :: T.sort (· ≤ ·)) := by
      apply (Multiset.coe_eq_coe (α := I)).mp
      rw [Finset.sort_eq, Finset.insert_val_of_notMem ha, ← Multiset.cons_coe, Finset.sort_eq]
    exact hcons.trans (List.perm_append_singleton a _).symm
  refine hperm.eq_of_pairwise' (Finset.pairwise_sort _ _) ?_
  refine List.pairwise_append.mpr ⟨Finset.pairwise_sort _ _, by simp, ?_⟩
  intro x hx y hy
  have hxT : x ∈ T := (Finset.mem_sort _).mp hx
  have hya : y = a := by simpa using hy
  exact hya ▸ (h x hxT).le

/-- Adjoining a largest index multiplies the ordered wedge on the right. -/
theorem orderedWedge_insert [DecidableEq I] (v : I → M) {T : Finset I} {a : I}
    (h : ∀ x ∈ T, x < a) :
    orderedWedge (R := R) v (insert a T) =
      orderedWedge (R := R) v T * ExteriorAlgebra.ι R (v a) := by
  rw [orderedWedge, orderedWedge, sort_insert_of_forall_lt h, List.map_append, List.prod_append]
  simp

/-- The ordered wedge of a basis family is the canonical exterior-algebra basis vector. -/
theorem orderedWedge_eq_basis (b : Module.Basis I R M) (T : Finset I) :
    orderedWedge (R := R) b T = b.ExteriorAlgebra T := by
  classical
  rw [ExteriorAlgebra.basis_apply_ofCard b (rfl : T.card = T.card), ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply, orderedWedge]
  congr 1
  refine List.ext_getElem ?_ ?_
  · rw [List.length_map, List.length_ofFn, Finset.length_sort]
  · intro k hk hk'
    rw [List.getElem_map, List.getElem_ofFn]
    congr 2

/-- The ordered product of the factors `1 + c_i e_i`, taken in increasing order. -/
def orderedPluckerProduct (v : I → M) (c : I → R) (S : Finset I) : ExteriorAlgebra R M :=
  ((S.sort (· ≤ ·)).map fun i => 1 + c i • ExteriorAlgebra.ι R (v i)).prod

@[simp] theorem orderedPluckerProduct_empty (v : I → M) (c : I → R) :
    orderedPluckerProduct (R := R) v c ∅ = 1 := by
  rw [orderedPluckerProduct]
  simp

theorem orderedPluckerProduct_insert [DecidableEq I] (v : I → M) (c : I → R) {S : Finset I}
    {a : I} (h : ∀ x ∈ S, x < a) :
    orderedPluckerProduct (R := R) v c (insert a S) =
      orderedPluckerProduct (R := R) v c S * (1 + c a • ExteriorAlgebra.ι R (v a)) := by
  rw [orderedPluckerProduct, orderedPluckerProduct, sort_insert_of_forall_lt h, List.map_append,
    List.prod_append]
  simp

/-- **Plücker expansion of an ordered product.**  The coefficient of the increasing wedge `e_T` is
the product of the scalars over `T`. -/
theorem orderedPluckerProduct_eq_sum [DecidableEq I] (v : I → M) (c : I → R) (S : Finset I) :
    orderedPluckerProduct (R := R) v c S =
      ∑ T ∈ S.powerset, (∏ i ∈ T, c i) • orderedWedge (R := R) v T := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S ha ih =>
    have hnot : a ∉ S := fun hmem => lt_irrefl a (ha a hmem)
    have hdisj : Disjoint S.powerset (Finset.image (insert a) S.powerset) := by
      refine Finset.disjoint_left.mpr ?_
      intro T hT hTimg
      obtain ⟨T', hT', hTT'⟩ := Finset.mem_image.mp hTimg
      have haT : a ∈ T := by rw [← hTT']; exact Finset.mem_insert_self a T'
      exact hnot (Finset.mem_powerset.mp hT haT)
    have hinj : Set.InjOn (insert a) (S.powerset : Set (Finset I)) := by
      intro T₁ h₁ T₂ h₂ heq
      have ha₁ : a ∉ T₁ := fun hmem => hnot (Finset.mem_powerset.mp h₁ hmem)
      have ha₂ : a ∉ T₂ := fun hmem => hnot (Finset.mem_powerset.mp h₂ hmem)
      rw [← Finset.erase_insert ha₁, ← Finset.erase_insert ha₂, heq]
    rw [orderedPluckerProduct_insert v c ha, ih, Finset.powerset_insert,
      Finset.sum_union hdisj, Finset.sum_image hinj]
    rw [mul_add, mul_one]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTS : T ⊆ S := Finset.mem_powerset.mp hT
    have haT : a ∉ T := fun hmem => hnot (hTS hmem)
    have hlt : ∀ x ∈ T, x < a := fun x hx => ha x (hTS hx)
    rw [Finset.prod_insert haT, orderedWedge_insert v hlt, smul_mul_assoc, mul_smul_comm,
      smul_smul]
    congr 1
    ring

end HTGeometry

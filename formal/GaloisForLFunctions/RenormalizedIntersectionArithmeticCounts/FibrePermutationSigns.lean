import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Orientation signs from actual permutation fibres

An invariant finite partition decomposes a permutation into restrictions
extended by identity. Its sign is the product of the fibre signs. When
each nonempty fibre is one cycle, the exponent is the number of points
plus the number of fibres. Singleton fibres are retained explicitly.
-/

noncomputable section
open Finset Equiv
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
variable {X Y : Type*} [Fintype X] [Fintype Y]
attribute [local instance] Classical.propDecidable

/-- Restrict a permutation to a fibre of an invariant arithmetic label. -/
def labelledFibrePerm (f : Perm X) (π : X → Y) (hπ : ∀ x, π (f x) = π x) (y : Y) :
    Perm {x : X // π x = y} :=
  f.subtypePerm fun x => by rw [hπ x]

omit [Fintype X] [Fintype Y] in
/-- Iteration of the restricted permutation is iteration in the actual ambient set. -/
theorem labelledFibrePerm_pow_val (f : Perm X) (π : X → Y)
    (hπ : ∀ x, π (f x) = π x) (y : Y) (n : ℕ) (x : {x : X // π x = y}) :
    ((labelledFibrePerm f π hπ y ^ n) x).val = (f ^ n) x.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply]
    change f (((labelledFibrePerm f π hπ y ^ n) x).val) = f ((f ^ n) x.val)
    exact congrArg f ih

omit [Fintype X] [Fintype Y] in
private theorem fibreBlock_apply (f : Perm X) (π : X → Y) (hπ : ∀ x, π (f x) = π x)
    (y : Y) (x : X) :
    Perm.ofSubtype (labelledFibrePerm f π hπ y) x = if π x = y then f x else x := by
  by_cases hx : π x = y
  · rw [if_pos hx, Perm.ofSubtype_apply_of_mem (a := x) _ hx]
    rfl
  · rw [if_neg hx, Perm.ofSubtype_apply_of_not_mem (a := x) _ hx]

/-- The sign is the product of the signs on the actual disjoint fibres. -/
theorem sign_eq_prod_labelledFibrePerm (f : Perm X) (π : X → Y)
    (hπ : ∀ x, π (f x) = π x) :
    Perm.sign f = ∏ y : Y, Perm.sign (labelledFibrePerm f π hπ y) := by
  classical
  let b := fun y => Perm.ofSubtype (labelledFibrePerm f π hπ y)
  have hlist (l : List Y) (hl : l.Nodup) (x : X) :
      (l.map b).prod x = if π x ∈ l then f x else x := by
    induction l with
    | nil => simp
    | cons y l ih =>
      rw [List.map_cons, List.prod_cons, Perm.mul_apply, ih (List.nodup_cons.mp hl).2]
      by_cases hx : π x ∈ l
      · have hxy : π x ≠ y := fun he => (List.nodup_cons.mp hl).1 (he ▸ hx)
        simp only [b, fibreBlock_apply, hπ, if_neg hxy,
          List.mem_cons, hx, or_true, ↓reduceIte]
      · simp only [b, fibreBlock_apply, List.mem_cons, hx, or_false, ↓reduceIte]
  obtain ⟨l, hl, hall⟩ := Finite.exists_univ_list Y
  have he : (l.map b).prod = f := Perm.ext fun x => by rw [hlist l hl x, if_pos (hall _)]
  have huniv : l.toFinset = univ := by ext y; simp only [List.mem_toFinset, mem_univ, iff_true]; exact hall y
  calc
    Perm.sign f = Perm.sign (l.map b).prod := congrArg Perm.sign he.symm
    _ = _ := by
      rw [map_list_prod, List.map_map]
      simp only [b, Function.comp_def, Perm.sign_ofSubtype]
      rw [← List.prod_toFinset _ hl, huniv]

/-- A transitive permutation of a nonempty finite set has sign (-1)^(card+1), including singletons. -/
theorem sign_of_transitive_perm [Nonempty X] (f : Perm X)
    (hf : f.IsCycleOn Set.univ) : Perm.sign f = (-1 : ℤˣ) ^ (Fintype.card X + 1) := by
  classical
  cases subsingleton_or_nontrivial X with
  | inl h =>
    letI := h
    have he : f = 1 := Subsingleton.elim _ _
    letI : Unique X := { default := Classical.choice ‹Nonempty X›, uniq := fun x => Subsingleton.elim _ _ }
    rw [he, Fintype.card_unique]
    simp
  | inr h =>
    letI := h
    have hc : f.IsCycle := Perm.isCycle_iff_exists_isCycleOn.mpr
      ⟨Set.univ, Set.nontrivial_univ, hf, fun _ _ => Set.mem_univ _⟩
    have hs : f.support = univ := by
      ext x
      simp only [Perm.mem_support, mem_univ, iff_true]
      exact hf.apply_ne Set.nontrivial_univ (Set.mem_univ x)
    rw [hc.sign, hs, card_univ, pow_succ]
    simp only [mul_neg_one]

/-- Transitive nonempty label fibres determine the entire permutation sign, retaining fixed points. -/
theorem sign_eq_pow_card_add_card (f : Perm X) (π : X → Y)
    (hπ : ∀ x, π (f x) = π x) (hs : Function.Surjective π)
    (hc : ∀ y, (labelledFibrePerm f π hπ y).IsCycleOn Set.univ) :
    Perm.sign f = (-1 : ℤˣ) ^ (Fintype.card X + Fintype.card Y) := by
  classical
  have hcard : (∑ y : Y, Fintype.card {x : X // π x = y}) = Fintype.card X := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv π)
  rw [sign_eq_prod_labelledFibrePerm f π hπ]
  calc
    _ = ∏ y : Y, (-1 : ℤˣ) ^ (Fintype.card {x : X // π x = y} + 1) := by
      apply prod_congr rfl
      intro y _
      obtain ⟨x, hx⟩ := hs y
      letI : Nonempty {x : X // π x = y} := ⟨⟨x, hx⟩⟩
      convert! sign_of_transitive_perm _ (hc y) using 1
      congr 2
      exact Subsingleton.elim _ _
    _ = _ := by
      rw [prod_pow_eq_pow_sum, sum_add_distrib, hcard]
      simp only [sum_const, card_univ, smul_eq_mul, mul_one]

#print axioms sign_eq_pow_card_add_card

#print axioms labelledFibrePerm_pow_val
#print axioms sign_eq_prod_labelledFibrePerm
#print axioms sign_of_transitive_perm
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

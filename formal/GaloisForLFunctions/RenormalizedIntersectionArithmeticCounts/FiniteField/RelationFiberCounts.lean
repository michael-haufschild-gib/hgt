import Mathlib.SetTheory.Cardinal.Finite

/-!
# Combining fibers with a disjoint section

Injectively indexed fibers of a fixed cardinality can be counted together
with a section over a disjoint family of base points. The proof embeds
the corresponding disjoint union into the literal relation.
-/

namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

/-- A disjoint section adds its full size to a family of constant-cardinality fibers. -/
theorem card_relation_lower_bound_add_section
    {I J Y Z : Type*} [Finite I] [Finite J] [Finite Y] [Finite Z]
    (P : Y → Z → Prop) (f : I → Y) (g : J → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ i j, f i ≠ g j) (z : J → Z) (hz : ∀ j, P (g j) (z j))
    (n : ℕ) (hn : ∀ i, Nat.card {w : Z | P (f i) w} = n) :
    Nat.card I * n + Nat.card J ≤ Nat.card {t : Y × Z // P t.1 t.2} := by
  classical
  letI := Fintype.ofFinite I
  let F : (Σ i : I, {w : Z | P (f i) w}) ⊕ J → {t : Y × Z // P t.1 t.2} :=
    Sum.elim (fun x => ⟨(f x.1, x.2.val), x.2.property⟩) (fun j => ⟨(g j, z j), hz j⟩)
  have hF : Function.Injective F := by
    intro x y h
    have hval := congrArg Subtype.val h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        have hij := hf (congrArg Prod.fst hval)
        have hzw := congrArg Prod.snd hval
        obtain ⟨i, w⟩ := x
        obtain ⟨j, v⟩ := y
        change i = j at hij
        subst j
        have hwv : w = v := Subtype.ext hzw
        subst v
        rfl
      | inr y => exact (hfg x.1 y (congrArg Prod.fst hval)).elim
    | inr x =>
      cases y with
      | inl y => exact (hfg y.1 x (congrArg Prod.fst hval).symm).elim
      | inr y => exact congrArg Sum.inr (hg (congrArg Prod.fst hval))
  letI : Finite (Σ i : I, {w : Z | P (f i) w}) :=
    Finite.of_injective (F ∘ Sum.inl) (hF.comp Sum.inl_injective)
  have hc := Nat.card_le_card_of_injective F hF
  rw [Nat.card_sum, Nat.card_sigma, Finset.sum_const_nat (fun i _ => hn i),
    Finset.card_univ, ← Nat.card_eq_fintype_card] at hc
  exact hc

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

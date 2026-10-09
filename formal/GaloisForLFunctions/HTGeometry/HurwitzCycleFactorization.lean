import GaloisForLFunctions.HTGeometry.HurwitzLeafIsolation
import GaloisForLFunctions.HTGeometry.CycleLeafDeletion
import Mathlib.Data.Fintype.EquivFin

open Equiv Set
namespace GaloisForLFunctions.HTGeometry.HurwitzFactorization
universe u

theorem related_minimal_cycle_factorizations_of_card (d : ℕ) :
    ∀ (α : Type u) [Fintype α] [DecidableEq α] (l r : List (Perm α)),
      Fintype.card α = d →
      (∀ g ∈ l, g.IsSwap) → (∀ g ∈ r, g.IsSwap) →
      l.length + 1 = d → r.length + 1 = d →
      l.prod = r.prod → l.prod.IsCycleOn univ → Related l r := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro α instF instD l r hcard hl hr hlen hrlen hprod hcycle
      rcases subsingleton_or_nontrivial α with hsub | hnontrivial
      · have hle : Fintype.card α ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hsub
        have hl0 : l = [] := List.length_eq_zero_iff.mp (by omega)
        have hr0 : r = [] := List.length_eq_zero_iff.mp (by omega)
        subst l
        subst r
        exact Related.refl []
      · letI : Nontrivial α := hnontrivial
        let a : α := Classical.choice (inferInstance : Nonempty α)
        obtain ⟨p, hp, hpfix, hpswap⟩ := isolate_chosen_sheet l hl (hlen.trans hcard.symm) hcycle a
        have hrcycle : r.prod.IsCycleOn univ := hprod ▸ hcycle
        obtain ⟨q, hq, hqfix, hqswap⟩ := isolate_chosen_sheet r hr (hrlen.trans hcard.symm) hrcycle a
        have hq' : Related r (q ++ [swap a (l.prod⁻¹ a)]) := by
          simpa only [← hprod] using hq
        let s : Perm α := swap a (l.prod⁻¹ a)
        have hp0 : l.prod = p.prod * s := by
          simpa only [List.prod_append, List.prod_singleton] using hp.prod_eq
        have hq0 : r.prod = q.prod * s := by
          simpa only [List.prod_append, List.prod_singleton] using hq'.prod_eq
        have hpq : p.prod = q.prod := mul_right_cancel ((hp0.symm.trans hprod).trans hq0)
        have hpσ : p.prod = l.prod * s := by
          have h := congrArg (fun f : Perm α => f * s) hp0.symm
          simpa [s, mul_assoc] using h
        let β := {x : α // x ≠ a}
        let P : List (Perm β) := eraseSheetWord p a hpfix
        let Q : List (Perm β) := eraseSheetWord q a hqfix
        have hPembed : Perm.ofSubtype P.prod = p.prod := ofSubtype_prod_eraseSheetWord p a hpfix
        have hQembed : Perm.ofSubtype Q.prod = q.prod := ofSubtype_prod_eraseSheetWord q a hqfix
        have hpfixprod : p.prod a = a := by
          rw [← hPembed]
          exact Perm.ofSubtype_apply_of_not_mem _ (by simp)
        have hPeq : P.prod = eraseSheetPerm p.prod a hpfixprod := by
          apply Perm.ofSubtype_injective
          rw [hPembed, ofSubtype_eraseSheetPerm]
        have hpcycle : p.prod.IsCycleOn {x | x ≠ a} := by
          rw [hpσ]
          exact isCycleOn_delete_sheet l.prod hcycle a
        have hPcycle : P.prod.IsCycleOn univ := by
          rw [hPeq]
          exact isCycleOn_eraseSheetPerm p.prod a hpfixprod hpcycle
        have hPQ : P.prod = Q.prod := by
          apply Perm.ofSubtype_injective
          rw [hPembed, hQembed, hpq]
        have hβ : Fintype.card β + 1 = Fintype.card α := card_erase_sheet a
        have hβlt : Fintype.card β < d := by omega
        have hpLen : l.length = p.length + 1 := by
          simpa only [List.length_append, List.length_singleton] using hp.length_eq
        have hqLen : r.length = q.length + 1 := by
          simpa only [List.length_append, List.length_singleton] using hq'.length_eq
        have hPLen : P.length + 1 = Fintype.card β := by
          change (eraseSheetWord p a hpfix).length + 1 = Fintype.card β
          rw [length_eraseSheetWord]
          omega
        have hQLen : Q.length + 1 = Fintype.card β := by
          change (eraseSheetWord q a hqfix).length + 1 = Fintype.card β
          rw [length_eraseSheetWord]
          omega
        have hPswap : ∀ g ∈ P, g.IsSwap := isSwap_eraseSheetWord p a hpfix hpswap
        have hQswap : ∀ g ∈ Q, g.IsSwap := isSwap_eraseSheetWord q a hqfix hqswap
        have hsmall : Related P Q := ih (Fintype.card β) hβlt β P Q rfl
          hPswap hQswap hPLen hQLen hPQ hPcycle
        have hpqRel : Related p q := by
          have h := hsmall.map (Perm.ofSubtype (p := fun x : α => x ≠ a))
          have hPmap : P.map (Perm.ofSubtype (p := fun x : α => x ≠ a)) = p :=
            map_ofSubtype_eraseSheetWord p a hpfix
          have hQmap : Q.map (Perm.ofSubtype (p := fun x : α => x ≠ a)) = q :=
            map_ofSubtype_eraseSheetWord q a hqfix
          rw [hPmap, hQmap] at h
          exact h
        exact hp.trans ((hpqRel.append [s]).trans hq'.symm)

/-- Every two minimal transposition factorizations of the same full cycle are connected
by product-preserving adjacent Hurwitz moves. -/
theorem related_minimal_cycle_factorizations {α : Type u} [Fintype α] [DecidableEq α]
    (l r : List (Perm α)) (hl : ∀ g ∈ l, g.IsSwap) (hr : ∀ g ∈ r, g.IsSwap)
    (hlen : l.length + 1 = Fintype.card α) (hrlen : r.length + 1 = Fintype.card α)
    (hprod : l.prod = r.prod) (hcycle : l.prod.IsCycleOn univ) : Related l r :=
  related_minimal_cycle_factorizations_of_card (Fintype.card α) α l r rfl
    hl hr hlen hrlen hprod hcycle

end GaloisForLFunctions.HTGeometry.HurwitzFactorization

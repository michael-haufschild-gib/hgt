import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.Card

open Equiv Set
namespace GaloisForLFunctions.HTGeometry.HurwitzFactorization
noncomputable section
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem ne_iff_of_perm_fixed (f : Perm α) (a : α) (ha : f a = a) (x : α) :
    f x ≠ a ↔ x ≠ a := by
  have h : f x = a ↔ x = a := by
    conv_lhs => rw [← ha]
    exact f.injective.eq_iff
  exact not_congr h

def eraseSheetPerm (f : Perm α) (a : α) (ha : f a = a) : Perm {x : α // x ≠ a} :=
  f.subtypePerm (ne_iff_of_perm_fixed f a ha)

theorem ofSubtype_eraseSheetPerm (f : Perm α) (a : α) (ha : f a = a) :
    Perm.ofSubtype (eraseSheetPerm f a ha) = f := by
  apply Perm.ofSubtype_subtypePerm
  intro x hx hxa
  subst x
  exact hx ha

theorem isSwap_eraseSheetPerm [Fintype α] (f : Perm α) (a : α) (ha : f a = a)
    (hf : f.IsSwap) : (eraseSheetPerm f a ha).IsSwap := by
  apply Perm.card_support_eq_two.mp
  have h : (Perm.ofSubtype (eraseSheetPerm f a ha)).support.card = 2 := by
    rw [ofSubtype_eraseSheetPerm]
    exact Perm.card_support_eq_two.mpr hf
  simpa only [Perm.support_ofSubtype, Finset.card_map] using h

def eraseSheetWord (l : List (Perm α)) (a : α) (h : ∀ g ∈ l, g a = a) :
    List (Perm {x : α // x ≠ a}) :=
  l.attach.map fun g => eraseSheetPerm g.val a (h g.val g.property)

omit [DecidableEq α] in
@[simp] theorem length_eraseSheetWord (l : List (Perm α)) (a : α)
    (h : ∀ g ∈ l, g a = a) : (eraseSheetWord l a h).length = l.length := by
  simp [eraseSheetWord]

theorem map_ofSubtype_eraseSheetWord (l : List (Perm α)) (a : α)
    (h : ∀ g ∈ l, g a = a) : (eraseSheetWord l a h).map Perm.ofSubtype = l := by
  unfold eraseSheetWord
  simp only [List.map_map, Function.comp_def, ofSubtype_eraseSheetPerm]
  exact List.attach_map_subtype_val l

theorem ofSubtype_prod_eraseSheetWord (l : List (Perm α)) (a : α)
    (h : ∀ g ∈ l, g a = a) : Perm.ofSubtype (eraseSheetWord l a h).prod = l.prod := by
  rw [map_list_prod, map_ofSubtype_eraseSheetWord]

theorem isSwap_eraseSheetWord [Fintype α] (l : List (Perm α)) (a : α)
    (h : ∀ g ∈ l, g a = a) (hl : ∀ g ∈ l, g.IsSwap) :
    ∀ g ∈ eraseSheetWord l a h, g.IsSwap := by
  intro g hg
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hg
  exact isSwap_eraseSheetPerm u.val a _ (hl u.val u.property)

omit [DecidableEq α] in
theorem isCycleOn_eraseSheetPerm (f : Perm α) (a : α) (ha : f a = a)
    (hf : f.IsCycleOn {x | x ≠ a}) : (eraseSheetPerm f a ha).IsCycleOn univ :=
  hf.subtypePerm

theorem card_erase_sheet [Fintype α] (a : α) :
    Fintype.card {x : α // x ≠ a} + 1 = Fintype.card α := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
  omega

/-- Deleting one sheet from a full cycle leaves a full cycle on the remaining sheets,
including the singleton and empty cases. -/
theorem isCycleOn_delete_sheet [Fintype α] (σ : Perm α) (hσ : σ.IsCycleOn univ) (a : α) :
    (σ * swap a (σ⁻¹ a)).IsCycleOn {x | x ≠ a} := by
  let τ := σ * swap a (σ⁻¹ a)
  have hτa : τ a = a := by simp [τ, Perm.mul_apply]
  have hpres := ne_iff_of_perm_fixed τ a hτa
  have hbij : BijOn τ {x | x ≠ a} {x | x ≠ a} := by
    refine ⟨fun x hx => (hpres x).mpr hx, τ.injective.injOn, ?_⟩
    intro y hy
    refine ⟨τ⁻¹ y, ?_, by simp⟩
    apply (hpres _).mp
    simpa using hy
  obtain hs | hs := ({x : α | x ≠ a} : Set α).subsingleton_or_nontrivial
  · exact ⟨hbij, fun x hx y hy => (hs hx hy).sameCycle τ⟩
  · have huniv : (univ : Set α).Nontrivial := hs.mono (subset_univ _)
    have hcycle : σ.IsCycle := Perm.isCycle_iff_exists_isCycleOn.mpr
      ⟨univ, huniv, hσ, fun _ _ => mem_univ _⟩
    have hσa : σ a ≠ a := hσ.apply_ne huniv (mem_univ a)
    have hnext : σ (σ a) ≠ a := by
      intro h
      have hswap := hcycle.eq_swap_of_apply_apply_eq_self hσa h
      obtain ⟨x, hxa, hxσa⟩ := hs.exists_ne (σ a)
      have hx := hσ.apply_ne huniv (mem_univ x)
      rw [hswap] at hx
      exact hx (swap_apply_of_ne_of_ne hxa hxσa)
    have hτ : τ = swap a (σ a) * σ := by
      change σ * swap a (σ⁻¹ a) = swap a (σ a) * σ
      rw [mul_swap_eq_swap_mul]
      simp [swap_comm]
    have hset : {x | (swap a (σ a) * σ) x ≠ x} = {x : α | x ≠ a} := by
      ext x
      change (swap a (σ a) * σ) x ≠ x ↔ x ≠ a
      rw [← Perm.mem_support, Perm.support_swap_mul_eq σ a hnext,
        Finset.mem_sdiff, Perm.mem_support, Finset.mem_singleton]
      exact and_iff_right (hσ.apply_ne huniv (mem_univ x))
    change τ.IsCycleOn {x | x ≠ a}
    rw [hτ, ← hset]
    exact (hcycle.swap_mul hσa hnext).isCycleOn

end
end GaloisForLFunctions.HTGeometry.HurwitzFactorization

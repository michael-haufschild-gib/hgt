import GaloisForLFunctions.HTGeometry.HurwitzFactorizationMoves
import GaloisForLFunctions.HTGeometry.TranspositionOccurrenceLeaf
import Mathlib.GroupTheory.Perm.Cycle.Basic

open Equiv
namespace GaloisForLFunctions.HTGeometry.HurwitzFactorization

theorem conjugate_by_product_pow {G : Type*} [Group G] (l : List G) (n : ℕ) :
    Related l (l.map (fun a => (l.prod ^ n)⁻¹ * a * l.prod ^ n)) := by
  induction n with
  | zero => simpa using Related.refl l
  | succ n ih =>
      have h := conjugate_by_product (l.map (fun a => (l.prod ^ n)⁻¹ * a * l.prod ^ n))
      rw [ih.prod_eq.symm] at h
      exact ih.trans (by simpa only [List.map_map, Function.comp_def, pow_succ,
        mul_inv_rev, mul_assoc] using h)

variable {α : Type*} [DecidableEq α]

theorem isSwap_conjugate (a b : Perm α) (ha : a.IsSwap) : (b⁻¹ * a * b).IsSwap := by
  obtain ⟨x, y, hxy, rfl⟩ := ha
  refine ⟨b⁻¹ x, b⁻¹ y, (b⁻¹).injective.ne hxy, ?_⟩
  simpa only [inv_inv] using (Equiv.swap_apply_apply b⁻¹ x y).symm

theorem isSwap_conjugate_iff (a b : Perm α) : (b⁻¹ * a * b).IsSwap ↔ a.IsSwap := by
  constructor
  · intro h
    simpa [mul_assoc] using isSwap_conjugate _ b⁻¹ h
  · exact isSwap_conjugate a b

theorem Related.isSwap_iff {l r : List (Perm α)} (h : Related l r) :
    (∀ a ∈ l, a.IsSwap) ↔ ∀ a ∈ r, a.IsSwap :=
  h.forall_iff isSwap_conjugate_iff

theorem occurrences_conjugate (l : List (Perm α)) (g : Perm α) (x : α) :
    occurrences (l.map (fun a => g⁻¹ * a * g)) x = occurrences l (g x) := by
  unfold occurrences
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  have heq : (g⁻¹ * a * g) x = x ↔ a (g x) = g x := by
    constructor
    · intro h
      calc
        a (g x) = g ((g⁻¹ * a * g) x) := (g.apply_symm_apply _).symm
        _ = g x := congrArg g h
    · intro h
      change g.symm (a (g x)) = x
      rw [h]
      exact g.symm_apply_apply x
  change (if (g⁻¹ * a * g) x ≠ x then 1 else 0) = (if a (g x) ≠ g x then 1 else 0)
  simp only [Ne, heq]

theorem forall_fixed_of_occurrences_eq_zero (l : List (Perm α)) (x : α)
    (h : occurrences l x = 0) : ∀ g ∈ l, g x = x := by
  revert h
  induction l with
  | nil => simp
  | cons g l ih =>
      intro h
      rw [occurrences_cons] at h
      have hg : g x = x := by
        by_contra hne
        simp [hne] at h
      have hl : occurrences l x = 0 := by simpa [hg] using h
      exact List.forall_mem_cons.mpr ⟨hg, ih hl⟩

theorem exists_swap_at_moved_point (g : Perm α) (hg : g.IsSwap) (a : α) (ha : g a ≠ a) :
    ∃ b, a ≠ b ∧ g = swap a b := by
  obtain ⟨x, y, hxy, rfl⟩ := hg
  by_cases hax : a = x
  · subst a
    exact ⟨y, hxy, rfl⟩
  · have hay : a = y := by
      by_contra hay
      exact ha (swap_apply_of_ne_of_ne hax hay)
    subst a
    exact ⟨x, hxy.symm, swap_comm x y⟩

/-- A sheet occurring once can be isolated in the final factor by actual adjacent moves. -/
theorem isolate_leaf (l : List (Perm α)) (a : α) (hl : ∀ g ∈ l, g.IsSwap)
    (ha : occurrences l a = 1) :
    ∃ p b, Related l (p ++ [swap a b]) ∧ a ≠ b ∧
      (∀ g ∈ p, g a = a) ∧ (∀ g ∈ p, g.IsSwap) := by
  induction l with
  | nil => simp at ha
  | cons g l ih =>
      have hgSwap : g.IsSwap := hl g (by simp)
      have hlSwap : ∀ t ∈ l, t.IsSwap := fun t ht => hl t (List.mem_cons_of_mem g ht)
      by_cases hg : g a = a
      · have hla : occurrences l a = 1 := by simpa [hg] using ha
        obtain ⟨p, b, hp, hab, hfix, hswap⟩ := ih hlSwap hla
        refine ⟨g :: p, b, ?_, hab, ?_, ?_⟩
        · simpa only [List.singleton_append, List.nil_append, List.cons_append] using hp.prepend [g]
        · exact List.forall_mem_cons.mpr ⟨hg, hfix⟩
        · exact List.forall_mem_cons.mpr ⟨hgSwap, hswap⟩
      · have hla : occurrences l a = 0 := by
          rw [occurrences_cons, if_pos hg] at ha
          omega
        have hfix := forall_fixed_of_occurrences_eq_zero l a hla
        have hprod := prod_fixed_of_occurrences_eq_zero l a hla
        have hmove : (l.prod⁻¹ * g * l.prod) a ≠ a := by
          intro h
          change l.prod.symm (g (l.prod a)) = a at h
          rw [hprod] at h
          have hh := congrArg l.prod h
          rw [l.prod.apply_symm_apply, hprod] at hh
          exact hg hh
        obtain ⟨b, hab, hb⟩ := exists_swap_at_moved_point _
          (isSwap_conjugate g l.prod hgSwap) a hmove
        refine ⟨l, b, ?_, hab, hfix, hlSwap⟩
        exact hb ▸ move_first g l

theorem isolate_leaf_canonical [Fintype α] (l : List (Perm α)) (a : α)
    (hl : ∀ g ∈ l, g.IsSwap) (ha : occurrences l a = 1) :
    ∃ p, Related l (p ++ [swap a (l.prod⁻¹ a)]) ∧
      (∀ g ∈ p, g a = a) ∧ (∀ g ∈ p, g.IsSwap) := by
  obtain ⟨p, b, hp, hab, hfix, hswap⟩ := isolate_leaf l a hl ha
  have hpfix : p.prod a = a := by
    by_contra h
    obtain ⟨g, hgp, hga⟩ := Perm.exists_mem_support_of_mem_support_prod (Perm.mem_support.mpr h)
    exact (Perm.mem_support.mp hga) (hfix g hgp)
  have hb : l.prod b = a := by
    rw [hp.prod_eq, List.prod_append, List.prod_singleton, Perm.mul_apply,
      swap_apply_right, hpfix]
  have hpartner : b = l.prod⁻¹ a := by
    have h := congrArg l.prod.symm hb
    simpa using h
  exact ⟨p, by simpa only [hpartner] using hp, hfix, hswap⟩

/-- Any chosen sheet can be isolated canonically in a minimal transposition factorization
of a full cycle; its partner is forced by the product. -/
theorem isolate_chosen_sheet [Fintype α] [Nontrivial α] (l : List (Perm α))
    (hl : ∀ g ∈ l, g.IsSwap) (hlen : l.length + 1 = Fintype.card α)
    (hcycle : l.prod.IsCycleOn Set.univ) (a : α) :
    ∃ p, Related l (p ++ [swap a (l.prod⁻¹ a)]) ∧
      (∀ g ∈ p, g a = a) ∧ (∀ g ∈ p, g.IsSwap) := by
  have hfree (x : α) : l.prod x ≠ x := hcycle.apply_ne Set.nontrivial_univ (Set.mem_univ x)
  obtain ⟨x, hx⟩ := exists_occurrences_eq_one l hl hlen hfree
  obtain ⟨n, hn⟩ := (hcycle.2 (Set.mem_univ a) (Set.mem_univ x)).exists_nat_pow_eq
  let L := l.map (fun t => (l.prod ^ n)⁻¹ * t * l.prod ^ n)
  have hL : Related l L := conjugate_by_product_pow l n
  have hLa : occurrences L a = 1 := by
    change occurrences (l.map (fun t => (l.prod ^ n)⁻¹ * t * l.prod ^ n)) a = 1
    rw [occurrences_conjugate, hn]
    exact hx
  obtain ⟨p, hp, hfix, hswap⟩ := isolate_leaf_canonical L a (hL.isSwap_iff.mp hl) hLa
  have hprod : L.prod = l.prod := hL.prod_eq.symm
  rw [hprod] at hp
  exact ⟨p, hL.trans hp, hfix, hswap⟩

end GaloisForLFunctions.HTGeometry.HurwitzFactorization

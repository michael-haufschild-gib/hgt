import GaloisForLFunctions.HTGeometry.PauliCommutatorVanishing

/-!
# Edges of an open chain

An edge of the open chain on `m + 1` sites joins two consecutive sites.  Two edges meet exactly
when their indices differ by at most one, so two distinct edges meet in exactly one site precisely
when they are consecutive, and then their sites are three consecutive sites.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {m : ℕ}

/-- The two endpoints of a chain edge. -/
def chainSites (i : Fin m) : Finset (Fin (m + 1)) := {i.castSucc, i.succ}

theorem mem_chainSites {i : Fin m} {s : Fin (m + 1)} :
    s ∈ chainSites i ↔ (s : ℕ) = (i : ℕ) ∨ (s : ℕ) = (i : ℕ) + 1 := by
  rw [chainSites, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ]

theorem card_chainSites (i : Fin m) : (chainSites i).card = 2 := by
  rw [chainSites, Finset.card_insert_of_notMem, Finset.card_singleton]
  rw [Finset.mem_singleton, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  omega

theorem chainSites_inter_self (i : Fin m) : chainSites i ∩ chainSites i = chainSites i :=
  Finset.inter_self _

/-- **Two edges meeting in one site are consecutive.** -/
theorem consecutive_of_card_inter_eq_one {p q : Fin m}
    (h : (chainSites p ∩ chainSites q).card = 1) :
    (q : ℕ) = (p : ℕ) + 1 ∨ (p : ℕ) = (q : ℕ) + 1 := by
  classical
  have hne : p ≠ q := by
    intro hc
    subst hc
    rw [chainSites_inter_self, card_chainSites] at h
    exact absurd h (by norm_num)
  obtain ⟨s, hs⟩ : (chainSites p ∩ chainSites q).Nonempty :=
    Finset.card_pos.mp (by omega)
  rw [Finset.mem_inter, mem_chainSites, mem_chainSites] at hs
  have hpq : (p : ℕ) ≠ (q : ℕ) := fun hc => hne (Fin.ext hc)
  omega

/-- The sites of two consecutive edges are three consecutive sites. -/
theorem chainSites_union_consecutive {p q : Fin m} (hq : (q : ℕ) = (p : ℕ) + 1)
    {s : Fin (m + 1)} :
    s ∈ chainSites p ∪ chainSites q ↔
      (s : ℕ) = (p : ℕ) ∨ (s : ℕ) = (p : ℕ) + 1 ∨ (s : ℕ) = (p : ℕ) + 2 := by
  rw [Finset.mem_union, mem_chainSites, mem_chainSites, hq]
  omega

/-- **Consecutive edges are determined by the three sites they cover.** -/
theorem eq_of_chainSites_union {p q p' q' : Fin m}
    (hq : (q : ℕ) = (p : ℕ) + 1) (hq' : (q' : ℕ) = (p' : ℕ) + 1)
    (h : chainSites p ∪ chainSites q = chainSites p' ∪ chainSites q') :
    p = p' := by
  classical
  have hp : (p.castSucc : Fin (m + 1)) ∈ chainSites p ∪ chainSites q :=
    Finset.mem_union_left _ (Finset.mem_insert_self _ _)
  have hp' : (p'.castSucc : Fin (m + 1)) ∈ chainSites p' ∪ chainSites q' :=
    Finset.mem_union_left _ (Finset.mem_insert_self _ _)
  rw [h] at hp
  rw [← h] at hp'
  rw [chainSites_union_consecutive hq'] at hp
  rw [chainSites_union_consecutive hq] at hp'
  rw [Fin.val_castSucc] at hp hp'
  refine Fin.ext ?_
  omega

end GaloisForLFunctions.HTGeometry

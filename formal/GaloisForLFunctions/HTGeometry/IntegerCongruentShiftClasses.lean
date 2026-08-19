import Mathlib

/-!
# Integer congruence classes of a finite family of shifts

The boundary datum of a jet polynomial needs its shifts to be pairwise incongruent modulo the
integers.  An arbitrary finite family is brought into that form by choosing, in each congruence
class, the member of least index.  This file is the pure combinatorics of that choice: the selector
is idempotent, its value is congruent to the original shift, and distinct selected values are
incongruent.
-/

namespace GaloisForLFunctions.HTGeometry

open Classical

/-- Two complex numbers differing by an integer. -/
def IntCongruent (a b : ℂ) : Prop := ∃ n : ℤ, a - b = (n : ℂ)

theorem IntCongruent.refl (a : ℂ) : IntCongruent a a := ⟨0, by simp⟩

theorem IntCongruent.symm {a b : ℂ} (h : IntCongruent a b) : IntCongruent b a := by
  obtain ⟨n, hn⟩ := h
  exact ⟨-n, by push_cast; linear_combination -hn⟩

theorem IntCongruent.trans {a b c : ℂ} (h : IntCongruent a b) (h' : IntCongruent b c) :
    IntCongruent a c := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, hm⟩ := h'
  exact ⟨n + m, by push_cast; linear_combination hn + hm⟩

variable {r : ℕ}

/-- The minimum of a finset only depends on the finset. -/
theorem min'_congr {s t : Finset (Fin r)} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by
  subst h
  rfl

/-- The congruence class of a shift, as a finset of indices. -/
noncomputable def congClass (lam : Fin r → ℂ) (i : Fin r) : Finset (Fin r) :=
  Finset.univ.filter fun i' => IntCongruent (lam i') (lam i)

theorem mem_congClass_iff {lam : Fin r → ℂ} {i k : Fin r} :
    k ∈ congClass lam i ↔ IntCongruent (lam k) (lam i) := by
  simp [congClass]

theorem mem_congClass_self (lam : Fin r → ℂ) (i : Fin r) : i ∈ congClass lam i :=
  mem_congClass_iff.mpr (IntCongruent.refl _)

theorem congClass_nonempty (lam : Fin r → ℂ) (i : Fin r) : (congClass lam i).Nonempty :=
  ⟨i, mem_congClass_self lam i⟩

theorem congClass_eq_of_congruent {lam : Fin r → ℂ} {i i' : Fin r}
    (h : IntCongruent (lam i) (lam i')) : congClass lam i = congClass lam i' := by
  ext k
  rw [mem_congClass_iff, mem_congClass_iff]
  exact ⟨fun hk => hk.trans h, fun hk => hk.trans h.symm⟩

/-- The least index congruent to a given one. -/
noncomputable def congRep (lam : Fin r → ℂ) (i : Fin r) : Fin r :=
  (congClass lam i).min' (congClass_nonempty lam i)

theorem congRep_congruent (lam : Fin r → ℂ) (i : Fin r) :
    IntCongruent (lam (congRep lam i)) (lam i) :=
  mem_congClass_iff.mp ((congClass lam i).min'_mem (congClass_nonempty lam i))

theorem congRep_eq_of_congruent {lam : Fin r → ℂ} {i i' : Fin r}
    (h : IntCongruent (lam i) (lam i')) : congRep lam i = congRep lam i' :=
  min'_congr (congClass_eq_of_congruent h) _ _

theorem congRep_idem (lam : Fin r → ℂ) (i : Fin r) :
    congRep lam (congRep lam i) = congRep lam i :=
  congRep_eq_of_congruent (congRep_congruent lam i)

/-- The index type of the selected representatives. -/
abbrev CongReps (lam : Fin r → ℂ) : Type := {i : Fin r // congRep lam i = i}

/-- Every index selects a representative. -/
noncomputable def toCongRep (lam : Fin r → ℂ) (i : Fin r) : CongReps lam :=
  ⟨congRep lam i, congRep_idem lam i⟩

theorem lam_toCongRep_congruent (lam : Fin r → ℂ) (i : Fin r) :
    IntCongruent (lam (toCongRep lam i : Fin r)) (lam i) := congRep_congruent lam i

/-- **The selected shifts are pairwise incongruent.** -/
theorem not_intCongruent_of_ne (lam : Fin r → ℂ) {a b : CongReps lam} (hab : a ≠ b) :
    ¬ IntCongruent (lam (a : Fin r)) (lam (b : Fin r)) := by
  intro hcon
  refine hab (Subtype.ext ?_)
  have ha : congRep lam (a : Fin r) = (a : Fin r) := a.2
  have hb : congRep lam (b : Fin r) = (b : Fin r) := b.2
  rw [← ha, ← hb]
  exact congRep_eq_of_congruent hcon

/-- Each shift is its representative plus an integer. -/
theorem exists_int_eq_lam_toCongRep (lam : Fin r → ℂ) (i : Fin r) :
    ∃ m : ℤ, lam i = lam (toCongRep lam i : Fin r) + (m : ℂ) := by
  obtain ⟨n, hn⟩ := lam_toCongRep_congruent lam i
  exact ⟨-n, by push_cast; linear_combination -hn⟩

end GaloisForLFunctions.HTGeometry

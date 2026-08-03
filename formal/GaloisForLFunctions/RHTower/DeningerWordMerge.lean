import GaloisForLFunctions.RHTower.DeningerTransversalForm

/-!
# Merging letters at the ends of a word

Multiplying a word by a letter of the factor its last letter lies in merges the two: the word keeps
the same letters except for the last, which is multiplied.  If the merged letter falls into the base
group the word shortens instead.  These are the atomic steps of cyclic reduction at the level of
words.

* `deningerLetterProd_snoc` : the product of a word with a last letter appended.
* `deningerMerge_last` : merging on the right.
* `deningerMerge_first` : merging on the left.
* `deningerCycStep` : one step of cyclic reduction at the level of words.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

theorem deningerLetterProd_snoc (M : List (Σ i, G i)) (p : Σ i, G i) :
    deningerLetterProd (φ := φ) (M ++ [p]) =
      deningerLetterProd (φ := φ) M * PushoutI.of p.1 p.2 := by
  rw [deningerLetterProd_append, deningerLetterProd_cons, deningerLetterProd_nil, mul_one]

/-- **Merging on the right.**  Multiplying by a letter of the factor of the last letter multiplies
that letter. -/
theorem deningerMerge_last (M : List (Σ i, G i)) (i : ι) (y x : G i) :
    deningerLetterProd (φ := φ) (M ++ [⟨i, y⟩]) * PushoutI.of i x =
      deningerLetterProd (φ := φ) (M ++ [⟨i, y * x⟩]) := by
  rw [deningerLetterProd_snoc, deningerLetterProd_snoc, mul_assoc, ← map_mul]

/-- If the merged letter falls into the base group, the word shortens. -/
theorem deningerMerge_last_mem (M : List (Σ i, G i)) (i : ι) (y x : G i)
    (h : y * x ∈ (φ i).range) :
    ∃ k : H, deningerLetterProd (φ := φ) (M ++ [⟨i, y⟩]) * PushoutI.of i x =
      deningerLetterProd (φ := φ) M * PushoutI.base φ k := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  rw [deningerMerge_last, deningerLetterProd_snoc, ← hk,
    PushoutI.of_apply_eq_base φ i k]

/-- **Merging on the left.**  Multiplying by a letter of the factor of the first letter multiplies
that letter. -/
theorem deningerMerge_first (M : List (Σ i, G i)) (i : ι) (y x : G i) :
    PushoutI.of i y * deningerLetterProd (φ := φ) (⟨i, x⟩ :: M) =
      deningerLetterProd (φ := φ) (⟨i, y * x⟩ :: M) := by
  rw [deningerLetterProd_cons, deningerLetterProd_cons, ← mul_assoc, ← map_mul]

/-- If the merged letter falls into the base group, the word shortens. -/
theorem deningerMerge_first_mem (M : List (Σ i, G i)) (i : ι) (y x : G i)
    (h : y * x ∈ (φ i).range) :
    ∃ k : H, PushoutI.of i y * deningerLetterProd (φ := φ) (⟨i, x⟩ :: M) =
      PushoutI.base φ k * deningerLetterProd (φ := φ) M := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  rw [deningerMerge_first, deningerLetterProd_cons, ← hk,
    PushoutI.of_apply_eq_base φ i k]

/-- **One step of cyclic reduction at the level of words.**  If the first and last letters lie in
the same factor, conjugating by the first letter removes it and multiplies it into the last. -/
theorem deningerCycStep (q : Σ i, G i) (M : List (Σ i, G i)) (y : G q.1) :
    (PushoutI.of q.1 q.2)⁻¹ * deningerLetterProd (φ := φ) (q :: (M ++ [⟨q.1, y⟩])) *
        PushoutI.of q.1 q.2 =
      deningerLetterProd (φ := φ) (M ++ [⟨q.1, y * q.2⟩]) := by
  rw [deningerLetterProd_cons, ← mul_assoc, inv_mul_cancel, one_mul, deningerMerge_last]

theorem deningerCycStep_length (q : Σ i, G i) (M : List (Σ i, G i)) (y : G q.1) :
    (M ++ [(⟨q.1, y * q.2⟩ : Σ i, G i)]).length + 1 =
      (q :: (M ++ [(⟨q.1, y⟩ : Σ i, G i)])).length := by
  simp

end RHTower

import GaloisForLFunctions.RHTower.Deninger.DeningerBaseLength

/-!
# Splitting a conjugated power

For an amalgam the two ends of a cyclically reduced conjugate are not inverse to one another, so a
power `(c v c⁻¹)ᵏ` is best written as `c · v^{k-1} · (v c⁻¹)`: the left conjugator survives intact,
the middle is a power of the cyclically reduced part, and all the cancellation is confined to the
last factor.

* `deningerConj_pow_split` : the splitting.
* `deningerNormalWord_append` : the normal word of a product of two transversal words.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
/-- **Splitting a conjugated power.**  The cancellation is confined to the last factor. -/
theorem deningerConj_pow_split (c v : PushoutI φ) (k : ℕ) :
    (c * v * c⁻¹) ^ (k + 1) = c * v ^ k * (v * c⁻¹) := by
  have hmap := map_pow (MulAut.conj c) v (k + 1)
  simp only [MulAut.conj_apply] at hmap
  rw [← hmap, pow_succ]
  group

/-- The normal word of a product of two transversal words meeting without cancellation. -/
theorem deningerNormalWord_append (C D : List (Σ i, G i))
    (hCset : ∀ p ∈ C, p.2 ∈ d.set p.1) (hCred : ∀ p ∈ C, p.2 ∉ (φ p.1).range)
    (hCalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) C)
    (hDset : ∀ p ∈ D, p.2 ∈ d.set p.1) (hDred : ∀ p ∈ D, p.2 ∉ (φ p.1).range)
    (hDalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) D)
    (hCD : ∀ p ∈ C.getLast?, ∀ q ∈ D.head?, p.1 ≠ q.1) :
    ((deningerLetterProd (φ := φ) C * deningerLetterProd (φ := φ) D) •
        (NormalWord.empty : NormalWord d)).toList = C ++ D := by
  have hprod : deningerLetterProd (φ := φ) C * deningerLetterProd (φ := φ) D =
      deningerLetterProd (φ := φ) (C ++ D) := (deningerLetterProd_append C D).symm
  rw [hprod]
  refine (deningerNormalWord_letterProd _ ?_ ?_ ?_).1
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hCset p hp
    · exact hDset p hp
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hCred p hp
    · exact hDred p hp
  · exact List.isChain_append.2 ⟨hCalt, hDalt, hCD⟩

end RHTower

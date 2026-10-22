import GaloisForLFunctions.RHTower.Deninger.DeningerAbsorbRight

/-!
# The two cases of a cyclic reduction step

Conjugating by the first letter deletes it and multiplies it into the last letter.  If the merged
letter is a genuine letter the word shortens by one; if it falls into the base group the word
shortens by two, the base group element being absorbed into the new last letter.

* `deningerCycStep_notMem` : the merged letter survives.
* `deningerCycStep_mem` : the merged letter falls into the base group.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **The merged letter survives.** -/
theorem deningerCycStep_notMem (q : Σ i, G i) (M : List (Σ i, G i)) (y : G q.1) :
    (PushoutI.of q.1 q.2)⁻¹ *
        deningerLetterProd (φ := φ) (q :: (M ++ [(⟨q.1, y⟩ : Σ i, G i)])) * PushoutI.of q.1 q.2 =
      deningerLetterProd (φ := φ) (M ++ [(⟨q.1, y * q.2⟩ : Σ i, G i)]) :=
  deningerCycStep q M y

/-- **The merged letter falls into the base group.**  The word shortens by two and the base group
element is absorbed into the new last letter. -/
theorem deningerCycStep_mem (q : Σ i, G i) (M' : List (Σ i, G i)) (p : Σ i, G i) (y : G q.1)
    (k : H) (hk : φ q.1 k = y * q.2) :
    (PushoutI.of q.1 q.2)⁻¹ *
        deningerLetterProd (φ := φ)
          (q :: (M' ++ [p] ++ [(⟨q.1, y⟩ : Σ i, G i)])) * PushoutI.of q.1 q.2 =
      deningerLetterProd (φ := φ) (M' ++ [(⟨p.1, p.2 * φ p.1 k⟩ : Σ i, G i)]) := by
  rw [deningerCycStep q (M' ++ [p]) y,
    deningerLetterProd_snoc (M' ++ [p]) (⟨q.1, y * q.2⟩ : Σ i, G i)]
  show deningerLetterProd (φ := φ) (M' ++ [p]) * PushoutI.of q.1 (y * q.2) = _
  rw [← hk, PushoutI.of_apply_eq_base φ q.1 k, deningerLetterProd_mul_base_snoc]

end RHTower

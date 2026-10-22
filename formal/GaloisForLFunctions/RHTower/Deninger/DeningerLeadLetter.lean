import GaloisForLFunctions.RHTower.Deninger.DeningerRotateCompare

/-!
# The leading letter survives when nothing cancels

If a reduced alternating word is multiplied on the right by an element and the word length is the
sum of the two lengths, then no cancellation has taken place and the normal form of the product
begins in the factor of the first letter.

* `deningerFstIdx_mul_of_len` : the leading letter of an uncancelled product.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- **The leading letter of an uncancelled product.** -/
theorem deningerFstIdx_mul_of_len (L : List (Σ i, G i)) (b : PushoutI φ)
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hlen : deningerLen d (deningerLetterProd (φ := φ) L * b) = L.length + deningerLen d b)
    (p : Σ i, G i) (hp : p ∈ L.head?) :
    (((deningerLetterProd (φ := φ) L * b) • (NormalWord.empty : NormalWord d)) :
      NormalWord d).fstIdx = some p.1 := by
  induction L generalizing p with
  | nil => simp at hp
  | cons r L' ih =>
    rw [List.head?_cons, Option.mem_def] at hp
    obtain rfl : p = r := (Option.some.inj hp).symm
    have hrred : p.2 ∉ (φ p.1).range := hred p List.mem_cons_self
    have hsplit : deningerLetterProd (φ := φ) (p :: L') * b =
        PushoutI.of p.1 p.2 * (deningerLetterProd (φ := φ) L' * b) := by
      rw [deningerLetterProd_cons, mul_assoc]
    have hle := deningerLen_letterProd_mul_le (d := d) L' b
    have hstep := deningerLen_of_mul_le (d := d) p.1 p.2 (deningerLetterProd (φ := φ) L' * b)
    rw [← hsplit] at hstep
    have hlen' : deningerLen d (deningerLetterProd (φ := φ) L' * b) = L'.length +
        deningerLen d b := by
      have hcons : (p :: L').length = L'.length + 1 := by simp
      omega
    cases hL' : L' with
    | nil =>
      subst hL'
      have hsplit' : deningerLetterProd (φ := φ) [p] * b = PushoutI.of p.1 p.2 * b := by
        rw [deningerLetterProd_cons, deningerLetterProd_nil, mul_one]
      have hb : ((b • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx ≠ some p.1 := by
        intro hc
        have hcon := deningerLen_of_mul_le_of_fstIdx (d := d) p.1 p.2 b hc
        rw [← hsplit'] at hcon
        have hcons : ([p] : List (Σ i, G i)).length = 1 := by simp
        omega
      rw [hsplit']
      exact deningerFstIdx_of_mul p.1 p.2 b hrred hb
    | cons s L'' =>
      subst hL'
      have hne : p.1 ≠ s.1 := (List.isChain_cons.1 halt).1 s (by simp)
      have hihd := ih (fun q hq => hred q (List.mem_cons_of_mem _ hq)) halt.tail hlen' s (by simp)
      have hb : (((deningerLetterProd (φ := φ) (s :: L'') * b) •
          (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx ≠ some p.1 := by
        rw [hihd]
        intro hc
        exact hne (Option.some.inj hc).symm
      rw [hsplit]
      exact deningerFstIdx_of_mul p.1 p.2 _ hrred hb

end RHTower

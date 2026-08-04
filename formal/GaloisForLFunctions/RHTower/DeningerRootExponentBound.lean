import GaloisForLFunctions.RHTower.DeningerCycRedWordOfPow

/-!
# The exponent of a root of a cyclically reduced element is bounded

A root of a cyclically reduced word is again a cyclically reduced word, of length the length of the
original divided by the exponent, so the exponent cannot exceed that length.  In particular an
element with a nonempty cyclically reduced normal word has only finitely many exponents available,
which is what makes a maximal root exist.

* `deningerRootExponent_le` : the bound.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **The exponent of a root of a cyclically reduced element is at most its length.** -/
theorem deningerRootExponent_le (V₀ : List (Σ i, G i)) (hV₀ne : V₀ ≠ [])
    (hV₀red : ∀ p ∈ V₀, p.2 ∉ (φ p.1).range)
    (hV₀alt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V₀)
    (hV₀cyc : ∀ p ∈ V₀.getLast?, ∀ q ∈ V₀.head?, p.1 ≠ q.1)
    (y : PushoutI φ) (n : ℕ) (h : y ^ (n + 1) = deningerLetterProd (φ := φ) V₀) :
    n + 1 ≤ V₀.length := by
  obtain ⟨U, hUne, -, -, -, hlen, -⟩ :=
    deningerCycRedWord_of_pow (d := d) y V₀ n hV₀ne hV₀red hV₀alt hV₀cyc h
  have hU : 1 ≤ U.length := List.length_pos_iff.2 hUne
  calc n + 1 = (n + 1) * 1 := by ring
    _ ≤ (n + 1) * U.length := Nat.mul_le_mul_left _ hU
    _ = V₀.length := hlen

end RHTower

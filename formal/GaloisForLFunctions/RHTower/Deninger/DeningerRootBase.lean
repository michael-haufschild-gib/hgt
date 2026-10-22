import GaloisForLFunctions.RHTower.Deninger.DeningerConjugator

/-!
# Roots in the base group

Two elements of an amalgam which lie in the base group and have the same power are equal, provided
the base group has unique roots.  This is the case of the uniqueness of roots in which no word
combinatorics occurs.

* `deningerPow_eq_of_len_zero` : uniqueness of roots for elements of the base group.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **Uniqueness of roots for elements of the base group.** -/
theorem deningerPow_eq_of_len_zero (hφ : ∀ i, Function.Injective (φ i))
    (hH : ∀ (a b : H) (n : ℕ), 0 < n → a ^ n = b ^ n → a = b)
    (x y : PushoutI φ) (hx : deningerLen d x = 0) (hy : deningerLen d y = 0)
    (n : ℕ) (hn : 0 < n) (h : x ^ n = y ^ n) : x = y := by
  obtain ⟨a, ha⟩ := (deningerLen_eq_zero_iff (d := d) x).1 hx
  obtain ⟨b, hb⟩ := (deningerLen_eq_zero_iff (d := d) y).1 hy
  have hab : a ^ n = b ^ n := by
    refine PushoutI.base_injective hφ ?_
    rw [map_pow, map_pow, ha, hb]
    exact h
  rw [← ha, ← hb, hH a b n hn hab]

end RHTower

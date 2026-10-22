import GaloisForLFunctions.RHTower.Deninger.DeningerShortConjCases

/-!
# The centralizer of a factor element

An element commuting with an element of a factor conjugates it to itself, which has length at most
one, so the conjugacy criterion for short elements applies: either the commuting element lies in
that factor, or the element it centralizes conjugates into the base group inside the factor.  Roots
of a factor element therefore lie in the factor, and uniqueness of roots there settles them.

* `deningerCentralizer_factor` : the centralizer criterion.
* `deningerPow_eq_of_factorPow` : uniqueness of roots of a factor element.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **The centralizer criterion.**  An element commuting with an element of a factor lies in that
factor, unless the latter conjugates into the base group inside it. -/
theorem deningerCentralizer_factor (i : ι) (v : G i) (hv : v ∉ (φ i).range) (w : PushoutI φ)
    (hcomm : w * PushoutI.of (φ := φ) i v = PushoutI.of (φ := φ) i v * w) :
    (∃ x : G i, w = PushoutI.of (φ := φ) i x) ∨
      ∃ (x : G i) (k : H), x⁻¹ * v * x = φ i k := by
  refine deningerShortConj_cases (d := d) i v hv w ?_
  have hfix : w⁻¹ * PushoutI.of (φ := φ) i v * w = PushoutI.of (φ := φ) i v := by
    calc w⁻¹ * PushoutI.of (φ := φ) i v * w
        = w⁻¹ * (PushoutI.of (φ := φ) i v * w) := by group
      _ = w⁻¹ * (w * PushoutI.of (φ := φ) i v) := by rw [← hcomm]
      _ = PushoutI.of (φ := φ) i v := by group
  rw [hfix]
  exact deningerLen_of_le_one (d := d) i v

include d in
/-- **Uniqueness of roots of a factor element.**  Two roots of an element of a factor which does not
conjugate into the base group inside it lie in that factor, hence agree. -/
theorem deningerPow_eq_of_factorPow (hφ : ∀ i, Function.Injective (φ i))
    (hG : ∀ (i : ι) (a b : G i) (n : ℕ), 0 < n → a ^ n = b ^ n → a = b)
    (i : ι) (ζ : G i) (hζ : ζ ∉ (φ i).range)
    (hnoesc : ¬ ∃ (x : G i) (k : H), x⁻¹ * ζ * x = φ i k)
    (x y : PushoutI φ) (n : ℕ)
    (hx : x ^ (n + 1) = PushoutI.of (φ := φ) i ζ)
    (hy : y ^ (n + 1) = PushoutI.of (φ := φ) i ζ) : x = y := by
  have hxc : x * PushoutI.of (φ := φ) i ζ = PushoutI.of (φ := φ) i ζ * x := by
    rw [← hx]
    exact ((Commute.refl x).pow_right (n + 1))
  have hyc : y * PushoutI.of (φ := φ) i ζ = PushoutI.of (φ := φ) i ζ * y := by
    rw [← hy]
    exact ((Commute.refl y).pow_right (n + 1))
  obtain ⟨α, hα⟩ | hesc := deningerCentralizer_factor (d := d) i ζ hζ x hxc
  · obtain ⟨β, hβ⟩ | hesc := deningerCentralizer_factor (d := d) i ζ hζ y hyc
    · have hαζ : α ^ (n + 1) = ζ := by
        refine PushoutI.of_injective hφ i ?_
        rw [map_pow, ← hα, hx]
      have hβζ : β ^ (n + 1) = ζ := by
        refine PushoutI.of_injective hφ i ?_
        rw [map_pow, ← hβ, hy]
      rw [hα, hβ, hG i α β (n + 1) (by omega) (by rw [hαζ, hβζ])]
    · exact absurd hesc hnoesc
  · exact absurd hesc hnoesc

end RHTower

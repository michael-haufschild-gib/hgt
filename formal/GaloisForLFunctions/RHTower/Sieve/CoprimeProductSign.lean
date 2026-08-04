import GaloisForLFunctions.RHTower.Sieve.SecondMomentExplicit

/-!
# The products of coprime pairs carry the product sign

For coprime `a, b` the Möbius function is multiplicative, so a family of coprime pairs whose factor
signs multiply to `ε` produces products all of which satisfy `μ(m) = ε`.  Combined with the
distinct-product bound this counts *integers of a prescribed Möbius sign*, not representations:

`#{m ∈ [1,X] : μ(m) = ε} ≥ (#S)² / (X · balancedMomentConst y)`.

This is the form the card's consequence `(4)` asserts.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **The product of a coprime pair carries the product sign.** -/
theorem moebius_image_sign {S : Finset (ℕ × ℕ)} {ε : ℤ}
    (hcop : ∀ p ∈ S, Nat.Coprime p.1 p.2)
    (hsign : ∀ p ∈ S, moebius p.1 * moebius p.2 = ε) :
    ∀ m ∈ S.image (fun p => p.1 * p.2), moebius m = ε := by
  classical
  intro m hm
  rw [Finset.mem_image] at hm
  obtain ⟨p, hp, rfl⟩ := hm
  rw [isMultiplicative_moebius.map_mul_of_coprime (hcop p hp)]
  exact hsign p hp

/-- **A lower bound for the count of integers with a prescribed Möbius sign.** -/
theorem card_moebius_eq_ge {y X : ℕ} (hy : 1 ≤ y) (S : Finset (ℕ × ℕ)) {ε : ℤ}
    (hV : 0 < (X : ℝ) * balancedMomentConst y)
    (hd : ∀ p ∈ S, p.1 ∈ Finset.Icc y (2 * y))
    (himg : ∀ p ∈ S, p.1 * p.2 ∈ Finset.Icc 1 X)
    (hcop : ∀ p ∈ S, Nat.Coprime p.1 p.2)
    (hsign : ∀ p ∈ S, moebius p.1 * moebius p.2 = ε) :
    ((S.card : ℕ) : ℝ) ^ 2 / ((X : ℝ) * balancedMomentConst y)
      ≤ ((((Finset.Icc 1 X).filter (fun m => moebius m = ε)).card : ℕ) : ℝ) := by
  classical
  refine le_trans (card_image_mul_ge_explicit hy S hV hd himg) ?_
  have hsub : S.image (fun p => p.1 * p.2)
      ⊆ (Finset.Icc 1 X).filter (fun m => moebius m = ε) := by
    intro m hm
    rw [Finset.mem_filter]
    refine ⟨?_, moebius_image_sign hcop hsign m hm⟩
    rw [Finset.mem_image] at hm
    obtain ⟨p, hp, rfl⟩ := hm
    exact himg p hp
  exact_mod_cast Finset.card_le_card hsub

end RHTower.Sieve

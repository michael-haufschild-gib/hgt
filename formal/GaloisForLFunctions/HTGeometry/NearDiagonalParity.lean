import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
# The parity condition of the near-diagonal substitution

The substitution `2n = m + r` used to reindex a near-diagonal double sum is *not* a bijection onto
all `r`: for a fixed `m` its range is exactly the parity class of `m`,

```
{r : 2n = m + r for some n} = {r : Even (r + m)}.
```

Replacing a sum over `n` by an unrestricted sum over `r` therefore silently doubles the index set.

The von Mangoldt weight makes the correction explicit: an even integer carrying nonzero von Mangoldt
weight is a power of two, so after weighting, the parity restriction only bites through the powers
of two, and for odd `m` it forces `r` odd.
-/

open ArithmeticFunction
open scoped ArithmeticFunction

namespace GaloisForLFunctions.HTGeometry

/-! ## The lost lattice condition -/

/-- The near-diagonal substitution `n ↦ r` determined by `2n = m + r`. -/
def nearDiagonalSubst (m n : ℤ) : ℤ := 2 * n - m

theorem nearDiagonalSubst_injective (m : ℤ) : Function.Injective (nearDiagonalSubst m) := by
  intro a b hab
  have : 2 * a = 2 * b := by
    simpa [nearDiagonalSubst, sub_left_inj] using hab
  omega

theorem two_mul_eq_add_nearDiagonalSubst (m n : ℤ) : 2 * n = m + nearDiagonalSubst m n := by
  simp [nearDiagonalSubst]

/-- **The lost lattice condition.**  The substitution reaches exactly the parity class of `m`. -/
theorem range_nearDiagonalSubst (m : ℤ) :
    Set.range (nearDiagonalSubst m) = {r : ℤ | Even (r + m)} := by
  ext r
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, by simp only [nearDiagonalSubst]; ring⟩
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    simp only [nearDiagonalSubst]
    omega

/-- Unrestricted summation over `r` is not the substituted sum: some `r` are missed. -/
theorem not_surjective_nearDiagonalSubst (m : ℤ) :
    ¬ Function.Surjective (nearDiagonalSubst m) := by
  intro hsurj
  obtain ⟨n, hn⟩ := hsurj (m + 1)
  simp only [nearDiagonalSubst] at hn
  omega

/-! ## The even von Mangoldt support -/

/-- **An even integer with nonzero von Mangoldt weight is a power of two.** -/
theorem exists_pow_two_of_even_of_vonMangoldt_ne_zero {m : ℕ} (heven : Even m)
    (hm : Λ m ≠ 0) : ∃ k : ℕ, 0 < k ∧ m = 2 ^ k := by
  obtain ⟨p, k, hp, hk, hpk⟩ := vonMangoldt_ne_zero_iff.mp hm
  have hpnat : Nat.Prime p := Nat.prime_iff.mpr hp
  have hdvd : 2 ∣ p ^ k := by
    rw [hpk]
    exact heven.two_dvd
  have hp2 : (2 : ℕ) ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
  have hpeq : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpnat).mp hp2).symm
  exact ⟨k, hk, by rw [← hpk, hpeq]⟩

/-- Contrapositive form: away from the powers of two, the even von Mangoldt weight vanishes. -/
theorem vonMangoldt_eq_zero_of_even_of_not_pow_two {m : ℕ} (heven : Even m)
    (hnot : ∀ k : ℕ, 0 < k → m ≠ 2 ^ k) : Λ m = 0 := by
  by_contra hm
  obtain ⟨k, hk, hkm⟩ := exists_pow_two_of_even_of_vonMangoldt_ne_zero heven hm
  exact hnot k hk hkm

/-- **The parity restriction for odd `m`.**  If `m` is odd, the substitution reaches exactly the
odd `r`, which is the restriction the unrestricted sawtooth sum drops. -/
theorem range_nearDiagonalSubst_of_odd {m : ℤ} (hm : Odd m) :
    Set.range (nearDiagonalSubst m) = {r : ℤ | Odd r} := by
  rw [range_nearDiagonalSubst]
  ext r
  simp only [Set.mem_setOf_eq]
  obtain ⟨t, ht⟩ := hm
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j - t - 1, by omega⟩
  · rintro ⟨j, hj⟩
    exact ⟨j + t + 1, by omega⟩

end GaloisForLFunctions.HTGeometry

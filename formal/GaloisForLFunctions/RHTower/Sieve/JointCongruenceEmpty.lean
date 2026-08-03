import GaloisForLFunctions.RHTower.Sieve.TruncatedPairSwap

/-!
# Most non-coprime pairs contribute nothing

If `d² ∣ n` and `e² ∣ n + h` then, writing `g = gcd(d,e)`, both `g² ∣ n` and `g² ∣ n + h`, so

`g² ∣ h`.

Hence for every pair with `gcd(d,e)² ∤ h` the joint count is **zero**, and the double sum of the
truncated pair identity is supported on the pairs that are coprime — handled by
`abs_card_joint_sub_lt` — together with those whose squared gcd divides the shift.

The shift `h` therefore controls which non-coprime pairs can occur at all: for `h` squarefree, only
`g = 1` survives and the pair sum is entirely coprime.
-/

namespace RHTower.Sieve

open Finset

/-- A common solution forces the squared gcd to divide the shift. -/
theorem gcd_sq_dvd_of_joint {d e h n : ℕ} (hd : d ^ 2 ∣ n) (he : e ^ 2 ∣ (n + h)) :
    (Nat.gcd d e) ^ 2 ∣ h := by
  have hgd : (Nat.gcd d e) ^ 2 ∣ d ^ 2 := pow_dvd_pow_of_dvd (Nat.gcd_dvd_left d e) 2
  have hge : (Nat.gcd d e) ^ 2 ∣ e ^ 2 := pow_dvd_pow_of_dvd (Nat.gcd_dvd_right d e) 2
  have h1 : (Nat.gcd d e) ^ 2 ∣ n := hgd.trans hd
  have h2 : (Nat.gcd d e) ^ 2 ∣ (n + h) := hge.trans he
  have h1' : (((Nat.gcd d e) ^ 2 : ℕ) : ℤ) ∣ (n : ℤ) := by exact_mod_cast h1
  have h2' : (((Nat.gcd d e) ^ 2 : ℕ) : ℤ) ∣ ((n : ℤ) + (h : ℤ)) := by exact_mod_cast h2
  have hz : (((Nat.gcd d e) ^ 2 : ℕ) : ℤ) ∣ (h : ℤ) := by
    simpa using dvd_sub h2' h1'
  exact_mod_cast hz

/-- **Pairs whose squared gcd misses the shift contribute nothing.** -/
theorem card_joint_eq_zero {d e h : ℕ} (hg : ¬ ((Nat.gcd d e) ^ 2 ∣ h)) (t L : ℕ) :
    #{n ∈ Finset.Ioc t (t + L) | d ^ 2 ∣ n ∧ e ^ 2 ∣ (n + h)} = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n _
  rintro ⟨hd, he⟩
  exact hg (gcd_sq_dvd_of_joint hd he)

/-- **For a squarefree shift only coprime pairs survive.** -/
theorem coprime_of_joint_of_squarefree {d e h n : ℕ} (hh : Squarefree h)
    (hd : d ^ 2 ∣ n) (he : e ^ 2 ∣ (n + h)) : Nat.Coprime d e := by
  have hdvd := gcd_sq_dvd_of_joint hd he
  have := hh (Nat.gcd d e) (by simpa [pow_two] using hdvd)
  exact Nat.isUnit_iff.mp this

end RHTower.Sieve

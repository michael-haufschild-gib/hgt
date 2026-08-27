import GaloisForLFunctions.RHTower.Sieve.HeathBrownDyadicCoefficientBound

/-!
# Submultiplicativity of the divisor count

The elementary inequality `d(ab) ≤ d(a)d(b)` is used repeatedly in the source.  We prove it by
injecting a divisor `d ∣ ab` into `(gcd(d,a), d/gcd(d,a))`; coprimality after removing the gcd
forces the second coordinate to divide `b`.
-/

namespace RHTower.Sieve

open Finset

/-- The divisor-counting function is submultiplicative. -/
theorem card_divisors_mul_le {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  classical
  let f : ℕ → ℕ × ℕ := fun d => (Nat.gcd d a, d / Nat.gcd d a)
  have hmaps : Set.MapsTo f ((a * b).divisors : Set ℕ)
      ((a.divisors.product b.divisors : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro d hd
    have hdvd : d ∣ a * b := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hgpos : 0 < Nat.gcd d a := Nat.gcd_pos_of_pos_left a hdpos
    have hga : Nat.gcd d a ∣ a := Nat.gcd_dvd_right d a
    have hgd : Nat.gcd d a ∣ d := Nat.gcd_dvd_left d a
    have hcancel : d / Nat.gcd d a ∣ (a / Nat.gcd d a) * b := by
      rw [← Nat.mul_dvd_mul_iff_left hgpos]
      convert hdvd using 1
      · exact Nat.mul_div_cancel' hgd
      · rw [← mul_assoc, Nat.mul_div_cancel' hga]
    have hcop : (d / Nat.gcd d a).Coprime (a / Nat.gcd d a) :=
      Nat.coprime_div_gcd_div_gcd hgpos
    have hdb : d / Nat.gcd d a ∣ b := hcop.dvd_of_dvd_mul_left hcancel
    simp [f, Nat.mem_divisors, hga, hdb, ha.ne', hb.ne']
  have hinj : Set.InjOn f ((a * b).divisors : Set ℕ) := by
    intro d hd e he hde
    have hgd : Nat.gcd d a ∣ d := Nat.gcd_dvd_left d a
    have hge : Nat.gcd e a ∣ e := Nat.gcd_dvd_left e a
    have hmulD : Nat.gcd d a * (d / Nat.gcd d a) = d := Nat.mul_div_cancel' hgd
    have hmulE : Nat.gcd e a * (e / Nat.gcd e a) = e := Nat.mul_div_cancel' hge
    exact hmulD ▸ hmulE ▸ congrArg (fun x : ℕ × ℕ => x.1 * x.2) hde
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  simpa using hcard

/-- Real-power form used after reindexing a divisor-weighted sum over multiples. -/
theorem card_divisors_mul_pow_le
    (K : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (((a * b).divisors.card : ℝ) ^ K) ≤
      ((a.divisors.card : ℝ) ^ K) * ((b.divisors.card : ℝ) ^ K) := by
  have hcard : (((a * b).divisors.card : ℕ) : ℝ) ≤
      (a.divisors.card : ℝ) * (b.divisors.card : ℝ) := by
    exact_mod_cast card_divisors_mul_le ha hb
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard K
  simpa [mul_pow] using hpow

end RHTower.Sieve

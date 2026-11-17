import GaloisForLFunctions.RHTower.LogVonMangoldtGaussianSums

/-!
# Coincident products of ordinary prime weights

For two finite cofactors dividing the same product, divide the product by
their least common multiple. The remaining variable occurs as the common
factor in two von Mangoldt weights. Beyond its first term their correlation
is supported on powers of a single prime and can be summed exactly.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- On the positive integers greater than one, simultaneous nonzero
dilates of the von Mangoldt weight force both dilations and their argument
to be powers of the least prime divisor of the first dilation. -/
theorem prime_powers_of_dilated_mangoldt_product {a b n : ℕ} (ha : 2 ≤ a) (hn : 2 ≤ n)
    (h : vonMangoldt (a*n) * vonMangoldt (b*n) ≠ 0) :
    (∃ i : ℕ, a = a.minFac ^ i) ∧ (∃ j : ℕ, b = a.minFac ^ j) ∧
      ∃ k : ℕ, 0 < k ∧ n = a.minFac ^ k := by
  let p := a.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hL := vonMangoldt_ne_zero_iff.mp (left_ne_zero_of_mul h)
  have hR := vonMangoldt_ne_zero_iff.mp (right_ne_zero_of_mul h)
  obtain ⟨e, _, he⟩ := RHTower.GaussZeroSum.eq_minFac_pow_of_dvd ha (dvd_mul_right a n) hL
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp
    (show a ∣ p ^ e by rw [← he]; exact dvd_mul_right a n)
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp
    (show n ∣ p ^ e by rw [← he]; exact dvd_mul_left n a)
  have hkpos : 0 < k := by
    by_contra! hk0
    simp [Nat.eq_zero_of_le_zero hk0] at hk
    omega
  have hpn : p ∣ n := hk ▸ dvd_pow_self _ hkpos.ne'
  obtain ⟨f, _, hf⟩ := RHTower.GaussZeroSum.eq_minFac_pow_of_dvd hp.two_le
    (dvd_mul_of_dvd_right hpn b) hR
  rw [hp.minFac_eq] at hf
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp
    (show b ∣ p ^ f by rw [← hf]; exact dvd_mul_right b n)
  exact ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hkpos, hk⟩⟩

private theorem mangoldt_weights_on_prime_powers {p a b n : ℕ} (hp : p.Prime)
    (ha : ∃ i : ℕ, a = p ^ i) (hb : ∃ j : ℕ, b = p ^ j)
    (hn : ∃ k : ℕ, 0 < k ∧ n = p ^ k) :
    vonMangoldt (a*n) * vonMangoldt (b*n) = Real.log p * vonMangoldt n := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨k, hk, rfl⟩ := hn
  rw [← pow_add, ← pow_add, vonMangoldt_apply_pow (by omega : i+k ≠ 0),
    vonMangoldt_apply_pow (by omega : j+k ≠ 0), vonMangoldt_apply_pow hk.ne',
    vonMangoldt_apply_prime hp]

/-- Closed form for the off-diagonal prime-weight correlation with a common
integer factor. The term at one is excluded and equals `Λ(a)Λ(b)` separately. -/
open Classical in
theorem sum_dilated_mangoldt_product {a : ℕ} (ha : 2 ≤ a) (b : ℕ) {X : ℕ} (hX : 1 ≤ X) :
    ∑ n ∈ Icc 2 X, vonMangoldt (a*n) * vonMangoldt (b*n) =
      if (∃ i : ℕ, a = a.minFac ^ i) ∧ (∃ j : ℕ, b = a.minFac ^ j) then
        Real.log a.minFac * Real.log ((a.minFac ^ Nat.log a.minFac X : ℕ) : ℝ)
      else 0 := by
  classical
  let p := a.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  let Q := p ^ Nat.log p X
  have hQ : Q ≤ X := Nat.pow_log_le_self _ (by omega)
  have hQpos : 0 < Q := pow_pos hp.pos _
  by_cases hd : (∃ i : ℕ, a = p ^ i) ∧ (∃ j : ℕ, b = p ^ j)
  · rw [if_pos hd]
    have hterm (n : ℕ) (hn : n ∈ Icc 2 X) :
        vonMangoldt (a*n) * vonMangoldt (b*n) = if n ∣ Q then Real.log p * vonMangoldt n else 0 := by
      obtain ⟨hn2, hnX⟩ := mem_Icc.mp hn
      split_ifs with hdiv
      · obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hdiv
        have hkpos : 0 < k := by
          by_contra! h
          simp [Nat.eq_zero_of_le_zero h] at hk
          omega
        exact mangoldt_weights_on_prime_powers hp hd.1 hd.2 ⟨k, hkpos, hk⟩
      · by_contra h
        obtain ⟨k, _, hk⟩ := (prime_powers_of_dilated_mangoldt_product ha hn2 h).2.2
        have hkle := (Nat.le_log_iff_pow_le hp.one_lt (by omega : X ≠ 0)).mpr
          (show p ^ k ≤ X by rw [← hk]; exact hnX)
        exact hdiv (hk ▸ pow_dvd_pow p hkle)
    have hsupport : (Icc 2 X).filter (· ∣ Q) = Q.divisors.erase 1 := by
      ext n
      simp only [mem_filter, mem_Icc, mem_erase, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hn, _⟩, hdvd⟩
        exact ⟨by omega, hdvd, hQpos.ne'⟩
      · rintro ⟨hne, hdvd, _⟩
        have hn0 := Nat.pos_of_dvd_of_pos hdvd hQpos
        exact ⟨⟨by omega, (Nat.le_of_dvd hQpos hdvd).trans hQ⟩, hdvd⟩
    rw [sum_congr rfl hterm, ← sum_filter, hsupport, ← mul_sum]
    have hhead : (∑ n ∈ Q.divisors.erase 1, vonMangoldt n) = ∑ n ∈ Q.divisors, vonMangoldt n := by
      apply sum_subset (erase_subset _ _)
      intro n hn hnot
      by_cases h : n = 1
      · simpa only [h] using vonMangoldt_apply_one
      · exact False.elim (hnot (mem_erase.mpr ⟨h, hn⟩))
    rw [hhead, vonMangoldt_sum]
  · rw [if_neg hd]
    apply sum_eq_zero
    intro n hn
    by_contra h
    obtain ⟨h₁, h₂, _⟩ := prime_powers_of_dilated_mangoldt_product ha (mem_Icc.mp hn).1 h
    exact hd ⟨h₁, h₂⟩

/-- Uniform logarithmic upper bound for the common-factor tail,
independent of the second dilation. -/
theorem sum_dilated_mangoldt_product_le {a : ℕ} (ha : 2 ≤ a) (b : ℕ) {X : ℕ} (hX : 1 ≤ X) :
    ∑ n ∈ Icc 2 X, vonMangoldt (a*n) * vonMangoldt (b*n) ≤ Real.log a * Real.log X := by
  classical
  rw [sum_dilated_mangoldt_product ha b hX]
  split_ifs
  · have hp : a.minFac.Prime := Nat.minFac_prime (by omega)
    apply mul_le_mul
    · exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast Nat.minFac_le (by omega : 0 < a))
    · exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.pow_log_le_self a.minFac (by omega : X ≠ 0))
    · exact Real.log_natCast_nonneg _
    · exact Real.log_natCast_nonneg _
  · exact mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

#print axioms sum_dilated_mangoldt_product
#print axioms sum_dilated_mangoldt_product_le

end GaloisForLFunctions.ExceptionalLayerTheory

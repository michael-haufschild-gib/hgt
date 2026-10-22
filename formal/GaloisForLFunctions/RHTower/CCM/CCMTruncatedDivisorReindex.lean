import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# A prime-shift cutoff truncates the divisor weight, not the radial index

Cutting the prime shifts at `q ≤ X` and reindexing `k = q * n` turns a double sum over visible prime
powers and radial multipliers into a single sum over **all** radial indices carrying the truncated
divisor weight

```text
a_X k = ∑_{q ∣ k, 2 ≤ q ≤ X} Λ q.
```

* `truncatedDivisorWeight_eq_filter_le` — the lower restriction `2 ≤ q` is vacuous, because
  `Λ 1 = 0`.
* `sum_shift_eq_sum_truncatedDivisorWeight` — the exact reindexing, by the bijection
  `(q, n) ↦ (q * n, q)` between visible shift/multiplier pairs and index/divisor pairs.
* `truncatedDivisorWeight_nonneg`, `truncatedDivisorWeight_le_log`,
  `truncatedDivisorWeight_eq_log_of_le`, `truncatedDivisorWeight_mono` — the divisor identity
  `∑_{q ∣ k} Λ q = log k` bounds the weight, the bound is attained as soon as `k ≤ X`, and the weight
  is monotone in the cutoff.  In particular the weight does **not** vanish for `k > X`: every
  multiple of a visible prime power keeps its contribution, which is why a prime-shift cutoff is not
  a radial-index cutoff.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Finset ArithmeticFunction

/-- The truncated divisor weight: the von Mangoldt mass of the divisors of `k` visible below the
prime-shift cutoff `X`. -/
def truncatedDivisorWeight (X k : ℕ) : ℝ :=
  ∑ q ∈ k.divisors.filter (fun q => 2 ≤ q ∧ q ≤ X), Λ q

/-- The lower restriction is vacuous: the only divisor below `2` is `1`, and `Λ 1 = 0`. -/
theorem truncatedDivisorWeight_eq_filter_le (X k : ℕ) :
    truncatedDivisorWeight X k = ∑ q ∈ k.divisors.filter (fun q => q ≤ X), Λ q := by
  classical
  rw [truncatedDivisorWeight]
  refine Finset.sum_subset ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, hq.2.2⟩
  · intro q hq hnot
    simp only [Finset.mem_filter] at hq
    have hpos : 0 < q := Nat.pos_of_mem_divisors hq.1
    have hq1 : q = 1 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hq.1, by omega, hq.2⟩)
    rw [hq1, vonMangoldt_apply_one]

theorem truncatedDivisorWeight_nonneg (X k : ℕ) : 0 ≤ truncatedDivisorWeight X k := by
  refine Finset.sum_nonneg fun q _ => vonMangoldt_nonneg

/-- **Equation (7).**  The truncated weight never exceeds the full divisor weight `log k`. -/
theorem truncatedDivisorWeight_le_log (X k : ℕ) : truncatedDivisorWeight X k ≤ Real.log k := by
  classical
  rw [truncatedDivisorWeight, ← vonMangoldt_sum (n := k)]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  exact fun q _ _ => vonMangoldt_nonneg

/-- The weight is monotone in the cutoff. -/
theorem truncatedDivisorWeight_mono {X Y : ℕ} (hXY : X ≤ Y) (k : ℕ) :
    truncatedDivisorWeight X k ≤ truncatedDivisorWeight Y k := by
  classical
  rw [truncatedDivisorWeight, truncatedDivisorWeight]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, hq.2.1, le_trans hq.2.2 hXY⟩
  · exact fun q _ _ => vonMangoldt_nonneg

/-- **Equation (8).**  Below the cutoff the weight is the full divisor weight. -/
theorem truncatedDivisorWeight_eq_log_of_le {X k : ℕ} (hk : k ≤ X) :
    truncatedDivisorWeight X k = Real.log k := by
  classical
  rw [truncatedDivisorWeight, ← vonMangoldt_sum (n := k)]
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro q hq hnot
  have hmem := Nat.mem_divisors.mp hq
  have hkpos : 0 < k := Nat.pos_of_ne_zero hmem.2
  have hle : q ≤ k := Nat.le_of_dvd hkpos hmem.1
  have hqX : q ≤ X := le_trans hle hk
  have hqpos : 0 < q := Nat.pos_of_mem_divisors hq
  have hq1 : q = 1 := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hq, by omega, hqX⟩)
  rw [hq1, vonMangoldt_apply_one]

/-- **Equation (9).**  For each fixed radial index the weight is eventually the full divisor
weight. -/
theorem truncatedDivisorWeight_eventually_eq_log (k : ℕ) :
    ∀ X, k ≤ X → truncatedDivisorWeight X k = Real.log k :=
  fun _ hX => truncatedDivisorWeight_eq_log_of_le hX

/-! ## The exact reindexing -/

/-- **Equations (4)–(6).**  Reindexing `k = q * n` turns the visible prime-shift double sum into a
single sum over every radial index, weighted by the truncated divisor weight.  The bijection is
`(q, n) ↦ (q * n, q)`. -/
theorem sum_shift_eq_sum_truncatedDivisorWeight (X K : ℕ) (G : ℕ → ℝ) :
    (∑ q ∈ Finset.Icc 2 X, Λ q * ∑ n ∈ Finset.Icc 1 (K / q), G (q * n))
      = ∑ k ∈ Finset.Icc 2 K, truncatedDivisorWeight X k * G k := by
  classical
  have hLsig := Finset.sum_sigma' (Finset.Icc 2 X) (fun q => Finset.Icc 1 (K / q))
    (fun q n => Λ q * G (q * n))
  have hRsig := Finset.sum_sigma' (Finset.Icc 2 K)
    (fun k => k.divisors.filter fun q => 2 ≤ q ∧ q ≤ X) (fun k q => Λ q * G k)
  have hL : (∑ q ∈ Finset.Icc 2 X, Λ q * ∑ n ∈ Finset.Icc 1 (K / q), G (q * n))
      = ∑ q ∈ Finset.Icc 2 X, ∑ n ∈ Finset.Icc 1 (K / q), Λ q * G (q * n) :=
    Finset.sum_congr rfl fun q _ => by rw [Finset.mul_sum]
  have hR : (∑ k ∈ Finset.Icc 2 K, truncatedDivisorWeight X k * G k)
      = ∑ k ∈ Finset.Icc 2 K, ∑ q ∈ k.divisors.filter (fun q => 2 ≤ q ∧ q ≤ X), Λ q * G k :=
    Finset.sum_congr rfl fun k _ => by rw [truncatedDivisorWeight, Finset.sum_mul]
  rw [hL, hR, hLsig, hRsig]
  refine Finset.sum_nbij' (fun x => ⟨x.1 * x.2, x.1⟩) (fun x => ⟨x.2, x.1 / x.2⟩) ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    rintro ⟨q, n⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hq2, hqX⟩, hn1, hnK⟩ := hx
    have hqpos : 0 < q := by omega
    have hmulK : q * n ≤ K := by
      rw [Nat.le_div_iff_mul_le hqpos] at hnK
      linarith [hnK]
    refine ⟨⟨by nlinarith, hmulK⟩, ⟨⟨Dvd.intro n rfl, by positivity⟩, hq2, hqX⟩⟩
  · -- backward membership
    rintro ⟨k, q⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hk2, hkK⟩, ⟨hdvd, hkne⟩, hq2, hqX⟩ := hx
    have hqpos : 0 < q := by omega
    have hqk : q ≤ k := Nat.le_of_dvd (by omega) hdvd
    refine ⟨⟨hq2, hqX⟩, ?_, ?_⟩
    · exact Nat.one_le_div_iff hqpos |>.mpr hqk
    · exact Nat.div_le_div_right hkK
  · -- left inverse
    rintro ⟨q, n⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx
    have hqpos : 0 < q := by omega
    simp [Nat.mul_div_cancel_left _ hqpos]
  · -- right inverse
    rintro ⟨k, q⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hx
    obtain ⟨_, ⟨hdvd, _⟩, _⟩ := hx
    simp [Nat.mul_div_cancel' hdvd]
  · -- the summands agree
    rintro ⟨q, n⟩ _
    rfl

end GaloisForLFunctions.RHTower

end

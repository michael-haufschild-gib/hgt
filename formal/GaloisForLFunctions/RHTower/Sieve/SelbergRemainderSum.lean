import GaloisForLFunctions.RHTower.Sieve.RoughPairRemainderSum

/-!
# The Selberg remainder sum of the pair sieve

Every divisor of the sieve's modulus below the level has at most `log z / log P₁` prime factors, and
there are at most `z` such divisors, so the whole remainder sum is at most `2 z · 6^{log z/log P₁}`.

Since the sifting primes are large this exponent is `o(1)` and the remainder is `z^{1+o(1)}` — the
classical divisor-moment estimate is not needed.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The Selberg remainder sum of the pair sieve.** -/
theorem sum_selbergRemainder_le {P₁ hN : ℕ} (hP₁ : 2 ≤ P₁) {z : ℝ} (hz : 1 ≤ z) :
    (∑ e ∈ (rangePrimorial P₁ hN).divisors,
        (if ((e : ℕ) : ℝ) ≤ z then 2 * (6 : ℝ) ^ e.primeFactors.card else 0))
      ≤ 2 * z * (6 : ℝ) ^ (Real.log z / Real.log P₁) := by
  classical
  have hz0 : (0 : ℝ) < z := by linarith
  have hP₁R : (2 : ℝ) ≤ (P₁ : ℝ) := by exact_mod_cast hP₁
  have hlogP : 0 < Real.log (P₁ : ℝ) := Real.log_pos (by linarith)
  set F : Finset ℕ := (rangePrimorial P₁ hN).divisors.filter (fun e => ((e : ℕ) : ℝ) ≤ z) with hF
  rw [← Finset.sum_filter]
  have hterm : ∀ e ∈ F, 2 * (6 : ℝ) ^ e.primeFactors.card
      ≤ 2 * (6 : ℝ) ^ (Real.log z / Real.log P₁) := by
    intro e he
    rw [hF, Finset.mem_filter, Nat.mem_divisors] at he
    obtain ⟨⟨hdvd, hP0⟩, hle⟩ := he
    have hcard : ((e.primeFactors.card : ℕ) : ℝ) ≤ Real.log ⌊z⌋₊ / Real.log P₁ :=
      card_primeFactors_le_log hP₁ hdvd (Nat.le_floor hle)
    have hfl : ((⌊z⌋₊ : ℕ) : ℝ) ≤ z := Nat.floor_le hz0.le
    have hlogfl : Real.log ⌊z⌋₊ ≤ Real.log z := by
      rcases Nat.eq_zero_or_pos ⌊z⌋₊ with h0 | hpos
      · rw [h0]
        simp only [Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg hz
      · exact Real.log_le_log (by exact_mod_cast hpos) hfl
    have hexp : ((e.primeFactors.card : ℕ) : ℝ) ≤ Real.log z / Real.log P₁ := by
      refine hcard.trans ?_
      exact (div_le_div_iff_of_pos_right hlogP).mpr hlogfl
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [← Real.rpow_natCast (6 : ℝ) e.primeFactors.card]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcardF : ((F.card : ℕ) : ℝ) ≤ z := by
    have hsub : F ⊆ Finset.Icc 1 ⌊z⌋₊ := by
      intro e he
      rw [hF, Finset.mem_filter, Nat.mem_divisors] at he
      obtain ⟨⟨hdvd, hP0⟩, hle⟩ := he
      have he1 : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with rfl | hpos
        · exact absurd (zero_dvd_iff.1 hdvd) hP0
        · exact hpos
      exact Finset.mem_Icc.2 ⟨he1, Nat.le_floor hle⟩
    have hc : F.card ≤ (Finset.Icc 1 ⌊z⌋₊).card := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    have hcR : ((F.card : ℕ) : ℝ) ≤ ((⌊z⌋₊ : ℕ) : ℝ) := by
      have : F.card ≤ ⌊z⌋₊ := by omega
      exact_mod_cast this
    exact hcR.trans (Nat.floor_le hz0.le)
  have hpow0 : (0 : ℝ) < (6 : ℝ) ^ (Real.log z / Real.log P₁) :=
    Real.rpow_pos_of_pos (by norm_num) _
  nlinarith [hcardF, hpow0]

end

end RHTower.Sieve

import GaloisForLFunctions.RHTower.Sieve.RoughSetShiftBound

/-!
# Summing the shifted counts of the discarded set

The fibre second moment needs the shifted counts summed over `1 ≤ d ≤ H`.  The sieve bounds each of
them, and its shift correction is uniform: every sifting prime exceeds `P₁`, so the correction is at
least `1 − log H/(log P₁ · P₁)` for every shift below `H`.

The shift `d = 0` is excluded here: at `d = 0` every prime divides the shift, the sieve degenerates
to the one-dimensional one, and the corresponding term is handled separately with the (weaker but
sufficient) one-dimensional bound.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The shifted counts of the discarded set, summed over the nonzero shifts.** -/
theorem sum_shift_roughSet_le (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ} (k H : ℕ) {z : ℝ}
    (hz : 1 ≤ z) (hY : 0 ≤ Y) (hh1 : 1 ≤ h) (hP₁h : P₁ ≤ h) (hlev : ((h : ℝ)) ^ (2 * k) ≤ z)
    (hk : ∀ d : ℕ, Real.exp 1
        * (∑ p ∈ rangePrimes P₁ h, pairClassCount d p / ((p : ℝ) - pairClassCount d p))
        + Real.log 2 ≤ (k : ℝ))
    (hcorr : 0 < 1 - Real.log H / (Real.log P₁ * (P₁ : ℝ)))
    (D : Finset ℕ) :
    (∑ d ∈ Finset.Ico 1 (H + 1),
      ((((roughSet P₁ h ⌊Y⌋₊ ∩ D).filter
        (fun m => m + d ∈ roughSet P₁ h ⌊Y⌋₊ ∩ D)).card : ℕ) : ℝ))
      ≤ (H : ℝ) * (Y / ((1 / 2) * (Real.exp (mertensS h - mertensS P₁) ^ 2
            * (1 - Real.log H / (Real.log P₁ * (P₁ : ℝ)))))
          + ∑ e ∈ (rangePrimorial P₁ h).divisors,
              (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0)) := by
  classical
  set R : ℝ := ∑ e ∈ (rangePrimorial P₁ h).divisors,
      (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) with hR
  set E : ℝ := Real.exp (mertensS h - mertensS P₁) ^ 2 with hE
  have hE0 : (0 : ℝ) < E := by
    rw [hE]
    positivity
  set c : ℝ := 1 - Real.log H / (Real.log P₁ * (P₁ : ℝ)) with hc
  have hterm : ∀ d ∈ Finset.Ico 1 (H + 1),
      ((((roughSet P₁ h ⌊Y⌋₊ ∩ D).filter
        (fun m => m + d ∈ roughSet P₁ h ⌊Y⌋₊ ∩ D)).card : ℕ) : ℝ)
        ≤ Y / ((1 / 2) * (E * c)) + R := by
    intro d hd
    rw [Finset.mem_Ico] at hd
    refine (card_shift_roughSet_le Y hP₁ d k hz hY hh1 hP₁h hlev (hk d) D).trans ?_
    refine add_le_add ?_ le_rfl
    set C : ℝ := ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ))
      with hC
    have hCge : c ≤ C := by
      rw [hc, hC]
      exact prod_shiftCorrection_ge P₁ h d hP₁ hd.1 (by omega : d ≤ H)
    have hden0 : (0 : ℝ) < (1 / 2) * (E * c) := by
      have : (0 : ℝ) < E * c := mul_pos hE0 hcorr
      linarith
    have hmono : (1 / 2) * (E * c) ≤ (1 / 2) * (E * C) := by
      have : E * c ≤ E * C := mul_le_mul_of_nonneg_left hCge hE0.le
      linarith
    rw [div_le_div_iff₀ (by linarith : (0:ℝ) < (1/2) * (E * C)) hden0]
    nlinarith [hY, hmono, hden0]
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  congr 1

end

end RHTower.Sieve

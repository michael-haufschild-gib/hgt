import GaloisForLFunctions.RHTower.Sieve.FibreRoughExplicit
import GaloisForLFunctions.RHTower.Sieve.MertensDiffExp

/-!
# The discarded part, in logarithms

Replacing the Mertens difference by the ratio of logarithms turns the closed form of the discarded
part into an expression in `log P₁ / log hN` alone, up to the two explicit Mertens errors.  This is
the form in which the parameters are chosen.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The discarded part of the fibre mean square, in logarithms.** -/
theorem sum_sq_card_fibre_roughSet_log {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h)
    (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {hN : ℕ} (k : ℕ) {z : ℝ}
    (hz : 1 ≤ z) (hY : 0 ≤ Y) (hh2 : 2 ≤ hN) (hP₁h : P₁ ≤ hN)
    (hlev : ((hN : ℝ)) ^ (2 * k) ≤ z)
    (hk : ∀ d : ℕ, Real.exp 1
        * (∑ p ∈ rangePrimes P₁ hN, pairClassCount d p / ((p : ℝ) - pairClassCount d p))
        + Real.log 2 ≤ (k : ℝ))
    (hcorr : 0 < 1 - Real.log ⌊h⌋₊ / (Real.log P₁ * (P₁ : ℝ))) :
    ∑ a ∈ outerBlock x h,
        ((((innerFibre x h a ∩ roughSet P₁ hN ⌊Y⌋₊).card : ℕ)) : ℝ) ^ 2
      ≤ (2 * h + 1) * (2 * ((2 * Y * (Real.log P₁ / Real.log hN)
              * Real.exp (mertensErr P₁ + mertensErr hN)
            + ∑ e ∈ (rangePrimorial P₁ hN).divisors,
                (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0))
          + ((⌊h⌋₊ : ℕ) : ℝ)
              * (2 * Y * (Real.log P₁ / Real.log hN) ^ 2
                    * Real.exp (mertensErr P₁ + mertensErr hN) ^ 2
                    / (1 - Real.log ⌊h⌋₊ / (Real.log P₁ * (P₁ : ℝ)))
                + ∑ e ∈ (rangePrimorial P₁ hN).divisors,
                    (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0)))) := by
  classical
  have hh1 : 1 ≤ hN := by omega
  have hlP : 0 < Real.log (P₁ : ℝ) := log_pos_of_two_le hP₁
  have hlh : 0 < Real.log (hN : ℝ) := log_pos_of_two_le hh2
  set E : ℝ := Real.exp (mertensErr P₁ + mertensErr hN) with hEdef
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  set A : ℝ := (Real.log (hN : ℝ) / Real.log (P₁ : ℝ)) * Real.exp (-(mertensErr P₁ + mertensErr hN))
    with hA
  have hA0 : (0 : ℝ) < A := by
    rw [hA]
    have : (0 : ℝ) < Real.log (hN : ℝ) / Real.log (P₁ : ℝ) := div_pos hlh hlP
    positivity
  have hAle : A ≤ Real.exp (mertensS hN - mertensS P₁) := exp_mertens_diff_ge hP₁ hh2
  have hAinv : (1 : ℝ) / A = (Real.log (P₁ : ℝ) / Real.log (hN : ℝ)) * E := by
    rw [hA, hEdef, Real.exp_neg]
    field_simp
  set Δ : ℝ := Real.exp (mertensS hN - mertensS P₁) with hΔ
  have hΔ0 : (0 : ℝ) < Δ := Real.exp_pos _
  refine (sum_sq_card_fibre_roughSet_explicit hx hh0 Y hP₁ k hz hY hh1 hP₁h hlev hk hcorr).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  refine mul_le_mul_of_nonneg_left (add_le_add (add_le_add ?_ le_rfl)
    (mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) (Nat.cast_nonneg _))) (by norm_num)
  · -- the diagonal term
    have hrw : 2 * Y * (Real.log (P₁ : ℝ) / Real.log (hN : ℝ)) * E * ((1 / 2) * Δ)
        = Y * Δ / A := by
      have h1 : (Real.log (P₁ : ℝ) / Real.log (hN : ℝ)) * E = 1 / A := hAinv.symm
      calc 2 * Y * (Real.log (P₁ : ℝ) / Real.log (hN : ℝ)) * E * ((1 / 2) * Δ)
          = 2 * Y * ((Real.log (P₁ : ℝ) / Real.log (hN : ℝ)) * E) * ((1 / 2) * Δ) := by ring
        _ = 2 * Y * (1 / A) * ((1 / 2) * Δ) := by rw [h1]
        _ = Y * Δ / A := by field_simp
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 / 2) * Δ)]
    have hgoal : Y ≤ 2 * Y * (Real.log (P₁ : ℝ) / Real.log (hN : ℝ)) * E * ((1 / 2) * Δ) := by
      rw [hrw, le_div_iff₀ hA0]
      nlinarith [hAle, hY, hA0]
    linarith [hgoal]
  · -- the off-diagonal term
    set c : ℝ := 1 - Real.log ⌊h⌋₊ / (Real.log P₁ * (P₁ : ℝ)) with hc
    have hAsq : ((Real.log (P₁ : ℝ) / Real.log (hN : ℝ)) * E) ^ 2 = 1 / A ^ 2 := by
      rw [← hAinv, div_pow, one_pow]
    have hsq : A ^ 2 ≤ Δ ^ 2 := by nlinarith [hAle, hA0, hΔ0]
    have hrwR : 2 * Y * (Real.log (P₁ : ℝ) / Real.log (hN : ℝ)) ^ 2 * E ^ 2 / c
        = Y / ((1 / 2) * (A ^ 2 * c)) := by
      have h2 : (Real.log (P₁ : ℝ) / Real.log (hN : ℝ)) ^ 2 * E ^ 2 = 1 / A ^ 2 := by
        rw [← mul_pow]
        exact hAsq
      calc 2 * Y * (Real.log (P₁ : ℝ) / Real.log (hN : ℝ)) ^ 2 * E ^ 2 / c
          = 2 * Y * ((Real.log (P₁ : ℝ) / Real.log (hN : ℝ)) ^ 2 * E ^ 2) / c := by ring
        _ = 2 * Y * (1 / A ^ 2) / c := by rw [h2]
        _ = Y / ((1 / 2) * (A ^ 2 * c)) := by
              have hA2 : A ^ 2 ≠ 0 := by positivity
              have hcne : c ≠ 0 := ne_of_gt hcorr
              field_simp
    rw [hrwR]
    refine div_le_div_of_nonneg_left hY (by positivity) ?_
    nlinarith [hsq, hcorr]

end

end RHTower.Sieve

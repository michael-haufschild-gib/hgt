import GaloisForLFunctions.RHTower.Sieve.FibreRoughTotal
import GaloisForLFunctions.RHTower.Sieve.RoughShiftSum
import GaloisForLFunctions.RHTower.Sieve.RoughSetCount

/-!
# The discarded part of the fibre mean square, explicitly

Composing the diagonal/off-diagonal split with the two sieve bounds gives a single explicit
inequality for the contribution of the discarded integers to the fibre mean square.  Every constant
is named; nothing is asymptotic.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The discarded part of the fibre mean square, in closed form.** -/
theorem sum_sq_card_fibre_roughSet_explicit {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h)
    (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {hN : ℕ} (k : ℕ) {z : ℝ}
    (hz : 1 ≤ z) (hY : 0 ≤ Y) (hh1 : 1 ≤ hN) (hP₁h : P₁ ≤ hN)
    (hlev : ((hN : ℝ)) ^ (2 * k) ≤ z)
    (hk : ∀ d : ℕ, Real.exp 1
        * (∑ p ∈ rangePrimes P₁ hN, pairClassCount d p / ((p : ℝ) - pairClassCount d p))
        + Real.log 2 ≤ (k : ℝ))
    (hcorr : 0 < 1 - Real.log ⌊h⌋₊ / (Real.log P₁ * (P₁ : ℝ))) :
    ∑ a ∈ outerBlock x h,
        ((((innerFibre x h a ∩ roughSet P₁ hN ⌊Y⌋₊).card : ℕ)) : ℝ) ^ 2
      ≤ (2 * h + 1) * (2 * ((Y / ((1 / 2) * Real.exp (mertensS hN - mertensS P₁))
            + ∑ e ∈ (rangePrimorial P₁ hN).divisors,
                (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0))
          + ((⌊h⌋₊ : ℕ) : ℝ)
              * (Y / ((1 / 2) * (Real.exp (mertensS hN - mertensS P₁) ^ 2
                    * (1 - Real.log ⌊h⌋₊ / (Real.log P₁ * (P₁ : ℝ)))))
                + ∑ e ∈ (rangePrimorial P₁ hN).divisors,
                    (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0)))) := by
  classical
  refine sum_sq_card_fibre_roughSet_le hx hh0 (roughSet P₁ hN ⌊Y⌋₊) ?_ ?_
  · refine le_trans ?_ (roughSetCountCard_roughSet_le Y hP₁ k hz hY hh1 hP₁h hlev (hk 0))
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  · exact sum_shift_roughSet_le Y hP₁ k ⌊h⌋₊ hz hY hh1 hP₁h hlev hk hcorr
      (fibreDyadicIndex x h)

end

end RHTower.Sieve

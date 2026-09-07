import GaloisForLFunctions.RHTower.MontgomeryPrimeAmpMoments
import GaloisForLFunctions.RHTower.MontgomeryPairFormTruncation
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Assembly bounds for the pair-correlation mean square

The zero side of Montgomery's lemma is `Σ_ρ 2x^ρ/((ρ−a_t)(ρ−b_t)) = primeSide + E`, with
`‖Σ_ρ …‖² = 4x ‖S(x,t)‖²`.  This module records the elementary inequalities used to compare
`∫_0^T ‖S‖²` with the prime-side mean square:

* `‖P + E‖² ≤ (1+δ)‖P‖² + (1+1/δ)‖E‖²` and `‖P‖² − (1+1/δ)‖E‖² ≤ (1+δ)‖P+E‖²`, integrated;
* `∫_0^T ‖E‖² ≤ 96 x² + 3 T (C + log(T+4))²/x + 1536/x⁴`.
-/

open MeasureTheory Filter Topology Set

namespace RHTower

/-! ## The `δ`-inequalities -/

theorem normSq_add_le_delta (a b : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ‖a + b‖ ^ 2 ≤ (1 + δ) * ‖a‖ ^ 2 + (1 + 1 / δ) * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hsq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hamgm : 2 * ‖a‖ * ‖b‖ ≤ δ * ‖a‖ ^ 2 + ‖b‖ ^ 2 / δ := by
    rw [← sub_nonneg]
    have : δ * ‖a‖ ^ 2 + ‖b‖ ^ 2 / δ - 2 * ‖a‖ * ‖b‖ = (δ * ‖a‖ - ‖b‖) ^ 2 / δ := by
      field_simp; ring
    rw [this]; positivity
  have : (1 + 1 / δ) * ‖b‖ ^ 2 = ‖b‖ ^ 2 + ‖b‖ ^ 2 / δ := by ring
  nlinarith

theorem normSq_add_ge_delta (a b : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ‖a‖ ^ 2 - (1 + 1 / δ) * ‖b‖ ^ 2 ≤ (1 + δ) * ‖a + b‖ ^ 2 := by
  have h : ‖a‖ ≤ ‖a + b‖ + ‖b‖ := by
    have := norm_add_le (a + b) (-b); simpa using this
  have hab := norm_nonneg (a + b)
  have hb := norm_nonneg b
  have hsq : ‖a‖ ^ 2 ≤ (‖a + b‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hamgm : 2 * ‖a + b‖ * ‖b‖ ≤ δ * ‖a + b‖ ^ 2 + ‖b‖ ^ 2 / δ := by
    rw [← sub_nonneg]
    have : δ * ‖a + b‖ ^ 2 + ‖b‖ ^ 2 / δ - 2 * ‖a + b‖ * ‖b‖ = (δ * ‖a + b‖ - ‖b‖) ^ 2 / δ := by
      field_simp; ring
    rw [this]; positivity
  have : (1 + 1 / δ) * ‖b‖ ^ 2 = ‖b‖ ^ 2 + ‖b‖ ^ 2 / δ := by ring
  nlinarith

/-! ## Continuity of the pieces -/

theorem continuousOn_montgomeryRemainder {x : ℝ} (hx : 1 ≤ x) (T : ℝ) :
    ContinuousOn (montgomeryRemainder x) (Icc 0 T) := by
  have hE : ∀ t, montgomeryRemainder x t
      = -2 * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) * lorentzZeroSumAll x t - primeSide x t := by
    intro t
    have h1 := tsum_montgomeryZeroTerm_eq hx t
    by_cases hx1 : 1 < x
    · have h2 := tsum_montgomeryZeroTerm_eq_primeSide_add_remainder hx1 t
      rw [← h1, h2]; ring
    · have hx1' : x = 1 := le_antisymm (not_lt.mp hx1) hx
      subst hx1'
      -- at `x = 1` both sides are computed directly from the definitions
      simp only [montgomeryRemainder, polarRemainder, xbBlock, trivialBlock, primeSide,
        primeSideTerm, Complex.ofReal_one, Complex.one_cpow, mul_one]
      sorry
  sorry

end RHTower

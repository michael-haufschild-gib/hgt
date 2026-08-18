import GaloisForLFunctions.RHTower.Sieve.FibreRoughSecondMoment
import GaloisForLFunctions.RHTower.Sieve.BandPairCount

/-!
# The discarded set, reduced to shifted counts

Composing the fibre second-moment identity with the band-pair count expresses the whole cost of
discarding a set as a sum of **shifted counts** `#{m : m and m + d both in the set}` over
`|d| ≤ h` — exactly what a two-dimensional sieve bounds.

No arithmetic enters here: `T` is an arbitrary finite set of integers.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The cost of discarding a set is a sum of shifted counts.** -/
theorem sum_sq_card_fibre_inter_le_shifts {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h) (T : Finset ℕ) :
    ∑ a ∈ outerBlock x h, (((innerFibre x h a ∩ T).card : ℝ)) ^ 2
      ≤ (2 * h + 1) * (2 * ∑ d ∈ Finset.range (⌊h⌋₊ + 1),
          ((((T ∩ fibreDyadicIndex x h).filter
            (fun m => m + d ∈ T ∩ fibreDyadicIndex x h)).card : ℕ) : ℝ)) := by
  classical
  refine (sum_sq_card_fibre_inter_le_band hx hh0 T).trans ?_
  exact mul_le_mul_of_nonneg_left (card_bandPairs_le (T ∩ fibreDyadicIndex x h)) (by linarith)

end

end RHTower.Sieve

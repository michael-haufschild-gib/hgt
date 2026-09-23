import GaloisForLFunctions.RHTower.Sieve.BalancedDivisorSecondMoment
import GaloisForLFunctions.RHTower.Sieve.WindowMultiplicity

/-!
# A distinct-image lower bound from a second moment

Writing the source count as a sum of fibre sizes and applying Cauchy–Schwarz,

`(#S)² ≤ #(image f) · ∑_{t ∈ image f} (#fibre t)²`,

so a representation count and a second moment of the multiplicity together bound the number of
*distinct* images from below.  This is the passage the coprime card's hard gate asks for: `(3)`
counts representations, and what is wanted is a count of physical products.

Nothing arithmetic enters — only that the source set is the disjoint union of its fibres.
-/

namespace RHTower.Sieve

open Finset

/-- **Cauchy–Schwarz lower bound for the image of a finite set.** -/
theorem sq_card_le_card_image_mul_sum_sq_fibre {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (f : ι → κ) :
    ((S.card : ℕ) : ℝ) ^ (2 : ℕ)
      ≤ (((S.image f).card : ℕ) : ℝ)
        * ∑ t ∈ S.image f, (((S.filter (fun i => f i = t)).card : ℕ) : ℝ) ^ (2 : ℕ) := by
  classical
  have hcard : ((S.card : ℕ) : ℝ)
      = ∑ t ∈ S.image f, (((S.filter (fun i => f i = t)).card : ℕ) : ℝ) := by
    rw [Finset.card_eq_sum_card_image f S]
    push_cast
    ring
  rw [hcard]
  exact sq_sum_le_card_mul_sum_sq

/-- **The image is large when the second moment is small.** -/
theorem card_image_ge_of_sum_sq_le {ι κ : Type*} [DecidableEq κ]
    (S : Finset ι) (f : ι → κ) {V : ℝ} (hV : 0 < V)
    (hsum : ∑ t ∈ S.image f, (((S.filter (fun i => f i = t)).card : ℕ) : ℝ) ^ (2 : ℕ) ≤ V) :
    ((S.card : ℕ) : ℝ) ^ (2 : ℕ) / V ≤ (((S.image f).card : ℕ) : ℝ) := by
  classical
  have hbase := sq_card_le_card_image_mul_sum_sq_fibre S f
  have himg : (0 : ℝ) ≤ (((S.image f).card : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [div_le_iff₀ hV]
  calc ((S.card : ℕ) : ℝ) ^ (2 : ℕ)
      ≤ (((S.image f).card : ℕ) : ℝ)
        * ∑ t ∈ S.image f, (((S.filter (fun i => f i = t)).card : ℕ) : ℝ) ^ (2 : ℕ) := hbase
    _ ≤ (((S.image f).card : ℕ) : ℝ) * V := mul_le_mul_of_nonneg_left hsum himg

end RHTower.Sieve

import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualVariationDuhamel
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualSourcePrimitive
import GaloisForLFunctions.RHTower.Sieve.SmoothAFEZetaSquareExactAFE

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

theorem smoothAFEZetaSquareDualVariationSourceField_eq_sourceField_sub
    {N : ℕ} {a u t : ℝ} (hN : 4 ≤ N)
    (ha : a ∈ Set.Icc (N : ℝ) (2 * N : ℝ))
    (hu : u ∈ Set.Icc (N : ℝ) (2 * N : ℝ)) :
    smoothAFEZetaSquareDualVariationSourceField (N : ℝ) a u t =
      smoothAFEZetaSquareDualSourceField (N : ℝ) u t -
        smoothAFEZetaSquareDualSourceField (N : ℝ) a t := by
  rw [smoothAFEZetaSquareDualVariationSourceField_eq_intervalIntegral_derivative
    hN ha hu]
  exact integral_smoothAFEZetaSquareDualDerivativeSourceField_eq_sub
    (show 0 < (N : ℝ) by exact_mod_cast (show 0 < N by omega)) a u t

theorem smoothAFEZetaSquareDualSourceField_diagonal_eq_frozen_add_variation
    {N : ℕ} (hN : 4 ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc (N : ℝ) (2 * N : ℝ)) :
    smoothAFEZetaSquareDualSourceField (N : ℝ) t t =
      smoothAFEZetaSquareDualSourceField (N : ℝ) (N : ℝ) t +
        smoothAFEZetaSquareDualVariationSourceField (N : ℝ) (N : ℝ) t t := by
  have hNN : (N : ℝ) ∈ Set.Icc (N : ℝ) (2 * N : ℝ) := by
    constructor
    · exact le_rfl
    · have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
  rw [smoothAFEZetaSquareDualVariationSourceField_eq_sourceField_sub hN hNN ht]
  ring

theorem smoothAFEZetaSquareDual_tsum_eq_chiSq_mul_sourceField
    (T r t : ℝ) :
    (∑' n : ℕ, zetaChi (linePt t) ^ (2 : ℕ) *
      ((n + 1).divisors.card : ℂ) *
      (n + 1 : ℂ) ^ (linePt t - 1) *
      smoothAFEZetaSquareDualWeight r ((n + 1 : ℝ) * T)) =
      zetaChi (linePt t) ^ (2 : ℕ) *
        smoothAFEZetaSquareDualSourceField T r t := by
  rw [smoothAFEZetaSquareDualSourceField]
  calc
    (∑' n : ℕ, zetaChi (linePt t) ^ (2 : ℕ) *
      ((n + 1).divisors.card : ℂ) *
      (n + 1 : ℂ) ^ (linePt t - 1) *
      smoothAFEZetaSquareDualWeight r ((n + 1 : ℝ) * T)) =
        ∑' n : ℕ, zetaChi (linePt t) ^ (2 : ℕ) *
          (((n + 1).divisors.card : ℂ) *
          (n + 1 : ℂ) ^ (linePt t - 1) *
          smoothAFEZetaSquareDualWeight r ((n + 1 : ℝ) * T)) := by
            apply tsum_congr
            intro n
            ring
    _ = zetaChi (linePt t) ^ (2 : ℕ) *
        ∑' n : ℕ, ((n + 1).divisors.card : ℂ) *
          (n + 1 : ℂ) ^ (linePt t - 1) *
          smoothAFEZetaSquareDualWeight r ((n + 1 : ℝ) * T) := by
            rw [tsum_mul_left]

theorem smoothAFEZetaSquareDual_tsum_diagonal_eq_frozen_add_variation
    {N : ℕ} (hN : 4 ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc (N : ℝ) (2 * N : ℝ)) :
    (∑' n : ℕ, zetaChi (linePt t) ^ (2 : ℕ) *
      ((n + 1).divisors.card : ℂ) *
      (n + 1 : ℂ) ^ (linePt t - 1) *
      smoothAFEZetaSquareDualWeight t ((n + 1 : ℝ) * (N : ℝ))) =
      zetaChi (linePt t) ^ (2 : ℕ) *
        (smoothAFEZetaSquareDualSourceField (N : ℝ) (N : ℝ) t +
          smoothAFEZetaSquareDualVariationSourceField
            (N : ℝ) (N : ℝ) t t) := by
  rw [smoothAFEZetaSquareDual_tsum_eq_chiSq_mul_sourceField,
    smoothAFEZetaSquareDualSourceField_diagonal_eq_frozen_add_variation hN ht]

end RHTower

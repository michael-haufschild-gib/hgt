import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualVariationDuhamel
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualSourcePrimitive
import GaloisForLFunctions.RHTower.Sieve.SmoothAFEZetaSquareExactAFE

/-!
# Square-dual AFE source field: frozen height plus variation

The dual side of the smoothed approximate functional equation for `ζ(s)^2` at `s = 1/2 + it` is
`χ(s)^2 · S(T, r, t)` with `S(T, r, t) = ∑_n d(n) n^(s - 1) W_r(n T)`, where `W_r` is the dual
weight at height `r` and `d(n)` the divisor function. This module writes the diagonal choice
`r = t` as the value at the frozen height `r = N` plus the variation
`V(N, N, t, t) = S(N, t, t) - S(N, N, t)`, for `t ∈ [N, 2N]`.

## Main results

- `smoothAFEZetaSquareDualVariationSourceField_eq_sourceField_sub`: for `N ≥ 4` and
  `a, u ∈ [N, 2N]`, the variation field is `S(N, u, t) - S(N, a, t)`.
- `smoothAFEZetaSquareDualSourceField_diagonal_eq_frozen_add_variation`: for `t ∈ [N, 2N]`,
  `S(N, t, t) = S(N, N, t) + V(N, N, t, t)`.
- `smoothAFEZetaSquareDual_tsum_eq_chiSq_mul_sourceField`: the dual series equals
  `χ(s)^2 · S(T, r, t)`.
- `smoothAFEZetaSquareDual_tsum_diagonal_eq_frozen_add_variation`: the diagonal dual series equals
  `χ(s)^2 (S(N, N, t) + V(N, N, t, t))`.

## Hypotheses

Unconditional; the seam identities assume `N ≥ 4` and heights in `[N, 2N]`.
-/

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

/-- For `N ≥ 4` and `a, u ∈ [N, 2N]`, the square-dual variation source field equals the difference
`S(N, u, t) - S(N, a, t)` of source fields at heights `u` and `a`. -/
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

/-- For `N ≥ 4` and `t ∈ [N, 2N]`, the diagonal source field splits as
`S(N, t, t) = S(N, N, t) + V(N, N, t, t)`. -/
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

/-- The dual AFE series `∑ χ(s)^2 d(n) n^(s - 1) W_r(n T)` at `s = 1/2 + it` equals
`χ(s)^2 · S(T, r, t)`. -/
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

/-- For `N ≥ 4` and `t ∈ [N, 2N]`, the diagonal dual AFE series equals
`χ(s)^2 (S(N, N, t) + V(N, N, t, t))`. -/
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

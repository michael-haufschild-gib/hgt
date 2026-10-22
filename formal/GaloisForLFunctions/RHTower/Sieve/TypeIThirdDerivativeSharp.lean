import GaloisForLFunctions.RHTower.Sieve.TypeIBound
import GaloisForLFunctions.RHTower.Sieve.TypeILogWeight
import GaloisForLFunctions.RHTower.Sieve.DilatedNearDiagonalSum
import GaloisForLFunctions.RHTower.Sieve.NearDiagonalThirdDerivativeSharp

/-!
# Sharp third-derivative bound for Type I near-diagonal sums

Applies the sharp third-derivative (van der Corput) estimate to the Type I near-diagonal exponential
sums `∑_{A ≤ m < B} e((T/2π) log(1 + r/(m d)))`. After dilation by `d` the sum is a near-diagonal
sum at shift `r/d`, and the bound is `16 · 1368 ((B - A) λ^(1/6) + √(B - A) λ^(-1/6))` with
`λ = T (r/d) / (72 π A^4)`. A partial-summation step adds a logarithmic weight `log m`.

## Main results

- `sharpThirdDerivativeTypeIBound`: the bound `16 · 1368 ((B - A) λ^(1/6) + √(B - A) λ^(-1/6))`.
- `norm_sum_ndExp_third_sharp_le`: the Type I sum over `[A, B)` is bounded by it.
- `sharpThirdDerivativeTypeIBound_mono`: the bound is monotone in the upper endpoint.
- `norm_sum_log_ndExp_third_sharp_le`: the `log m`-weighted sum is at most
  `2 · bound · log(B - 1)`.

## Hypotheses

Unconditional. The estimates assume `T, r > 0`, `d ≥ 1`, `A ≥ 1`, the short-span condition
`B - A - 1 ≤ A`, `r/d ≤ A` and `λ ≤ 1` (and `A < B` for the weighted sum).
-/

namespace RHTower.Sieve

open RHTower

noncomputable section

/-- Sharp third-derivative bound `16 · 1368 ((B - A) λ^(1/6) + √(B - A) λ^(-1/6))` with
`λ = nearDiagonalLambda3 T (r/d) A = T (r/d) / (72 π A^4)`. -/
def sharpThirdDerivativeTypeIBound (T r : ℝ) (d A B : ℕ) : ℝ :=
  16 * 1368 * ((((B - A : ℕ) : ℝ) * nearDiagonalLambda3 T (r / d) A ^ (1 / 6 : ℝ))
    + Real.sqrt (((B - A : ℕ) : ℝ)) *
      nearDiagonalLambda3 T (r / d) A ^ (-(1 / 6 : ℝ)))

/-- Assuming `T, r > 0`, `d, A ≥ 1`, `B - A - 1 ≤ A`, `r/d ≤ A` and `λ ≤ 1`, the Type I sum
`∑_{A ≤ m < B} e((T/2π) log(1 + r/(m d)))` has norm at most `sharpThirdDerivativeTypeIBound T r d A B`. -/
theorem norm_sum_ndExp_third_sharp_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {d : ℕ} (hd : 1 ≤ d) (A B : ℕ) (hA : 1 ≤ A) (hspan : B - A - 1 ≤ A)
    (hrA : r / d ≤ (A : ℝ)) (hlam1 : nearDiagonalLambda3 T (r / d) A ≤ 1) :
    ‖∑ m ∈ Finset.Ico A B, ndExp T r m d‖
      ≤ sharpThirdDerivativeTypeIBound T r d A B := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [sum_ndExp_eq_dilated, dilated_nearDiagonalSum_eq T r d A B]
  exact norm_nearDiagonalSum_third_sharp_le hT (div_pos hr hd0) A B hA hspan hrA hlam1

theorem sharpThirdDerivativeTypeIBound_nonneg {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {d A B : ℕ} (hd : 1 ≤ d) (hA : 1 ≤ A) :
    0 ≤ sharpThirdDerivativeTypeIBound T r d A B := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hlam0 : 0 < nearDiagonalLambda3 T (r / d) A :=
    nearDiagonalLambda3_pos hT (div_pos hr hd0) hA0
  rw [sharpThirdDerivativeTypeIBound]
  positivity

/-- For `T, r > 0` and `d, A ≥ 1`, the sharp Type I bound is monotone in the upper endpoint `B`. -/
theorem sharpThirdDerivativeTypeIBound_mono {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {d A J B : ℕ} (hd : 1 ≤ d) (hA : 1 ≤ A) (hJB : J ≤ B) :
    sharpThirdDerivativeTypeIBound T r d A J ≤
      sharpThirdDerivativeTypeIBound T r d A B := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hlam0 : 0 < nearDiagonalLambda3 T (r / d) A :=
    nearDiagonalLambda3_pos hT (div_pos hr hd0) hA0
  have hsub : J - A ≤ B - A := Nat.sub_le_sub_right hJB A
  have hsubR : (((J - A : ℕ) : ℝ)) ≤ (((B - A : ℕ) : ℝ)) := by exact_mod_cast hsub
  have hsqrt : Real.sqrt (((J - A : ℕ) : ℝ)) ≤ Real.sqrt (((B - A : ℕ) : ℝ)) :=
    Real.sqrt_le_sqrt hsubR
  have hfirst0 : 0 ≤ nearDiagonalLambda3 T (r / d) A ^ (1 / 6 : ℝ) := by positivity
  have hsecond0 : 0 ≤ nearDiagonalLambda3 T (r / d) A ^ (-(1 / 6 : ℝ)) := by positivity
  rw [sharpThirdDerivativeTypeIBound, sharpThirdDerivativeTypeIBound]
  nlinarith [mul_le_mul_of_nonneg_right hsubR hfirst0,
    mul_le_mul_of_nonneg_right hsqrt hsecond0]

/-- Under the hypotheses of `norm_sum_ndExp_third_sharp_le` and `A < B`, the `log k`-weighted sum
`∑_{A ≤ k < B} log k · e((T/2π) log(1 + r/(k d)))` is at most `2 · bound · log(B - 1)`, by partial
summation. -/
theorem norm_sum_log_ndExp_third_sharp_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {d : ℕ} (hd : 1 ≤ d) {A B : ℕ} (hAB : A < B) (hA : 1 ≤ A)
    (hspan : B - A - 1 ≤ A) (hrA : r / d ≤ (A : ℝ))
    (hlam1 : nearDiagonalLambda3 T (r / d) A ≤ 1) :
    ‖∑ k ∈ Finset.Ico A B, ((Real.log k : ℝ) : ℂ) * ndExp T r k d‖
      ≤ 2 * sharpThirdDerivativeTypeIBound T r d A B * Real.log ((B - 1 : ℕ) : ℝ) := by
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  refine norm_sum_Ico_mul_le_of_bounded_partial_mono hAB (fun k => Real.log k)
    (fun k => ndExp T r k d) (Real.log_nonneg hA1) ?_ ?_
  · intro i hi
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast le_trans hA hi
    refine Real.log_le_log (by linarith) ?_
    push_cast
    linarith
  · intro k hk
    have hle : A + k ≤ B := by omega
    have hspan' : A + k - A - 1 ≤ A := by omega
    refine (norm_sum_ndExp_third_sharp_le hT hr hd A (A + k) hA hspan' hrA hlam1).trans ?_
    exact sharpThirdDerivativeTypeIBound_mono hT hr hd hA hle

end

end RHTower.Sieve

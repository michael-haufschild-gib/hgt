import GaloisForLFunctions.RHTower.Sieve.DyadicOverlapKernel

/-!
# The dyadic mean square is a near-diagonal bilinear form

Combining the exact pair expansion with the overlap bound:

```text
dyadicMeanSquare f ℓ A B ≤ ∑_{m, n ∈ (A, B+ℓ]} |f(m)|·|f(n)|·(ℓ − |m − n|)₊ .
```

The right-hand side is supported on `|m − n| < ℓ`, and it is the same bilinear form that
`gallagher_identity` evaluates as `∫ (𝓕 triC δ)·|logPoly|²` — with the additive kernel
`(ℓ − |m − n|)₊` in place of the multiplicative `(δ − |log m − log n|)₊`.

This is the last purely combinatorial step: from here the argument is analytic.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The dyadic mean square, bounded by its near-diagonal band.** -/
theorem dyadicMeanSquare_le_band (f : ℕ → ℝ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (A B : ℕ) :
    dyadicMeanSquare f ℓ A B
      ≤ ∑ m ∈ Finset.Icc (A + 1) (B + ℓ), ∑ n ∈ Finset.Icc (A + 1) (B + ℓ),
          |f m| * |f n| * max ((ℓ : ℝ) - |(m : ℝ) - (n : ℝ)|) 0 := by
  classical
  rw [dyadicMeanSquare_eq_count f hℓ A B]
  refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => ?_
  set K : ℝ := (((Finset.Icc A B).filter
      (fun z => m ∈ Finset.Icc (z + 1) (z + ℓ)
        ∧ n ∈ Finset.Icc (z + 1) (z + ℓ))).card : ℝ) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; exact Nat.cast_nonneg _
  have habs : (0 : ℝ) ≤ |f m| * |f n| := by positivity
  calc f m * f n * K ≤ |f m * f n * K| := le_abs_self _
    _ = |f m| * |f n| * K := by rw [abs_mul, abs_mul, abs_of_nonneg hK0]
    _ ≤ |f m| * |f n| * max ((ℓ : ℝ) - |(m : ℝ) - (n : ℝ)|) 0 :=
        mul_le_mul_of_nonneg_left (overlap_card_le ℓ A B m n) habs

/-- The band vanishes off the diagonal strip. -/
theorem band_kernel_eq_zero {ℓ m n : ℕ} (h : (ℓ : ℝ) ≤ |(m : ℝ) - (n : ℝ)|) :
    max ((ℓ : ℝ) - |(m : ℝ) - (n : ℝ)|) 0 = 0 :=
  max_eq_right (by linarith)

end RHTower.Sieve

end

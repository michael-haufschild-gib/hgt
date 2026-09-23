import GaloisForLFunctions.RHTower.Sieve.FejerHalf

/-!
# The symmetric Fejér transform

Adding the half-interval transform at `L` to its value at `-L` — which is what the reflection
`t ↦ -t` turns the left half of a symmetric triangular weight into — gives

`2(1 - cos TL)/(TL²)`.

The `i/L` terms cancel: they are purely imaginary and odd, and they are exactly the part decaying
only like `|L|^{-1}`.  What survives is real, nonnegative (since `cos ≤ 1`) and `O(|L|^{-2})`.

Those are the two properties a localisation argument needs and the sharp kernel `2 sin(TL)/L` lacks:
nonnegativity, so tails can be discarded without sign cancellation, and square-summable decay, so the
discard is quantitatively small.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- The sum of conjugate phases. -/
theorem exp_phase_add_neg (θ : ℝ) :
    Complex.exp (((θ : ℝ) : ℂ) * Complex.I) + Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)
      = 2 * Complex.cos ((θ : ℝ) : ℂ) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- **The symmetric Fejér transform.** -/
theorem integral_fejer_symm (L : ℝ) (hL : L ≠ 0) {T : ℝ} (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, ((1 - t / T : ℝ) : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I))
      + (∫ t in (0 : ℝ)..T,
          ((1 - t / T : ℝ) : ℂ) * Complex.exp (((t * (-L) : ℝ) : ℂ) * Complex.I))
      = (2 - 2 * Complex.cos (((T * L : ℝ)) : ℂ)) / ((T : ℂ) * (L : ℂ) ^ (2 : ℕ)) := by
  have hLne : (-L) ≠ 0 := neg_ne_zero.mpr hL
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hT)
  rw [integral_fejerHalf L hL hT, integral_fejerHalf (-L) hLne hT]
  have hneg : ((T * (-L) : ℝ) : ℂ) = ((-(T * L) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hneg]
  have hsub : Complex.exp (((-(T * L) : ℝ) : ℂ) * Complex.I)
      = 2 * Complex.cos (((T * L : ℝ)) : ℂ)
        - Complex.exp (((T * L : ℝ) : ℂ) * Complex.I) := by
    have hadd := exp_phase_add_neg (T * L)
    linear_combination hadd
  rw [hsub]
  push_cast
  field_simp
  ring

end RHTower.Sieve

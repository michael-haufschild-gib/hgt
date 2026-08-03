import GaloisForLFunctions.RHTower.Sieve.ChordalSeparation

/-!
# Bounded partial sums of the conjugate Dirichlet kernel

The partial sums of `∑ sin(dθ)` are bounded uniformly in the number of terms, by a quantity
depending only on `θ`:

`|∑_{d < D} sin(dθ)| ≤ 1 / |sin(θ/2)|`.

The proof composes two facts already in the corpus: the geometric sum bound
`‖∑_{d < D} ζ^d‖ ≤ 2/‖ζ - 1‖` of `GeometricSumBound.lean`, and the chord identity
`‖exp(iθ) - 1‖ = 2|sin(θ/2)|` of `ChordalSeparation.lean`.  Taking imaginary parts loses nothing.

Uniformly bounded partial sums are the Abel-summation input for the classical estimate of
`∑_{d ≤ M} sin(dθ)/d`, which is in turn what converts the Toeplitz kernel `1/(m-n)` into a bounded
Fourier multiplier — the route to Hilbert's inequality and hence to the sharp large sieve constant.
-/

namespace RHTower.Sieve

open Finset

/-- Powers of `exp(iθ)` are the exponentials of the multiples of `θ`. -/
theorem exp_I_pow (θ : ℝ) (d : ℕ) :
    (Complex.exp ((θ : ℂ) * Complex.I)) ^ d = Complex.exp (((d * θ : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **Geometric partial sums on the circle.** -/
theorem norm_sum_exp_le {θ : ℝ} (hθ : Complex.exp ((θ : ℂ) * Complex.I) ≠ 1) (D : ℕ) :
    ‖∑ d ∈ Finset.range D, Complex.exp (((d * θ : ℝ) : ℂ) * Complex.I)‖
      ≤ 1 / |Real.sin (θ / 2)| := by
  have hcong : ∑ d ∈ Finset.range D, Complex.exp (((d * θ : ℝ) : ℂ) * Complex.I)
      = ∑ d ∈ Finset.range D, (Complex.exp ((θ : ℂ) * Complex.I)) ^ d :=
    Finset.sum_congr rfl fun d _ => (exp_I_pow θ d).symm
  rw [hcong]
  have hnorm : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    simp
  refine le_trans (norm_geom_sum_le hnorm hθ D) ?_
  rw [norm_exp_I_sub_one θ]
  have hsin : (0 : ℝ) < |Real.sin (θ / 2)| := by
    rcases eq_or_lt_of_le (abs_nonneg (Real.sin (θ / 2))) with h | h
    · exfalso
      have hz : Real.sin (θ / 2) = 0 := by
        have := abs_eq_zero.1 h.symm
        exact this
      apply hθ
      have hchord : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 0 := by
        rw [norm_exp_I_sub_one θ, hz, abs_zero, mul_zero]
      have hz2 := norm_eq_zero.1 hchord
      exact sub_eq_zero.1 hz2
    · exact h
  rw [div_le_div_iff₀ (by linarith) hsin]
  linarith

/-- **Bounded sine partial sums.** -/
theorem abs_sum_sin_le {θ : ℝ} (hθ : Complex.exp ((θ : ℂ) * Complex.I) ≠ 1) (D : ℕ) :
    |∑ d ∈ Finset.range D, Real.sin ((d : ℝ) * θ)| ≤ 1 / |Real.sin (θ / 2)| := by
  have him : (∑ d ∈ Finset.range D, Complex.exp (((d * θ : ℝ) : ℂ) * Complex.I)).im
      = ∑ d ∈ Finset.range D, Real.sin ((d : ℝ) * θ) := by
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Complex.exp_ofReal_mul_I_im]
  have hle := norm_sum_exp_le hθ D
  have habs : |(∑ d ∈ Finset.range D, Complex.exp (((d * θ : ℝ) : ℂ) * Complex.I)).im|
      ≤ ‖∑ d ∈ Finset.range D, Complex.exp (((d * θ : ℝ) : ℂ) * Complex.I)‖ :=
    Complex.abs_im_le_norm _
  rw [him] at habs
  linarith

end RHTower.Sieve

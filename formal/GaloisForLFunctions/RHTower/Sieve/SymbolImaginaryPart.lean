import GaloisForLFunctions.RHTower.Sieve.AntisymmetricSymbol

/-!
# The symbol's imaginary part is the sine sum

`AntisymmetricSymbol.lean` expresses the antisymmetrised symbol as `2i` times
`∑_d K_d · Im(ζ^{jd})`, where the multiplier apparatus supplies the imaginary parts as components of
powers.  `HarmonicSineBound.lean` bounds a sum of `Real.sin`.  The two are the same quantity:

`Im((exp(iθ))^k) = sin(kθ)`.

Rewriting through that identity puts the uniform bound `1 + 3π` directly on the symbol's imaginary
part, in the form the kernel dictionary consumes.
-/

namespace RHTower.Sieve

open Finset

/-- The imaginary part of a power of a unimodular exponential. -/
theorem im_exp_pow (θ : ℝ) (k : ℕ) :
    ((Complex.exp ((θ : ℂ) * Complex.I)) ^ k).im = Real.sin ((k : ℝ) * θ) := by
  rw [exp_I_pow θ k, Complex.exp_ofReal_mul_I_im]

/-- **Uniform bound on the symbol's imaginary part.**  The harmonic-weighted sum of imaginary parts
is bounded by an absolute constant. -/
theorem abs_sum_im_exp_pow_div_le {θ : ℝ} (h0 : 0 < θ) (hpi : θ ≤ Real.pi) (M : ℕ) :
    |∑ d ∈ Finset.range M,
        (1 / ((d : ℝ) + 1)) * ((Complex.exp ((θ : ℂ) * Complex.I)) ^ d).im|
      ≤ 1 + 3 * Real.pi := by
  have hcong : ∀ d ∈ Finset.range M,
      (1 / ((d : ℝ) + 1)) * ((Complex.exp ((θ : ℂ) * Complex.I)) ^ d).im
        = (1 / ((d : ℝ) + 1)) * Real.sin ((d : ℝ) * θ) := by
    intro d _
    rw [im_exp_pow θ d]
  rw [Finset.sum_congr rfl hcong]
  exact abs_sum_sin_div_le_uniform h0 hpi M

end RHTower.Sieve

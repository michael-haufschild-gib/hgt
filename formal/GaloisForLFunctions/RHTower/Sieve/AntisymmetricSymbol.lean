import GaloisForLFunctions.RHTower.Sieve.KernelValue

/-!
# The antisymmetric symbol is purely imaginary

The full symbol of a one-sided coefficient sequence is *not* bounded: for `K_d = 1/d` its real part
is `∑_d cos(dθ)/d`, which diverges like `-log|2 sin(θ/2)|`.  Only the imaginary part is uniformly
bounded, which is why Hilbert's inequality concerns the *antisymmetric* kernel.

Pairing each coefficient with its complementary index makes this explicit:

`ζ^{jd} - ζ^{j(Q-d)} = 2i · Im(ζ^{jd})`,

since `ζ^{j(Q-d)}` is the conjugate of `ζ^{jd}`.  So the antisymmetrised symbol is `2i` times a real
sine sum — exactly the quantity `HarmonicSineBound.lean` bounds by `1 + 3π` when weighted by `1/d`.

This is the structural reason the kernel `1/(m-n)` has a bounded symbol while `1/|m-n|` does not.
-/

namespace RHTower.Sieve

open Finset

/-- **Antisymmetrised character is purely imaginary.** -/
theorem antisym_pow_eq {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q) {d : ℕ}
    (hd : d ≤ Q) (j : ℕ) :
    ζ ^ (j * d) - ζ ^ (j * (Q - d)) = 2 * ((ζ ^ (j * d)).im : ℂ) * Complex.I := by
  rw [← conj_pow_eq hQ hζ hd j, Complex.sub_conj]
  push_cast
  ring

/-- The antisymmetrised symbol of a real coefficient sequence is `2i` times a sine sum. -/
theorem antisym_symbol_eq {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q)
    (K : ℕ → ℝ) (j : ℕ) :
    ∑ d ∈ Finset.range (Q + 1), (K d : ℂ) * (ζ ^ (j * d) - ζ ^ (j * (Q - d)))
      = 2 * Complex.I * ((∑ d ∈ Finset.range (Q + 1), K d * (ζ ^ (j * d)).im : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdle : d ≤ Q := by
    have := Finset.mem_range.1 hd
    omega
  rw [antisym_pow_eq hQ hζ hdle j, Complex.ofReal_mul]
  ring

end RHTower.Sieve

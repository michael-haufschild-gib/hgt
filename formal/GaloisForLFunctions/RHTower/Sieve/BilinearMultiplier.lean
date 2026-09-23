import GaloisForLFunctions.RHTower.Sieve.ResidueSingleton

/-!
# The bilinear bound for a multiplier, stated on the kernel

Combining the two halves already proved: a symbol bounded by `C` gives a quadratic form bounded by
`C·Q‖x‖²` (`SymbolBound.lean`), and the multiplier with that symbol *is* the kernel
`Ǩ(m,n) = ∑_j c_j conj(ζ^{jm}) ζ^{jn}` (`CoefficientExpansion.lean`).  Hence

`‖∑_m ∑_n x_m conj(x_n) Ǩ(m,n)‖ ≤ C · Q ‖x‖²`.

This is the bilinear inequality in the shape Hilbert's inequality takes: the left side is an
arbitrary sesquilinear form built from a Toeplitz-type kernel, and the bound depends only on the
sup-norm of the kernel's symbol.  Specialising the symbol to that of `1/(m-n)`, whose absolute bound
is `HarmonicSineBound.lean`, is what remains.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- **Bilinear bound from a bounded symbol.** -/
theorem abs_sum_kernel_bilinear_le {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q)
    {c : Fin Q → ℝ} {C : ℝ} (hc : ∀ j, |c j| ≤ C) (x : EuclideanSpace ℂ (Fin Q)) :
    ‖∑ m : Fin Q, ∑ n : Fin Q, (x m * (starRingEnd ℂ) (x n))
        * ∑ j : Fin Q, (c j : ℂ)
            * ((starRingEnd ℂ) ((ζ ^ (j : ℕ)) ^ (m : ℕ)) * (ζ ^ (j : ℕ)) ^ (n : ℕ))‖
      ≤ C * ((Q : ℝ) * ‖x‖ ^ (2 : ℕ)) := by
  rw [← sum_symbol_mul_normSq_eq Q ζ c x]
  set r : ℝ := ∑ j : Fin Q, c j * ‖⟪expRow Q (ζ ^ (j : ℕ)), x⟫_ℂ‖ ^ (2 : ℕ) with hr
  have hnorm : ‖((r : ℝ) : ℂ)‖ = |r| := by simp
  rw [hnorm, hr]
  exact abs_sum_symbol_mul_norm_inner_le hQ hζ hc x

end RHTower.Sieve

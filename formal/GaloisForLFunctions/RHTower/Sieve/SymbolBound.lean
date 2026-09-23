import GaloisForLFunctions.RHTower.Sieve.DiscreteParseval

/-!
# A bounded symbol gives a bounded quadratic form

A Fourier multiplier acts on the exponential coordinates by scaling the `j`-th coefficient by the
symbol value `c j`.  Since the coefficients enter Parseval with nonnegative weights, a symbol bounded
by `C` gives a quadratic form bounded by `C` times the energy:

`|∑_j c_j |⟪expRow Q (ζ^j), x⟫|²| ≤ C · Q ‖x‖²`.

The proof is the triangle inequality followed by exact discrete Parseval; no cancellation is used,
so the constant is exactly the sup-norm of the symbol.

This is the abstract half of Hilbert's inequality.  Applied with the symbol of the Toeplitz kernel
`1/(m-n)` — bounded by an absolute constant in `HarmonicSineBound.lean` — it gives a bilinear bound
with an absolute constant, which is what upgrades the large sieve from
`Δ = N + O(δ^{-1} log δ^{-1})` to `Δ = N + O(δ^{-1})`.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- **Bounded symbol, bounded form.** -/
theorem abs_sum_symbol_mul_norm_inner_le {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q)
    (hζ : IsPrimitiveRoot ζ Q) {c : Fin Q → ℝ} {C : ℝ} (hc : ∀ j, |c j| ≤ C)
    (x : EuclideanSpace ℂ (Fin Q)) :
    |∑ j : Fin Q, c j * ‖⟪expRow Q (ζ ^ (j : ℕ)), x⟫_ℂ‖ ^ (2 : ℕ)| ≤ C * ((Q : ℝ) * ‖x‖ ^ (2 : ℕ)) := by
  classical
  have hpar := sum_norm_inner_expRow_root hQ hζ x
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ j : Fin Q,
      |c j * ‖⟪expRow Q (ζ ^ (j : ℕ)), x⟫_ℂ‖ ^ (2 : ℕ)|
        ≤ C * ‖⟪expRow Q (ζ ^ (j : ℕ)), x⟫_ℂ‖ ^ (2 : ℕ) := by
    intro j
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖⟪expRow Q (ζ ^ (j : ℕ)), x⟫_ℂ‖)]
    exact mul_le_mul_of_nonneg_right (hc j) (sq_nonneg _)
  have hstep : ∑ j : Fin Q, |c j * ‖⟪expRow Q (ζ ^ (j : ℕ)), x⟫_ℂ‖ ^ (2 : ℕ)|
      ≤ ∑ j : Fin Q, C * ‖⟪expRow Q (ζ ^ (j : ℕ)), x⟫_ℂ‖ ^ (2 : ℕ) :=
    Finset.sum_le_sum fun j _ => hterm j
  refine le_trans hstep ?_
  rw [← Finset.mul_sum, hpar]

end RHTower.Sieve

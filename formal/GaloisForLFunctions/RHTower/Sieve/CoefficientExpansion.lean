import GaloisForLFunctions.RHTower.Sieve.SymbolBound

/-!
# Coordinates of an exponential coefficient

The coefficient of a vector against an exponential row is its finite Fourier coefficient,

`⟪expRow Q ξ, x⟫ = ∑_m conj(ξ^m) x_m`,

and its squared modulus expands into the double sum

`|⟪expRow Q ξ, x⟫|² = ∑_m ∑_n conj(ξ^m) x_m · conj(conj(ξ^n) x_n)`.

Both are exact and use no orthogonality: the first is the definition of the inner product on
`EuclideanSpace`, the second is `|z|² = z · conj z` with the sum expanded.

Summing the second against a symbol `c_j` and exchanging the order of summation is what turns a
Fourier multiplier into a kernel — the last bookkeeping step between `SymbolBound.lean` and a
bilinear inequality for the Toeplitz kernel `1/(m-n)`.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- The exponential coefficient in coordinates. -/
theorem inner_expRow_apply (Q : ℕ) (ξ : ℂ) (x : EuclideanSpace ℂ (Fin Q)) :
    ⟪expRow Q ξ, x⟫_ℂ = ∑ m : Fin Q, (starRingEnd ℂ) (ξ ^ (m : ℕ)) * x m := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [expRow, RCLike.inner_apply]
  ring

/-- The squared modulus of an exponential coefficient, expanded. -/
theorem normSq_inner_expRow (Q : ℕ) (ξ : ℂ) (x : EuclideanSpace ℂ (Fin Q)) :
    ((‖⟪expRow Q ξ, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ)
      = ∑ m : Fin Q, ∑ n : Fin Q,
          ((starRingEnd ℂ) (ξ ^ (m : ℕ)) * x m)
            * (starRingEnd ℂ) ((starRingEnd ℂ) (ξ ^ (n : ℕ)) * x n) := by
  have hz : ((‖⟪expRow Q ξ, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ)
      = ⟪expRow Q ξ, x⟫_ℂ * (starRingEnd ℂ) ⟪expRow Q ξ, x⟫_ℂ := by
    rw [mul_comm, conj_mul_self]
  rw [hz, inner_expRow_apply, map_sum]
  exact Finset.sum_mul_sum _ _ _ _

end RHTower.Sieve

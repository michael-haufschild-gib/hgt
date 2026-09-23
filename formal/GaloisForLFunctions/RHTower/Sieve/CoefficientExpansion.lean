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
    ((‖⟪expRow Q ξ, x⟫_ℂ‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ∑ m : Fin Q, ∑ n : Fin Q,
          ((starRingEnd ℂ) (ξ ^ (m : ℕ)) * x m)
            * (starRingEnd ℂ) ((starRingEnd ℂ) (ξ ^ (n : ℕ)) * x n) := by
  have hz : ((‖⟪expRow Q ξ, x⟫_ℂ‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ⟪expRow Q ξ, x⟫_ℂ * (starRingEnd ℂ) ⟪expRow Q ξ, x⟫_ℂ := by
    rw [mul_comm, conj_mul_self]
  rw [hz, inner_expRow_apply, map_sum]
  exact Finset.sum_mul_sum _ _ _ _

/-- **Multiplier is a kernel.**  Summing the expansion against a symbol and exchanging the order of
summation exhibits the multiplier with symbol `c` as the kernel `∑_j c_j conj(ζ^{jm}) ζ^{jn}`. -/
theorem sum_symbol_mul_normSq_eq (Q : ℕ) (ζ : ℂ) (c : Fin Q → ℝ)
    (x : EuclideanSpace ℂ (Fin Q)) :
    ((∑ j : Fin Q, c j * ‖⟪expRow Q (ζ ^ (j : ℕ)), x⟫_ℂ‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ∑ m : Fin Q, ∑ n : Fin Q,
          (x m * (starRingEnd ℂ) (x n))
            * ∑ j : Fin Q, (c j : ℂ)
                * ((starRingEnd ℂ) ((ζ ^ (j : ℕ)) ^ (m : ℕ)) * (ζ ^ (j : ℕ)) ^ (n : ℕ)) := by
  classical
  rw [Complex.ofReal_sum]
  have h1 : ∀ j : Fin Q, ((c j * ‖⟪expRow Q (ζ ^ (j : ℕ)), x⟫_ℂ‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ∑ m : Fin Q, ∑ n : Fin Q, (c j : ℂ) *
          (((starRingEnd ℂ) ((ζ ^ (j : ℕ)) ^ (m : ℕ)) * x m) *
            (starRingEnd ℂ) ((starRingEnd ℂ) ((ζ ^ (j : ℕ)) ^ (n : ℕ)) * x n)) := by
    intro j
    rw [Complex.ofReal_mul, normSq_inner_expRow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Complex.conj_conj]
  ring

end RHTower.Sieve

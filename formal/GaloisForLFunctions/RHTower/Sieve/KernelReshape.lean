import GaloisForLFunctions.RHTower.Sieve.BilinearMultiplier

/-!
# Matching the two shapes of the kernel

`CoefficientExpansion.lean` produces the kernel in the shape `∑_j c_j conj(ζ^{jm}) ζ^{jn}`, whereas
`InverseDFT.lean` consumes it in the shape `∑_j c_j ζ^{jk}`.  The bridge is that conjugation is
inversion on the unit circle, so for `m ≤ Q`

`conj(ζ^{jm}) = ζ^{j(Q-m)}`,

because both are inverses of `ζ^{jm}` — the first since `|ζ| = 1`, the second since
`ζ^{j(Q-m)} ζ^{jm} = (ζ^Q)^j = 1`.

Substituting turns the conjugate pairing into a single character `ζ^{j((Q-m)+n)}`, which is exactly
the index at which the inverse transform reads off a coefficient.
-/

namespace RHTower.Sieve

open Finset

/-- Conjugation of a root-of-unity power is the complementary power. -/
theorem conj_pow_eq {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q) {m : ℕ}
    (hm : m ≤ Q) (j : ℕ) :
    (starRingEnd ℂ) (ζ ^ (j * m)) = ζ ^ (j * (Q - m)) := by
  have hnorm : ‖ζ‖ = 1 := norm_eq_one_of_isPrimitiveRoot hQ hζ
  have hne : ζ ^ (j * m) ≠ 0 := by
    intro hcon
    have : ‖ζ ^ (j * m)‖ = 0 := by rw [hcon, norm_zero]
    rw [norm_pow, hnorm, one_pow] at this
    norm_num at this
  have h1 : (starRingEnd ℂ) (ζ ^ (j * m)) * ζ ^ (j * m) = 1 := by
    rw [conj_mul_self, norm_pow, hnorm, one_pow]
    norm_num
  have h2 : ζ ^ (j * (Q - m)) * ζ ^ (j * m) = 1 := by
    rw [← pow_add]
    have hsum : j * (Q - m) + j * m = j * Q := by
      have : (Q - m) + m = Q := by omega
      calc j * (Q - m) + j * m = j * ((Q - m) + m) := by ring
        _ = j * Q := by rw [this]
    rw [hsum, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have := h1.trans h2.symm
  exact mul_right_cancel₀ hne this

/-- The conjugate pairing is a single character. -/
theorem kernel_pairing_eq {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q) {m : ℕ}
    (hm : m ≤ Q) (n : ℕ) (c : Fin Q → ℝ) :
    ∑ j : Fin Q, (c j : ℂ)
        * ((starRingEnd ℂ) ((ζ ^ (j : ℕ)) ^ m) * (ζ ^ (j : ℕ)) ^ n)
      = ∑ j : Fin Q, (c j : ℂ) * ζ ^ ((j : ℕ) * ((Q - m) + n)) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_mul, ← pow_mul, conj_pow_eq hQ hζ hm (j : ℕ), ← pow_add]
  congr 2
  ring

end RHTower.Sieve

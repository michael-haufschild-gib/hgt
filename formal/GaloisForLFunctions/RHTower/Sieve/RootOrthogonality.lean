import GaloisForLFunctions.RHTower.Sieve.CoefficientExpansion

/-!
# Orthogonality of the roots of unity, in divisibility form

The single relation behind every discrete Fourier computation:

`∑_{j < Q} (ζ^k)^j = Q` if `Q ∣ k`, and `0` otherwise.

Both branches are immediate — `ζ^k = 1` exactly when `Q ∣ k` for a primitive root, and otherwise the
full geometric sum vanishes because `(ζ^k)^Q = 1`.  Stating it with the `if` makes it usable as a
rewrite inside a sum over `k`, which is what the inverse discrete Fourier transform needs: summing a
symbol against `ζ^{j·k}` and exchanging returns the coefficient at the surviving index.

Together with `CoefficientExpansion.sum_symbol_mul_normSq_eq` this is what identifies the kernel of
a multiplier with a prescribed sequence.
-/

namespace RHTower.Sieve

open Finset

/-- **Orthogonality in divisibility form.** -/
theorem sum_pow_mul_eq {ζ : ℂ} {Q : ℕ} (hζ : IsPrimitiveRoot ζ Q) (k : ℕ) :
    ∑ j ∈ Finset.range Q, (ζ ^ k) ^ j = if Q ∣ k then (Q : ℂ) else 0 := by
  by_cases hdvd : Q ∣ k
  · rw [if_pos hdvd]
    have hone : ζ ^ k = 1 := (hζ.pow_eq_one_iff_dvd k).2 hdvd
    rw [hone]
    simp
  · rw [if_neg hdvd]
    have hne : ζ ^ k ≠ 1 := fun hcon => hdvd ((hζ.pow_eq_one_iff_dvd k).1 hcon)
    have hpow : (ζ ^ k) ^ Q = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    exact sum_range_pow_eq_zero hpow hne

/-- The same relation with the exponent written as a product, the form in which it appears after
exchanging the order of summation. -/
theorem sum_pow_mul_index_eq {ζ : ℂ} {Q : ℕ} (hζ : IsPrimitiveRoot ζ Q) (k : ℕ) :
    ∑ j ∈ Finset.range Q, ζ ^ (j * k) = if Q ∣ k then (Q : ℂ) else 0 := by
  rw [← sum_pow_mul_eq hζ k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_mul, mul_comm k j]

end RHTower.Sieve

import GaloisForLFunctions.RHTower.DirichletSummatorySwap

/-!
# The triple hyperbola identity

Iterating the summatory swap once more turns a threefold Dirichlet convolution into nested floor-cut
partial sums:

`∑_{m ≤ N} (a * (b * c))(m) = ∑_{p ≤ N} a(p) ∑_{q ≤ ⌊N/p⌋} b(q) ∑_{k ≤ ⌊N/p/q⌋} c(k)`.

The nested floor conditions are the hyperbola `pqk ≤ N`: `k ≤ ⌊⌊N/p⌋/q⌋ ↔ pqk ≤ N`.  This is the identity
that a Perron passage consumes when a partial sum has been rewritten as a triple multiplicative
convolution — the shape produced by two applications of the log recursion.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The triple summatory swap.** -/
theorem sum_Icc_mul_mul_apply {R : Type*} [Semiring R] (a b c : ArithmeticFunction R) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, (a * (b * c)) m)
      = ∑ p ∈ Finset.Icc 1 N, a p
          * ∑ q ∈ Finset.Icc 1 (N / p), b q * ∑ k ∈ Finset.Icc 1 (N / p / q), c k := by
  rw [RHTower.sum_Icc_mul_apply a (b * c) N]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [RHTower.sum_Icc_mul_apply b c (N / p)]

/-- The nested floor conditions are the hyperbola `pqk ≤ N`. -/
theorem le_div_div_iff {N p q k : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    k ≤ N / p / q ↔ p * q * k ≤ N := by
  rw [Nat.le_div_iff_mul_le (by omega : 0 < q), Nat.le_div_iff_mul_le (by omega : 0 < p)]
  constructor
  · intro h
    calc p * q * k = k * q * p := by ring
      _ ≤ N := h
  · intro h
    calc k * q * p = p * q * k := by ring
      _ ≤ N := h

end RHTower.Sieve

end

import GaloisForLFunctions.RHTower.Sieve.KernelReshape

/-!
# The kernel of a transform symbol

Composing the two halves of the dictionary.  If the symbol is built from a coefficient sequence,
`c_j = ∑_d K_d ζ^{jd}`, then its kernel at a strictly lower-triangular index is the coefficient at
the difference:

`∑_j c_j conj(ζ^{jm}) ζ^{jn} = Q · K_{m-n}`   for `n < m < Q`.

The conjugate becomes a power by `KernelReshape.conj_pow_eq`, turning the pairing into the single
character `ζ^{j((Q-m)+n)}`; the inverse transform of `ResidueSingleton.lean` then reads off the
coefficient at `(Q - ((Q-m)+n)) % Q`, which for `n < m < Q` is exactly `m - n`.

Restricting to `n < m` is not a loss: a Toeplitz kernel is determined off the diagonal by its lower
triangle together with its symmetry type.
-/

namespace RHTower.Sieve

open Finset

/-- **Kernel of a transform symbol.** -/
theorem kernel_value {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q) (K : ℕ → ℂ)
    {m n : ℕ} (hmQ : m < Q) (hnm : n < m) :
    ∑ j ∈ Finset.range Q, (∑ d ∈ Finset.range Q, K d * ζ ^ (j * d))
        * ((starRingEnd ℂ) (ζ ^ (j * m)) * ζ ^ (j * n))
      = (Q : ℂ) * K (m - n) := by
  have hmle : m ≤ Q := le_of_lt hmQ
  have hklt : (Q - m) + n < Q := by omega
  have hstep : ∀ j ∈ Finset.range Q,
      (∑ d ∈ Finset.range Q, K d * ζ ^ (j * d))
          * ((starRingEnd ℂ) (ζ ^ (j * m)) * ζ ^ (j * n))
        = (∑ d ∈ Finset.range Q, K d * ζ ^ (j * d)) * ζ ^ (j * ((Q - m) + n)) := by
    intro j _
    rw [conj_pow_eq hQ hζ hmle j, ← pow_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl hstep, kernel_of_symbol_singleton hζ K hQ hklt]
  congr 2
  have hval : Q - ((Q - m) + n) = m - n := by omega
  rw [hval, Nat.mod_eq_of_lt (by omega : m - n < Q)]

end RHTower.Sieve

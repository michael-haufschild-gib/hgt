import GaloisForLFunctions.RHTower.Sieve.RootOrthogonality

/-!
# Recovering a kernel from its symbol

If a symbol is built from a coefficient sequence by `c_j = ∑_d K_d ζ^{jd}`, then pairing it against
`ζ^{jk}` and summing over `j` returns the coefficients at the indices congruent to `-k`:

`∑_j (∑_d K_d ζ^{jd}) ζ^{jk} = Q · ∑_{d : Q ∣ d + k} K_d`.

The proof is one exchange of summation followed by the divisibility form of orthogonality; the `if`
in that lemma collapses the inner sum to the surviving residue class.  When `K` is supported on
`range Q` the congruence pins down a single `d`, so the right-hand side is `Q · K_{(-k) mod Q}` — the
inverse discrete Fourier transform.

Combined with `CoefficientExpansion.sum_symbol_mul_normSq_eq`, which turns a symbol into the kernel
`Ǩ(m,n) = ∑_j c_j conj(ζ^{jm}) ζ^{jn}`, this is what identifies that kernel with a prescribed
sequence.
-/

namespace RHTower.Sieve

open Finset

/-- **Kernel recovery.**  Pairing a symbol against a character returns the coefficients on the
surviving residue class. -/
theorem kernel_of_symbol {ζ : ℂ} {Q : ℕ} (hζ : IsPrimitiveRoot ζ Q) (K : ℕ → ℂ) (k : ℕ) :
    ∑ j ∈ Finset.range Q, (∑ d ∈ Finset.range Q, K d * ζ ^ (j * d)) * ζ ^ (j * k)
      = (Q : ℂ) * ∑ d ∈ {d ∈ Finset.range Q | Q ∣ d + k}, K d := by
  classical
  have hstep : ∀ j ∈ Finset.range Q,
      (∑ d ∈ Finset.range Q, K d * ζ ^ (j * d)) * ζ ^ (j * k)
        = ∑ d ∈ Finset.range Q, K d * ζ ^ (j * (d + k)) := by
    intro j _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [mul_assoc, ← pow_add, mul_add]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  have hinner : ∀ d ∈ Finset.range Q,
      ∑ j ∈ Finset.range Q, K d * ζ ^ (j * (d + k))
        = if Q ∣ d + k then (Q : ℂ) * K d else 0 := by
    intro d _
    rw [← Finset.mul_sum, sum_pow_mul_index_eq hζ]
    by_cases h : Q ∣ d + k
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [Finset.sum_congr rfl hinner, Finset.mul_sum, Finset.sum_filter]

end RHTower.Sieve

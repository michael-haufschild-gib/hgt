# Cofactor eigenstates split over the translated zeros

- **ID:** adr-global-eigenstate-split
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For `0 < ε < 1/2`, a finite set `F` of exponents with `1/2 ≤ Re s < 1 − ε`, and
  `u = Σ_{s∈F} Σ_{k≤K} c_{s,k} log^k n · n^s`: the real and imaginary parts of `u` both satisfy the
  renormalized inversion law iff `c_{s,k} = 0` whenever `k ≥ ord_{s+ε} ζ`. The power-log eigenspace
  of `D̃` over `F` is the direct sum of the zero blocks; its dimension is `Σ_{s∈F} ord_{s+ε} ζ`.

## Paper proof
1. **Dilations act triangularly on blocks.** `D_p f(n) = f(⌊n/p⌋)` preserves admitted rows
   (pronic contraction `√(2/p)`), and `D_p(log^d n · n^s) = p^{-s}(log n − log p)^d n^s` modulo an
   admitted row: rounding `⌊n/p⌋` costs `(d + ‖s‖)(1 + log n)^d = O(n^{1/4})`, and for `n < p` only a
   bounded head remains. On coefficients `D_p` is `p^{-s}` times a unipotent upper-triangular matrix.
2. **Elimination.** `(D_p − p^{-s})^{K+1}` kills every block of exponent `s` and degree `≤ K`;
   `D_p − μ` with `μ ≠ p^{-s'}` is injective on blocks of exponent `s'` (downward induction).
3. **Separation by 2 and 3.** If `2^{-s} = 2^{-s'}` and `3^{-s} = 3^{-s'}` with `s ≠ s'`, then
   `(s − s')log 2 = 2πia`, `(s − s')log 3 = 2πib`, so `a log 3 = b log 2` and `3^a = 2^b`, impossible
   by parity.
4. **Independence.** For `s₀ ∈ F` apply the composition over `s ∈ F∖{s₀}` of
   `(D_{p_s} − p_s^{-s})^{K+1}` with separating `p_s ∈ {2, 3}`: every other block dies, the block of
   `s₀` is transformed injectively; if the full sum is admitted, the single-block lemma forces the
   transformed and hence the original coefficients of `s₀` to vanish.
5. Combine with the per-exponent symbol law and triangular Leibniz inversion
   (`power-log-eigenstates-of-the-cofactor-count-zeta-multiplicity`).

## Lean
`ArithmeticDefectRigidity/CofactorEigenstatesSplitOverTranslatedZeros.lean`:
`cAdmitted_dil_powerLogRow_sub`, `iterate_elimStep_kill`, `eq_zero_of_elimStep_eq_zero`,
`exists_separating_prime`, `coeff_eq_zero_of_cAdmitted_sum`,
`powerLogRows_global_renormalizedInversion_iff_order`. Standard axioms only.

## Insight
On every finite exponent window the index of the renormalized cofactor counts translated zeros with
multiplicity. The ADR exclusion target, restricted to power-log states, is exactly zero-freeness of
`Re s > 1/2 + ε`; nothing weaker and nothing stronger.

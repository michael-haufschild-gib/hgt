# The renormalized cofactor acts on power rows by ζ(s + ε)

- **ID:** adr-symbol-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For `0 < ε < 1`, `α = 1 − ε`, `0 < Re s < α`:
  `Σ_{j≤n} j^{-ε}⌊n/j⌋^s = ζ(s+ε) n^s + 𝓛_s n^α + O(n^{(Re s − ε)/2})`, with
  `𝓛_s = α⁻¹ Σ_m m^s (m^{-α} − (m+1)^{-α})` the absolute pole trace of the row. Hence on power rows
  `(I + D̃) Re(a n^s) = Re(a ζ(s+ε) n^s) + (bounded pronic energy)`: the symbol of the ADR
  renormalized cofactor is `ζ(s+ε) − 1`.

## Consequences
- **Eigenstate classification.** For `1/2 ≤ Re s < 1 − ε`, `a ≠ 0` (`Re a ≠ 0` if `s` real), the row
  `Re(a n^s)` satisfies the renormalized inversion law (`v + D̃v` admitted, i.e. `D̃v ≈ −v`) iff
  `ζ(s + ε) = 0`.
- **Real exponents are excluded** at every subcritical damping (`ζ < 0` on `(0,1)`): no real power
  profile is a cofactor eigenstate.
- The README's exclusion target "approximate eigenrelation `D̃u ≈ −u`" is, on power-like states,
  exactly the zero condition at the spectral exponent `s + ε`; impure sources with real zeros or
  zeros in `Re > 1/2 + ε` realize such states.

## Paper proof
Hyperbola at `q = ⌊√n⌋`, `r = √n` for `f(d) = d^{-ε}`, `g = δ_s(k) = k^s − (k−1)^s`
(`Σ_{k≤m}δ_s(k) = m^s`):
`S(n) = Σ_{d≤q} d^{-ε}⌊n/d⌋^s + Σ_{k≤q} δ_s(k)(F(⌊n/k⌋) − F(q))`, `F(N) = Σ_{d≤N} d^{-ε}`.
1. Head: `⌊n/d⌋^s = (n/d)^s + O(‖s‖q^{Re s−1})`, so head `= n^s P_{s+ε}(q) + O(q^{Re s − ε})`;
   `P_{s+ε}(q) = r^{α−s}/(α−s) + ζ(s+ε) + O(r^{-Re s−ε})`.
2. Long moduli: `F(⌊n/k⌋) = (n/k)^α/α + ζ(ε) + O(r^{-ε})`, `Σ_k‖δ_s(k)‖ = O(q^{Re s})`.
3. Abel: `Σ_{k≤q}δ_s(k)k^{-α} = Σ_{m≤q} m^s cell_m + q^s(q+1)^{-α}`; tail
   `Σ_{m>q} m^s cell_m = (α/(α−s))(q+1)^{s−α} + O(q^{Re s−α−1})` by the second-order estimate
   `g'(x) = αx^{-α-1}(x^s − m^s)` for `g(x) = m^s x^{-α} − (α/(α−s))x^{s−α}`.
4. The cross terms `n^{(1+s−ε)/2}` cancel exactly; the two cutoff differences
   `r^{2α}(r^{s−α} − (q+1)^{s−α})/(α−s)` and `(q^s/α) r^α (q+1)^{-α}(r^α − (q+1)^α)` are
   `O(r^{Re s − ε})`.
5. Classification: `Re(b n^s)`, `b ≠ 0`, `Re s ≥ 1/2` dominates `Σ Re(b n^{iγ})²/(2n)`, which grows like
   `(|b|²/4)H_T` (`γ ≠ 0`, bounded cross term `Σ n^{2iγ−1}`) or `(Re b)²H_T/2` (`γ = 0`).

## Lean
`formal/GaloisForLFunctions/ArithmeticDefectRigidity/TheRenormalizedCofactorActsOnPowerRowsByZeta.lean`:
`norm_powerRowCofactorSum_sub_le`, `exists_pronicNorm_powerRow_symbol_le`,
`powerRow_renormalizedInversion_bounded_iff`, `not_realPowerRow_renormalizedInversion_bounded`,
`not_exists_pronicNorm_powerRow_le`, `sum_mul_partialSum_div_eq_hyperbola`,
`norm_powerPoleSum_sub_partial_le`. Standard axioms only.

## Open
Transfer to actual escape: show an escaping cofactor limit is power-like on its moving support
(regular variation of `E_T` along the extraction), so its tied hull characters satisfy `ζ(s+ε)=0`.

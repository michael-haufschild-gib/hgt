# Every positive-power cyclotomic band retains the zero width

- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** Argon §3B; `ChebyshevCyclotomicTail`, `QuasiRHQuotientHeadAndFiniteContactAbscissaLaw`.
- **Statement:** For every δ>0, the infimum of energy exponents r≥1 of the actual Chebyshev near band at `K=ceil(N^δ)` is `2Θ`, where Θ is the actual zeta zero abscissa.

## Paper proof

Write `a_j=(ψ(j−1)−(j−1))/(j sqrt(j−1))` for j≥3, and zero for j≤2.
The unconditional error bound at Θ gives, for every η>0,
`Σ_{j≤N}|a_j| ≪η N^(Θ−1/2+η)`.
Indeed use the error estimate with η/2, bound `(j−1)^(Θ−1/2+η/2)` by its value at N,
and sum `1/j`; the logarithm costs the remaining η/2.

For a nontrivial Qth root ζ, the exact identity
`(1−ζ)P(ζ)=Σ_j a_j(1−ζ^j)` bounds its norm by twice that coefficient mass A.
Root spacing gives `|1−ζ_k|≥4 min(k,Q−k)/Q`, while `|1+ζ_k|≤2`.
Summing inverse squares outside K therefore gives
`Far(N,K)≤2(N+1)A²/K ≪η N^(2Θ+η)/K`.
At `K=ceil(N^δ)`, the far exponent is at most `2Θ−δ+η`.

The full nonnegative remainder and normalized Chebyshev energy have the same exponents ≥1,
whose infimum is `2Θ`. Suppose the near band has an upper exponent r≥1 below `2Θ`.
Take `0<η<δ`; the full remainder then has exponent
`max(r,2Θ−δ+η)<2Θ`, a contradiction. Conversely the near band is bounded by the full
remainder, which has every exponent `2Θ+η`. This proves the exact infimum and the equivalent
subpower criterion: for r≥1, `2Θ≤r` iff the near band has every exponent `r+η`.

Thus the five-sixths and three-quarters targets can use any fixed positive-power band,
not only cube-root and square-root bands. Mode count alone does not weaken the arithmetic
problem: every such band still carries the full zero-width exponent.

## Remaining arithmetic question

Prove an actual near-band upper estimate at `5/3+η` or `3/2+η`. The localization theorem
does not supply either estimate. Fixed finite bands and subpower-growing bands are not covered.

## Verification

- [x] Corpus search: existing far tail uses only the trivial coefficient envelope.
- [x] Dependency-closed paper proof above.
- [ ] Lean formalization of intrinsic tail, exact band exponent, and target-strip corollaries.
- [ ] Focused checks, standard-axiom audits, umbrella wiring.

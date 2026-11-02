# Prime–pole cancellation uniform over all Haar details

- **Stage:** 3-formalized
- **Type:** THEOREM; direct Lean and transitive axiom audits passed.
- **Parent:** SC arithmetic mixed-source control.

Let `R(Y,a,b)` be the literal full prime-window coupling minus both mixed
pole terms, divided by `√Y`. Set `m_a=haarMass(a)` and
`w_b=logCellWidth(b)`, the original squared Hilbert masses.
There is an absolute constant `C>0` such that, for all sufficiently
large natural `Y`, every

```text
M ≤ exp(√log Y/184320000),   X∈ℕ,
Σ_{a=1}^X m_a d_a² ≤ 1,     Σ_{b=1}^M w_b q_b² ≤ 1
```

satisfies

```text
|Σ_{b=1}^M q_b Σ_{a=1}^X d_a R(Y,a,b)|
  ≤ C exp(−√log Y/92160000).
```

There is no restriction on the detail horizon `X`. The same estimate
holds for the literal all-prime source at every common horizon `N`
with `X≤N` and `Y(M+1)≤N+1`. Coefficients are real.
The normalized prime matrix also approaches the rank-one matrix
`4(√(2b+2)−√(2b)) ∫haar_a(u)e^(−u/2)du` at the same rate.
The `√Y` normalization remains; this is not a complete Weil index bound.

## Paper argument

Support restricts the full trace to prime powers
`m≤2Y(b+1)e^(−u)`. Weighted Chebyshev gives
`0≤T_(Y,b)(u)/√Y≤4C₀√(2b+2)e^(−u/2)`.
The unsigned Haar contracting moment is at most `2m_a/√(2a)`.
Both signed pole moments satisfy the same bound, while the coarse
contracting moment has absolute value at most two. Consequently

```text
R(Y,a,b)² ≤ C₁(b+1)m_a/[a(a+1)].
```

Weighted Cauchy–Schwarz, `w_b≥1/(b+1)`, and the telescoping pronic tail give

```text
|Σ_{b=1}^M q_b Σ_{a=A+1}^X d_a R(Y,a,b)|²
  ≤ C₁(M+1)³/(A+1).
```

For the remaining rows, unit mass gives
`|d_a q_b|≤7(A+1)(M+1)`. The existing growing-packet theorem bounds their
sum by this coefficient bound times `C₂ exp(−√log Y/7680000)` whenever
`A≤exp(√log Y/23040000)` and `M≤A`.

Put `r=1/184320000`, `t=√log Y`, and `A=⌊exp(8rt)⌋`.
Natural `M≤exp(rt)` implies `M≤A`. The finite block is bounded by
`28C₂ exp(−15rt)`; the tail square is at most `8C₁ exp(−5rt)`.
Their sum is at most `(28C₂+8C₁+1)exp(−2rt)`.
Exact prime support identifies every admissible common-horizon source
with this same matrix remainder.

The remaining opposite pole factors as `(2/Y)H₊(d)Q₋(q)`.
The original unit masses give `|H₊|≤1` and `|Q₋|≤2(M+1)²`.
For the stated coarse range and `log Y≥1`, its absolute value is at most
`16exp(−2rt)`, proving the rank-one approximation.

## Formalization and scope

Main declarations in `ArithmeticIndexDescent/AllDetailPrimePoleCancellation.lean`:

- `exists_fullPrimeWindowRemainder_all_detail_growing_coarse_rate`.
- `exists_allPrimesMixedSource_all_detail_growing_coarse_rate`.
- `exists_fullPrimeWindowCoupling_all_detail_rank_one_rate`.

The support estimate is in `FullPrimeWindowTraceDecay`; unsigned Haar
integration in `FullPrimeWindowHaarDecay`; both-pole row estimates in
`FullPrimeWindowRowBounds`; weighted tails in `PrimeWindowRowTails`;
unit-coordinate estimates in `PrimeWindowUnitCoordinates`.
The original squared Hilbert mass identities are
`integral_haarSectionProfile_sq` and `inner_coarseAtom`.

All six modules pass individual direct Lean checks. Their displayed
transitive axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. The umbrella imports all six modules.

Corpus novelty audit found fixed-family and growing-square cancellation,
plus Gamma-norm cancellation retaining an aperture factor. The all-detail
operator estimate in the original cell masses was not found.
External priority is unchecked. The retained `√Y` normalization leaves
complete-source positivity and the finite-index ceiling open.

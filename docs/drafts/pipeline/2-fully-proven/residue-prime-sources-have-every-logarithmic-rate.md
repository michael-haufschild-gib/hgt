# Residue-prime sources have every logarithmic rate

- **ID:** residue-prime-sources-have-every-logarithmic-rate
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Parent:** fixed-conductor-packets-remain-positive-at-growing-overlap

## Statement

For every fixed positive modulus `q` and natural `k`, there is `Y₀`
such that, for every `X≥Y≥Y₀` and every real residue pattern `F`,

`|Σ_(n≤X) F(n mod q)Λ(n) − κ_F X|
 ≤ X/(log Y)^k · Σ_(r mod q)|F(r)|`,

where `κ_F=ϕ(q)⁻¹Σ_(r unit)F(r)`. Every prime power is retained.

## Proof [PROVED HERE]

The existing quantitative progression theorem gives, uniformly over the
finitely many reduced classes, an error
`C X exp(-a(log X)^(1/10))`, with `a>0`. A non-unit class contains only
primes dividing `q`, so its prime sum is bounded by `θ(q)` and has zero
main term. In every class the omitted proper prime powers have total
weight at most `ψ(X)-θ(X)≤2√X log X`. This is bounded by the same
power-log exponential envelope beyond a common horizon. The constant
`θ(q)` is absorbed there as well. Thus one such envelope controls all
residue indicators, with their correct unit or non-unit main term.

For each fixed `k`,
`C(log Y)^k exp(-a(log Y)^(1/10))→0`. The exponential envelope is
decreasing in `X` once `X>1`; hence every indicator error is at most
`X/(log Y)^k` for all `X≥Y` beyond one horizon. Expand `F` in the
finite residue-indicator basis and apply the triangle inequality.

## Lean status

Formalization follows directly. This is supporting quantitative source
transfer, not a separately counted contribution.

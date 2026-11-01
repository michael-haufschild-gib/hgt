# Literal stabilizer model as finite logarithmic rows

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** Argon §4.1.
- **Parent:** [Global model transport](../1-in-progress/odd-stabilizer-finite-aperture-transport.md).
- **Lean:** `TransThresholdPairCorrelation/StabilizerModelRowDecomposition.lean`.

## Statements

Put `N=floor X` and
`R_m=(min(N,floor(m exp θ))−m)/2`, with natural subtraction and division.

The literal model satisfies the exact identity

`model=(1/(4π))Σ_{odd 3≤m≤N}[2g(log m)logRow(m,R_m)+taperVariation(m,R_m)]`

for arbitrary Q, Ω, g, X and θ
(`stabilizerModelOddCoalSum_eq_logarithmic_rows`). Every endpoint and the
literal scalar 1/4 are retained. If `θ≤log 2`, then `2R_m≤m`
(`two_mul_stabilizerApertureLength_le`).

For each fixed smooth height profile, a constant C≥0 bounds the actual
standard taper's global endpoint error by

`|model−(1/(2π))Σ_{odd 3≤m≤N}g(log m)logRow(m,R_m)|≤C N O(Q)/T`

for T≥1 and θ≤log 2, uniformly in admissible taper length, collar and
monotone transition profile (`WindowProfile.exists_model_taper_transport_le`).
Here `O(Q)=Σ_{q≤Q,odd}μ²(q)/φ(q)`.

## Proof

The cosine transform, lag weight and square-root denominator are symmetric
in the two endpoints. Grouping the distinct ordered pairs leaves one upper
triangle with taper factor `g(log m)+g(log n)`. For m<n,
`|log n−log m|≤θ` is equivalent to `n≤floor(m exp θ)`.
Odd parity gives the unique parametrization `n=m+2(r+1)`, with `r<R_m`.
The identity `g(log m)+g(log n)=2g(log m)+(g(log n)−g(log m))`
then yields the stated row decomposition.

For θ≤log 2, `m exp θ≤2m`, hence `2R_m≤m`. The proved local taper
variation bound applies at every retained base; summing at most N bases
and using `1/(4π)≤1` gives the global estimate.

## Scope

This identifies the literal source with the local row estimates, including
empty rows. Removing the remaining aperture, controlling its short-base and
upper-boundary regions, and evaluating the primitive spatial correction still
require separate bounds. Actual prime discrepancy remains open.

All three transitive axiom audits use only `propext`, `Classical.choice` and
`Quot.sound`; the final direct leaf check passes.

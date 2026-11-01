# Uniform coprime-harmonic error averaged over conductors

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Route:** Argon §4.1.
- **Parent:** [Literal model calibration](parity-stabilizer-logarithmic-coalescent-calibration.md).

## Target

Let `A(q)=μ²(q)/φ(q)²` and `H_q(N)=Σ_{n≤N,(n,q)=1}1/n`.
For every Q and every choice of positive integer horizons N(q), prove

`Σ_{q≤Q} q A(q)|H_q(N(q))−(φ(q)/q)log N(q)|≤36864(1+log Q)`.

This also bounds the odd-conductor sum. Uniformity permits
`N(q)=floor(qt/π)` throughout the height window. It would make the
coprime-harmonic contribution `O(T log²T)`, below the proposed model main
term `T log³T`.

## Proof mechanism

Möbius decomposition and floor-harmonic bounds give, for N≥1,

`|H_q(N)−(φ(q)/q)log N|≤Σ_{d|q}(1+log d)/d`.

The existing `sum_totientRatio_sq_div_le` bounds `Σ_{q≤Q}qA(q)` by
`64(1+log Q)`. Dirichlet-weight partial summation at exponent 1/2 then
gives `Σ A(q)sqrt(q)≤192`; the inequality `1+log q≤3sqrt(q)` gives
`Σ A(q)(1+log q)≤576`.

Finally `A(dk)≤A(d)A(k)`: a squarefree product has coprime factors,
and otherwise the left side vanishes. Divisor swapping bounds the averaged
error by `576·64(1+log Q)`.

## Status

The three new statements—uniform individual error, summable logarithmic
moment and averaged error—await Lean verification. The first arithmetic
moment reuses the existing corpus theorem; no duplicate public theorem is
needed. Global model calibration and actual prime discrepancy remain open.

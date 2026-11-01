# Stabilizer normalization on arbitrary intervals and actual prime rectangles

- **Stage:** 3-formalized
- **Parent:** [Exact period normalization](../3-formalized/stabilizer-odd-pair-normalization-audit.md).
- **Route:** Argon §4.1.

## Finite estimates

Write `W_Q(h)=2 Σ_{q≤Q, q odd} μ(q)² c_q(h)/φ(q)²`. For every `Q≥1` and
interval length M, the full odd-coordinate rectangle satisfies

`0≤Σ_{i,j<M} W_Q(|(2i+1)−(2j+1)|)−2M²≤2Q³`.

Also `|Σ_{n<M}W_Q(n)−2M|≤2Q²` and `0≤W_Q(0)≤2Q`.
Removing coordinate one and repeated pairs leaves mass D with

`|D−2M²|≤2Q³+4Q²+4M+2(M+2)Q`.

Consequently, at M=Q², its full-rectangle scalar mean obeys
`|Mean(Q,Q²,β)−β/2|≤4|β|/Q`. Both cutoff and interval grow, without a
common-period condition.

## Actual prime comparison

Let `P(X)=Σ_{p,q<X, p,q odd primes, p≠q} log p log q`. Then `P(X)/X²→1`.
At `Q=n+1`, `M=Q²`, and `X=2M`, the normalized actual-prime-minus-model
discrepancy tends to `1−β/2`. Scalar 1/4 therefore leaves limit 7/8.
Scalar two uniquely gives limit zero.

## Proof

For q>1, complete-period mean zero and `|c_q(n)|≤φ(q)` bound every shifted
prefix by `qφ(q)`. The period-square identity gives nonnegative pair mass
at most `q²φ(q)²`; the packet coefficient cancels both totients. Summing at
most Q conductors gives the rectangle error. The same prefix bound gives the
row estimate, and the exact row/column/diagonal deletion identity gives D.

The prime rectangle is the square of the odd-prime logarithmic sum minus its
diagonal. PNT gives the first term's normalized limit one; the diagonal is at
most `log X · Σ_{p<X}log p`, hence has normalized limit zero. Combining this
with the explicit packet estimate gives the discrepancy limit and uniqueness.

## Scope

These are raw full-rectangle arithmetic weights before inserting an aperture,
`1/sqrt(nm)`, or a signed Fourier kernel. The signed coalescent discrepancy
estimate remains open. Raw centering alone is insufficient, as the independent
Frullani phase-resonance theorem shows.

## Lean

- `TransThresholdPairCorrelation/StabilizerIncompletePeriods.lean`: six public theorems.
- `TransThresholdPairCorrelation/StabilizerPrimeRectangleDiscrepancy.lean`: five public theorems.

Both leaves pass final direct source checks and are wired. Together with the
eight complete-period and deletion theorems, all nineteen transitive axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

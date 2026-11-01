# Stabilizer normalization outside complete periods

- **Stage:** 1-in-progress
- **Parent:** [Exact period normalization](../3-formalized/stabilizer-odd-pair-normalization-audit.md).

## Targets

For every `Q≥1` and interval length `M`, prove
`0≤Σ_{i,j<M} W_Q(|(2i+1)−(2j+1)|)−2M²≤2Q³`.
Also prove `|Σ_{n<M}W_Q(n)−2M|≤2Q²` and `0≤W_Q(0)≤2Q`.
The exact row/column/diagonal deletion identity then controls the distinct odd
rectangle with error at most `2Q³+4Q²+4M+2(M+2)Q`.

This would retain scalar mean β/2 whenever `Q³=o(M²)`, without factorial periods.
The actual distinct odd-prime logarithmic rectangle has candidate mean one:
PNT gives its full square mass, and its diagonal costs at most
`log X · Σ_{p<X} log p`. Thus the scalar 1/4 would leave raw mean discrepancy 7/8;
scalar 2 would remove it. No signed-aperture conclusion follows.

## Proof mechanism to formalize

For `q>1`, complete-period mean zero and `|c_q(n)|≤φ(q)` give every shifted
prefix bound `qφ(q)`. The existing period-square identity gives nonnegative pair
mass at most `q²φ(q)²`; the packet coefficient cancels both totients. Summing over
at most Q conductors gives `2Q³`. The same prefix bound gives the row estimate.
All ingredients are in the corpus; no matching incomplete-period normalization
or actual-prime rectangle comparison was found.

## Status

`StabilizerIncompletePeriods.lean` proves the four finite estimates and the
square-scale bound `|Mean(Q,Q²,β)−β/2|≤4|β|/Q`. Its square-scale limit is also
proved; the leaf compiles and is wired. Transitive axiom audits and final direct
source check remain. Actual prime comparison is drafted and under Lean checking.

# Decreasing-weight Möbius–divisor producer obstruction

- **Status:** DW1 false in Lean; its general smoothing mechanism is retired.
- **Scope:** this retires a proposed producer, not SD1 or the CCM-FU RH route.
- **Original chain:** complete divisor source -> monotone-kernel diagonal dominance ->
  half-order source estimate -> strict-right continuation -> RH. The second arrow fails.

DW1 asserts `(sum_d C_d(w))²<=sum_d C_d(w)²` for every nonnegative decreasing time sequence,
where `C_d(w)=mu(d)sum_(k=d)^(M-1)w_k D(floor(k/d))` and
`D(q)=log(q!)-sum tau+2 gamma q` is the actual arithmetic source.

## Exact obstruction and positive survivor

At M=7, flat weights violate DW1. The complete symbolic finite-source calculation is closed
in Lean using analytic bounds on logarithms and Euler's constant. Continuity also gives an
unconditional positive strictly decreasing geometric counterexample. No numerical result is
a premise. This is not a claim that all geometric kernels fail.

The strongest audited surviving structural statement is the exact all-scale prefix law

`C_d(M,w)=sum_(t=1)^(M-1)C_d(t+1,1)*(w_t-w_(t+1))+C_d(M,1)*w_M`.

Its paper proof is finite Abel summation; its Lean proof is closed. The half-order specialization
is formally identified with the existing arithmetic dilation channel. This representation
preserves the mixed terms; it supplies no sign. It is not claimed as a new general Abel theorem.

Formal module:
[MobiusDivisorMonotoneWeightObstruction.lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorMonotoneWeightObstruction.lean).
Source check, named-leaf audit, umbrella wiring, and four-theorem axiom audit pass.

## Independent producer tests

PH1 requires every mixed pairing of the half-order source with a flat prefix to be nonnegative.
It fails numerically at M=17,t=6. GH1 instead requires every mixed geometric pairing to be
nonnegative. It passes the initial grid through M=512, but fails at M=1802,q=1/1000000 and
several larger scales. Both explicit witnesses are independently checked at60/100 digits.
These numerical counterexamples are not Lean certificates; no formal closure claim is made
for PH1 or GH1. Neither is substituted for DW1 or SD1 after failure.

The [report](../2-fully-proven/computations/mobius-divisor-decreasing-weights-2026-09-06/REPORT.md)
contains protocols, full results, analytic proof outline, and limitations. The actual half-order
SD1 sign and the explicit continuation bridge absorbing the harmonic diagonal loss remain open.

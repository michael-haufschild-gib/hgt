# Plancherel mass of the logarithmic divisor jet

- **ID:** SSH-DIVISOR-JET-PLANCHEREL
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Q1/O1, conductor costs in periodic shell cancellation.

## Statement

For `m≥1`, write `j_m=(J_m−Λ(m))/√φ(m)`. The exact complete-period mass is

`(1/m)Σ_(0≤n<m) j_m(n)²`
`= log²m + (Σ_(d|m)Λ(d)²φ(m/d)−Λ(m)²)/φ(m)`.

In particular this is at most `2 log²m`, and
`Σ_(0≤n<m)|j_m(n)|≤2m log m`. The normalized Ramanujan mode itself has
period mass `1`, hence period absolute mass at most `m`.

## Paper proof

The conductor expansion of the divisor jet is
`J_m=log(m)c_m+Σ_(d|m)Λ(d)c_(m/d)`.
Every occurring conductor divides `m`. Complete-period Ramanujan
orthogonality therefore removes all mixed terms. The diagonal cross term
at `d=1` is zero because `Λ(1)=0`. Removing the constant conductor subtracts
exactly `Λ(m)²` from the normalized period mass.

Evaluating the conductor expansion at a multiple of `m`, and using the
logarithmic totient identity, gives
`Σ_(d|m)Λ(d)φ(m/d)=φ(m)tameDifferent(m)`.
For `d|m`, `Λ(d)²≤log(m)Λ(d)`, so the quadratic divisor sum is at most
`φ(m)log(m)tameDifferent(m)≤φ(m)log²(m)`.
Discard the nonnegative mean square to obtain the mass bound.
Cauchy–Schwarz on the complete period gives the absolute-mass bounds.

## Scope and gates

This is an exact Plancherel identity for the downward divisor source.
It can replace its pointwise amplitude by complete-period mass in Abel
summation. The full agreement-shell decomposition remains open.

- [x] Corpus supplies complete-period orthogonality at every common multiple.
- [x] Divisor-jet conductor expansion and amplitude audit complete.
- [x] Exact mass, logarithmic bound, and period absolute mass formalized.
- [x] Final direct and transitive axiom audits; umbrella import.

## Lean declarations

Module: `SuccessorShellArithmetic/TopBand/RamanujanDivisorPlancherel.lean`.

- `sum_range_ramanujan_packet_sq`: exact Plancherel on any common period.
- `sum_range_ramanujanLogDivisorJet_sq`: full divisor-jet quadratic mass.
- `periodMean_centeredRamanujanJet_sq`: exact normalized variance.
- `periodMean_centeredRamanujanJet_sq_le`: logarithmic quadratic bound.
- `sum_range_abs_centeredRamanujanJet_le`: period absolute mass at most `2m log m`.
- `sum_range_abs_normalizedRamanujanMode_le`: normalized-mode period absolute mass at most `m`.

Final `lake --old env lean` check passed. All audited transitive dependencies
use only `propext`, `Classical.choice`, and `Quot.sound`.

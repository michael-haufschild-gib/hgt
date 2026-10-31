# The divisor jet lowers conductor with positive coefficients

- **ID:** SSH-DIVISOR-JET-CONDUCTOR-EXPANSION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Q1/O1, exact Ramanujan decomposition of the downward shell source.

## Statement

For `m≥1` and every `n≥0`, the logarithmic divisor jet has
the finite conductor expansion

`J_m(n)=log(m)c_m(n)+Σ_(d|m)Λ(d)c_(m/d)(n)`.

Every coefficient is nonnegative. Its constant coefficient is `Λ(m)`;
the centered jet uses only nonpolar conductors dividing `m`. Consequently

`|J_m(n)−Λ(m)|≤φ(m)[log m+tameDifferent(m)]−Λ(m)`

for `m≥1`, with equality at every multiple of `m`. The normalized
centered jet therefore has an exact sup norm, bounded by `2√φ(m) log m`.

## Paper proof

The Ramanujan divisor identity is `Σ_(k|d)c_k(n)=d·1_(d|n)`.
Insert it in
`J_m(n)=Σ_(d|m)μ(m/d)log(d)d·1_(d|n)` and exchange the finite sums.
The coefficient of `c_k(n)`, for `k|m`, is

`Σ_(e|m/k)μ((m/k)/e)log(ke)`.

For `k=m` this is `log m`; otherwise the constant `log k` vanishes
under the Möbius sum and the remaining sum is `Λ(m/k)`. This gives
the expansion, including `m=1`, where both sides vanish.

Remove the `k=1` term. Each remaining Ramanujan sum has absolute value
at most `φ(k)`, attained simultaneously when `m|n`. The value there is
`φ(m)[log m+tameDifferent(m)]−Λ(m)` by the existing logarithmic
totient identity. Finally `tameDifferent(m)≤log m` and `Λ(m)≥0` give
the stated normalized bound.

## Scope and gates

This is the exact finite spectral decomposition of the divisor jet.
It does not yet decompose the complete shell form or pay its horizon edge.

- [x] Corpus search found the divisor jet, its mean, and its value at a conductor multiple.
- [x] The corpus logarithmic Leibniz rule and `Λ*μ=−μ·log` give the expansion directly.
- [x] Expansion, sharp amplitude, and normalized bound formalized.
- [x] Final direct Lean check, transitive axiom audits, and umbrella import.

## Lean declarations

Module: `SuccessorShellArithmetic/TopBand/RamanujanDivisorSpectrum.lean`.

- `ramanujanLogDivisorJet_eq_conductor_sum`: exact expansion, including conductor zero.
- `ramanujanLogDivisorJet_sub_mean_eq`: removal of the constant conductor.
- `abs_ramanujanLogDivisorJet_sub_mean_le`: sharp absolute envelope.
- `abs_ramanujanLogDivisorJet_sub_mean_of_dvd`: attainment at every multiple.
- `abs_centeredRamanujanJet_le_logarithmic`: normalized logarithmic envelope.

Final `lake --old env lean` check passed. All audited transitive dependencies
use only `propext`, `Classical.choice`, and `Quot.sound`.

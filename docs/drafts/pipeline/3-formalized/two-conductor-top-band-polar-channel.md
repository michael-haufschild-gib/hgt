# The polar channel on two-conductor top-band packets

- **ID:** SSH-TWO-CONDUCTOR-POLAR-CHANNEL
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean checked)
- **Source:** `docs/reports/review-3010/obstacles-summary.md` Q1/O1.

## Statement

Fix a `C²` atom profile supported in `[0,1]`, with positive quadratic mass.
Write `a_m=c_m/√φ(m)`, `U_m=√φ(m)`, and
`V_m=(Σ_(d|m)|μ(m/d)d log d|+Λ(m))/√φ(m)`.
For `m≥2`, put `a=α+βa_m`. The literal joint top-band coefficient satisfies

`|J(a,a)−α²J(1,1)|`
`≤Kφ m[|αβ|(2U_m+V_m)+β²φ(m)]G(1+log N)`

uniformly for `N≥8`, `1≤c≤N/4`, and real `α,β`.

## Paper proof

The finite Mangoldt convolution, shell row, and both polar moments are
linear in their coefficient functions. Consequently

`J(a,a)−α²J(1,1)=αβ[J(1,a_m)+J(a_m,1)]+β²J(a_m,a_m)`.

The periodic-partner theorem bounds the first and third coefficients by
`Kφ mU_m G(1+log N)` and `Kφ mφ(m)G(1+log N)`.
The [mixed Ramanujan–polar theorem](mixed-ramanujan-polar-top-band-cancellation.md) bounds the second by
`Kφ m(U_m+V_m)G(1+log N)`. Take the larger profile constant and apply
the triangle inequality. The exact quadratic witness identity then
identifies this coefficient in `2 Pole−NR`.

## Scope and gates

Only the polar–polar entry remains outside the overlap-independent bound.
The full agreement-shell sum-of-squares decomposition remains open.

- [x] Corpus search: `jointTopCoefficient`; no packet expansion found.
- [x] Mixed Ramanujan–polar input passed its final direct and transitive axiom audits.
- [x] Bilinear expansion and packet bound formalized and directly audited.
- [x] Umbrella and foundational README updated.

`TopBand.RamanujanPackets` proves `jointTopCoefficient_two_mode` and
`exists_abs_ramanujan_packet_sub_polar_le`. Its direct check exits zero
without diagnostics; both transitive axiom sets are exactly
`propext`, `Classical.choice`, `Quot.sound`.

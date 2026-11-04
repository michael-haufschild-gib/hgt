# Quartic cross-load profile: global pointwise positivity fails

- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Wall:** Σ6
- **Refuted claim:** `P(r)=(1−r²/2)²` makes the complete fifth even source
  positive definite for every nonnegative center.

For `F=thetaCuspFullSource` and `G=3F²+2xFF'`, the correction is
`G_P=(1−2x²)²G−8x²(1−2x²)F²`. At `x=log(32/π)/2`, both
`nativeShiftedMatrix 5 0 x+G_P(x)B` and its literal weighted source fail PSD
for every `0<a<1/2`, where `B=crossLoad paidSevenSchur`.
The proof retains every theta atom and the exact aperture remainder.
Killing theorems: `ThirtyTwoCrossObstruction.repair_not_posSemidef` and
`weightedRepair_not_posSemidef` in `FifthEvenPolynomialCrossObstruction.lean`.

**Positive survivor.** At the same center, scalar loads are PD exactly for
`t<τ`, PSD exactly for `t≤τ`, with a singular endpoint and `0<τ<27/35`.
For each critical aperture, the exact capacity is `τ(a)=τ/α(a)`, with
`67/70≤α(a)≤1`, hence `τ≤τ(a)≤70τ/67<54/67`.

**New insight.** Aperture dependence rescales this exact load interval and
increases capacity by at most `70/67`; it cannot restore unit-load positivity.
The obstruction concerns pointwise source positivity and does not refute the
integrated rank-nine matrix.

**Paper and Lean status.** The [capacity proof](../3-formalized/theta-cusp-polynomial-profile-scale-thirty-two.md)
is dependency-closed and formalized, including both capacity classifications,
singular boundaries, and uniform gain bound. Canonical checks and 33-declaration
transitive axiom audit passed; only standard Lean axioms occur.

Earlier [positive regions](../3-formalized/theta-cusp-polynomial-cross-load-positive-regions.md)
(origin and scale-eight neighborhoods, cofinal ray) and
[explicit interval](../3-formalized/theta-cusp-polynomial-cross-load-positive-interval.md)
(`x≥0`, `1/2≤x²`, `x≤3/4`) remain valid. The zero-flux identity preserves
all fifth even mixed entries, with index `2(i+j)`. Global rank-nine positivity
remains open; Σ6 remains partially solved.

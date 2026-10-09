# Bounded probe families cannot certify the whole potential domain

Status: RETIRED — obstruction and strongest positive survivor formalized.

## Rejected route

Replace cofinal integer-log sampling by a bounded family while retaining a
universal whole-line convergence conclusion from individual eventual probe
lower bounds. This fails even for arithmetic minorants with zero excess.

## Obstruction

For log(m_j)<=B, use the closed reciprocal-kernel domain of radius max(B,0).
Its negative coefficient lift has finite potential at every sampled shift and
at the origin, hence exact finite actual-probe limits and eventual lower bounds.
An integer-log shift beyond that radius has a divergent potential and an
actual probe tending to minus infinity.

Formal theorem:
`RHTower.bounded_logShift_family_misses_minorant_divergence` in
`formal/GaloisForLFunctions/RHTower/WeilLogShiftArithmeticDomain.lean`.

## Strongest positive survivor

Cofinality is exactly the universal sampling condition in the zero-excess
class, proved by `RHTower.cofinal_iff_zero_excess_probe_sampling`.
Every finite open or closed symmetric potential domain is also realizable by
both a zero-excess arithmetic minorant and a zero-deficit majorant, including
the empty domain and singleton origin. The coefficient lift preserves the
entire domain despite its two forced zero coordinates.

Paper proof: dependency-closed, using only our Lean corpus.
Lean status: all ten public theorems and the coefficient definition compile;
all eleven axiom audits contain only `[propext, Classical.choice, Quot.sound]`.
Umbrella and API are wired. Global lint reports seven unrelated unwired modules;
full verification details are recorded on the survivor card:
`../3-formalized/weil-logshift-arithmetic-domains.md`.

Second-pass audit: the obstruction exposes an exact sampling classification
and arbitrary finite arithmetic convergence radii, not only a negative example.
Both are formalized. No external novelty or RH proof claim.

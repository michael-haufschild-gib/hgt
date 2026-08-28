# HB canonical two-branch left-action covariance no-go

Status: failed/retired
Route: HB
Date: 2026-08-28

## Retired proposal

Treat failure of canonical two-branch FE--Schwarz covariance as evidence that the constructed
Peierls action lacks correct source incidence, then seek a different propagator or left-coordinate
normalization.

## Exact obstruction

HC22 proves this diagnosis false. The existing target-independent global Peierls propagator has
exact canonical left-coordinate BM incidence on every Xi fibre, including every tilted fibre.
For every nonzero amplitude, canonical regular/complementary left-source covariance holds exactly
when `Re(q)=1/2`. Universal unit covariance is equivalent to RH.

Thus changing propagator or dual normalization cannot repair the canonical two-branch covariance
gap while preserving the literal incidence data. Incidence is not the obstruction; covariance is
the RH endpoint itself.

## Strongest positive survivor

At every tilted fibre Lean proves all three statements simultaneously:

- exact canonical left-source Peierls incidence;
- failure of canonical two-branch FE covariance;
- strict positivity of canonical FE--Schwarz orbit optical power.

This is formalized as
`hbXiPeierlsCanonicalLeftAction_tilted_incidence_noCovariance_positiveOptical` in
`ThetaCuspHawkingBMCanonicalLeftActionCovarianceEndpoint.lean`.

The dependency-closed replacement is four-sector FE--Schwarz orbit dynamics: HC16 constructs its
global Peierls trace, HC17 gives the fixed-weight Ward dichotomy, HC18 gives the canonical optical
transgression, and HC22 shows why individual two-branch covariance cannot replace that orbit
landing off wall.

## Lean status

Positive survivor and exact global classification are fully formalized, target-built, and
axiom-audited. No `sorry`, `admit`, added `axiom`, `opaque`, or `unsafe` declaration occurs.

## Route decision

Retire attempts to fix canonical two-branch covariance by rebuilding already valid action
incidence. Continue only with an independent covariance law or a four-sector coercive invariant.

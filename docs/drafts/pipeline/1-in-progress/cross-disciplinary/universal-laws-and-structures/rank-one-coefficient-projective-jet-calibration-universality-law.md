# Rank-one coefficient projective-jet calibration universality law

## Status

In progress — paper proof and Lean source complete; exact check and literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/RankOneDifferenceBoundaryTomography.lean`
  - `rankOneCoefficientPairedBoundaryCurrent_eq_outerProduct`
  - `rankOneCoefficientIncomingCovector_single`
- `HTGeometry/SharedClockRankOneRigidity.lean`
  - `sharedClockObservation_factorization_unique_up_to_scale`

## Universal law

At every finite scalar-difference clock level, suppose one visible positive coefficient derivative
is nonzero. Any factorization of the oriented paired boundary current into a source functional and
an outgoing response has one unique nonzero calibration scalar. The source functional is that
scalar times the canonical incoming covector, the response is the reciprocal scalar times the
universal Gamma factorial-tail vector, and every coordinate probe reads the corresponding positive
coefficient derivative with the same calibration.

Thus unknown rank-one separation loses no relative positive-jet information: its complete
ambiguity is one global scalar shared by every visible derivative and every outgoing coordinate.

## Paper proof

The paired-current outer-product theorem identifies the canonical factors. A nonzero coefficient
coordinate gives a nonzero incoming probe because its binomial multiplier is nonzero; the last
Gamma boundary coordinate is also nonzero. General shared-clock factorization rigidity then gives
one unique reciprocal scalar pair. Evaluating its source equality on each `Pi.single` probe and
using the incoming-covector coordinate formula recovers the whole visible positive coefficient
jet with that scalar.

## Lean status

Source complete in
`formal/GaloisForLFunctions/HTGeometry/RankOneCoefficientProjectiveJetCalibrationUniversalityLaw.lean`.

Direct source check is deferred to final audit because both provenance modules currently lack
cached `.olean` artifacts; no early `lake build` was run.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.

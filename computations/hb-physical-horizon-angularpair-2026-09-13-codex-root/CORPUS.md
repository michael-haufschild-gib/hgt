# Current-corpus basis

Fresh corpus search and direct source inspection used:

- `ThetaCuspHawkingBMPhysicalLiftHorizonCurrent.lean`: exact current/contact cancellation, horizon value, finite integrals, and `angular_pair_original`.
- `ThetaCuspHawkingBMFullAngularMasterCurrent.lean`: `physicalRate`, full covectors, and full angular master current.
- `ThetaCuspHawkingBMQuadraticMixedSource.lean`: exact square and gradient covector formulas.
- `ThetaCuspHawkingBMSquareSourceDifferential.lean`: half-square, gradient-energy, and coexact differential identities.
- `ThetaCuspHawkingBMEisensteinCuspFinitePartSpecializationNoGo.lean`: pointwise post-specialization cannot recover a general analytic-family cusp finite part.
- `ThetaCuspHawkingBMEisensteinScalarLandingNoGo.lean`: balanced landing contains both scalar canonical landing and complete cusp finite-part residual; the direct zero-cusp-finite-part route kills the canonical vertex.
- `rh-current-frontier-map.md`: complete temporal/metric/QNM matching, all-face flux assembly, top subtraction, and fixed-clock extinction remain open obligations.

The implemented formula is copied from these definitions, not inferred from background knowledge.  Corpus search coverage reported 57,829 files inventoried with no pending files; applicability was verified by direct source inspection because semantic compiler coverage was incomplete.

# Card 4 — DONE, promoted to 3-formalized on 2026-08-14

`nonautonomous-isogeny-tail-time-splitting` is in `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ht/`
with certificate `nonautonomous-isogeny-tail-time-splitting-formalized.md`.

## What closed the gate (the complex-torus column, every dimension)

Over `ℂ` every connected commutative algebraic group is `ℂ^n / Λ` as a complex Lie group, so one
analytic stack over `ℂ^n` settles the abelian-variety side in all dimensions.  Two structural
changes vs the one-variable elliptic column:

1. **Carrier**: the codiscrete-germ field does NOT generalise (polar sets are hypersurfaces for
   `n ≥ 2`).  Use the FRACTION FIELD OF THE ENTIRE FUNCTIONS — needs no Cousin/Oka.
2. **Deck input**: "arbitrarily small periods" is useless for `n ≥ 2` (the period group of a
   nonconstant several-variable function need not be discrete: `f(z₁,z₂)=z₁`).  Use DENSITY of the
   accumulated division points, from a cocompact period lattice.

## Modules (all wired into `GaloisForLFunctions.HTGeometry`, all axiom-clean)

- `EntireFunctionField`, `EntireDirectionalDerivation`, `EntireTranslation`, `EntireDenseInvariant`
- `GeneralCoefficientDerivation`, `MultiReparametrization`, `MultiReparametrizationAutomorphism`,
  `ComplexTorusTail`
- `ComplexLatticeDensity` — `PeriodLattice`, `dense_divisionPoints`, `stdPeriodLattice`
- `ComplexTorusVelocityTail` — `TorusField n`, `complexTorusVelocityField`,
  `torusDeckInvariantField_eq_torusVelocityField` (6), `differentialIndependent_torusVelocity` (7a),
  `eq_constEntire_of_algebraMap_mem_torusVelocityField` (7b)
- `ComplexTorusIsogenyDeck` — `exists_mem_torusSubfield_fieldScaleEquiv_iff` (1)
- `ComplexTorusMaurerCartan` — `deriv_coordEntire` (the Lie algebra in coordinates),
  `deriv_fieldScaleEquiv_coordEntire` + `bijective_velocity_transport` (5), `stdTorus_phase_tail`
- `ComplexTorusPositionVelocity` — `torusDeckFixedField_eq_torusBaseAdjoinJets` (2), no hypothesis

## Naming trap

`torusVelocityField` was ALREADY TAKEN by `HTGeometry/TorusVelocityField.lean` (the `G_m^r` column).
Mine is `complexTorusVelocityField`.  Always build the umbrella (`lake build
GaloisForLFunctions.HTGeometry`) after adding modules — leaf builds do not catch name clashes.

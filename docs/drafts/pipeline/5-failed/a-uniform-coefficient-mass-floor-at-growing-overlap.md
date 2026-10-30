# A uniform coefficient-mass floor at growing overlap

- **ID:** a-uniform-coefficient-mass-floor-at-growing-overlap
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement rejected:** Along a divergent overlap schedule, one fixed positive constant
  bounds actual synthesized squared mass below by coefficient mass times one atom's mass.

## Obstruction

The adjacent coefficient vector `(+1,-1)` has coefficient squared mass two, while its
atom-normalized synthesized mass is `1-Cφ(t)/Cφ(0)` with `t→0`. The ratio tends to zero.
For `c≥2`, it is explicitly at most `4·8000²/(c²∫φ²)`.

## Positive survivor and exact insight

Every finite plateau overlap Gram remains positive definite at every positive width.
The least nonzero coefficient can be isolated just after its logarithmic center, giving
a nonzero test and positive squared mass. The obstruction concerns uniform comparison
across horizons and widths, not finite nondegeneracy.

The exact autocorrelation deficit and its quantitative upper bound describe how this
comparison fails. Consequently a constant coefficient-mass comparison cannot replace the
actual overlap Gram throughout a growing schedule. These statements make no sign assertion
about the complete Weil form.

## Proof status

Dependency-closed paper arguments and exact Lean statements are complete:

- `TransMetzlerWeilPositivity.plateau_overlap_gram_strictly_positive`
  in `ThePlateauOverlapGramIsNondegenerate.lean`;
- `TransMetzlerWeilPositivity.plateauAdjacentMassRatio_eq`,
  `plateauAdjacentMassRatio_le_inv_sq`, and `no_uniform_plateau_atomic_mass_floor`
  in `GrowingOverlapHasNoUniformGramFloor.lean`.

Both leaves passed direct checks and all transitive axiom audits with default limits.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. Both umbrella imports are wired.

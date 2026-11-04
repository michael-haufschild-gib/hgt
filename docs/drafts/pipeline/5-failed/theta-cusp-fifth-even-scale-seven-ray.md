# Fifth cross-load from scale seven

- **Stage:** 5-failed
- **Wall:** Σ6
- **Refuted claim:** The fixed coefficient `paidSevenSchur` makes the complete
  cross-loaded source positive definite for every `q≥7`.

At `x₈=½log(8/π)` the complete matrix `crossRepair x₈` is not positive
semidefinite. The proof retains the actual unequal-pair weight, bounds both
sides of the complete compensation, and controls the pure atoms and infinite
tail. It is a source obstruction, not merely a failure of a lower estimate.

**Positive survivor — exact scaling capacity.** For the same fixed coefficient,
there is `1/2<τ<1` such that the loaded source at `x₈` is positive definite
exactly for multipliers `t<τ`, positive semidefinite exactly for `t≤τ`, and
singular at `τ`. The half-load is therefore strictly admissible at the point
where the unit-load fails. The native scale-five positivity theorem and the
fixed-load positive endpoint neighborhoods and scale-5000 tail remain valid.

The survivor has a dependency-closed paper proof and Lean formalization:
[Cross-load scaling capacity at scale eight](../3-formalized/theta-cusp-cross-load-scale-eight-capacity.md).
Declarations in `GaloisForLFunctions.ThetaCuspSections`:
`EightCrossSource.crossRepair_not_posSemidef` and
`EightCrossCapacity.exact_scaling_capacity`.

The source criterion with this fixed coefficient is retired. Global rank-nine
positivity and other compensation profiles remain open.

# Finite readings and exact mass cannot supply a Bézout source reserve

- **ID:** qii-finite-readings-exact-mass-reserve
- **Stage:** 5-failed
- **Type:** FALSIFIED; strongest positive survivor formalized
- **Source:** ../1-in-progress/q-ii-source-effectivity-and-linear-degree.md
- **Rejected statement:** A source threshold obtained from finitely many linear readings and exact L² mass can give Bézout on a full positive-aperture source space.

## Exact scope

Fix any positive aperture `r`, any linear map `L` from its real test space to a
finite-dimensional real vector space, and any function `F : V -> R -> R`.
Use the source reserve `Phi(f)=F(L(f),integral(f²))`, retaining both free fibre
coordinates. None of the closed, strict, or graded source cones has Bézout.
No continuity, growth, linearity, or symmetry condition on `F` is imposed.

This is a theorem about source thresholds with every source available after
a finite fibre lift. It is not a theorem about every conceivable membership
rule using mass, nor about cones that exclude whole source directions.

## Strongest positive survivor [PROVED HERE]

For every real `M`, there is a source in `ker L` of **exactly unit L² mass**
whose Weil energy exceeds `M`. Start with the already proved finite-kernel
Rayleigh witness, of positive mass `m`, and scale by `sqrt(1/m)`.
Linearity preserves the kernel; quadratic homogeneity makes the mass one
and preserves the strict Rayleigh inequality.

Set `c=max(F(0,1),0)+1`. Choose such a unit-mass kernel source with Weil
energy greater than `c`. Assign its two fibre degrees `c` and `1/2`.
The polar square is exactly `c>F(0,1)`, so the lifted cycle is strictly
effective. Its original self-intersection is `c-WeilEnergy<0`.
The same witness belongs to the closed and graded cones.

## No-go closure

- **Killing mechanism:** Exact mass and finite readings remain fixed while Weil energy is unbounded.
- **Positive survivor:** Unit-mass unboundedness in every finite linear reading kernel, and an explicit strict effective negative square for every nonlinear threshold.
- **New insight:** Adding exact quadratic mass to finite linear coordinates does not recover the source energy needed for Bézout. A reserve must retain further infinite source information or impose a narrower source domain.
- **Status:** Dependency-closed paper proof and complete Lean proof. External novelty unverified.

## Lean certificate

Module: `ArithmeticCastelnuovoSeveri/FiniteReadingsAndMassCannotSupplyBezout.lean`.

- `exists_realTestAt_unit_mass_in_ker_weilPair_gt`
- `exists_strictSourceCone_finite_readings_and_mass_negative_square`
- `finite_readings_and_mass_sourceCones_not_bezout`

Actual-file `lake --old env lean` check passed. All three transitive axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
Umbrella import and README entry added.

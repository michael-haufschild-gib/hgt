# Hecke theta unit orbits as logarithmic periodizations

- **ID:** hecke-theta-unit-orbits-as-logarithmic-periodizations
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [Hecke theta Mellin unfolding](hecke-theta-mellin-continuation-and-unit-unfolding.md)
- **Lean:** `HeckeLFunctions/HeckeThetaUnitOrbitsAreLogPeriodizations.lean`

For every actual nonzero integral ideal `b` and positive Gaussian parameter,
its theta series with the zero term removed is exactly the torsion order
times the sum, over integral ideals `I` in class `[b]⁻¹`, of the logarithmic
lattice periodization of the kernel at the chosen generator of `I*b`.

## Proof and declarations

`summable_norm_heckeThetaUnitOrbit` restricts the proved absolute convergence
of the actual ideal Gaussian series along the injective map `u ↦ u*a` for
each nonzero element `a`.

`heckeThetaKernel_unit_as_logTranslate` and
`heckeThetaKernel_torsionLogLattice` express exact unit covariance as a
translation by the negative actual unit logarithm. The torsion coordinate
disappears from the kernel.

`summable_norm_heckeThetaLogPeriodization` proves absolute lattice-sum
convergence by restricting the actual unit orbit to torsion coordinate one.
`tsum_heckeThetaUnitOrbit_eq_logPeriodization` reindexes the norm-summable
unit series by torsion and lattice coordinates, exchanges the sums, and
extracts the exact cardinality `Units.torsionOrder K`.

`summable_norm_heckeThetaClassUnitKernels` proves absolute convergence of
the full class/unit product family by injecting it into the actual ideal.
`heckeIdealTheta_sub_constant_eq_tsum_nonzero` removes exactly the actual
zero term. `heckeIdealTheta_sub_constant_eq_classUnitSum` applies the actual
generator equivalence, and
`heckeIdealTheta_sub_constant_eq_classLogPeriodizations` combines the two
reindexings with the exact torsion coefficient.

## Verification and scope

The complete scratch and final direct source audit passed without warnings.
All three transitive axiom audits contain only `propext`, `Classical.choice`,
and `Quot.sound`. The module is wired into the Hecke umbrella without
compiling that umbrella. No convergence premise, raised proof limit, or
unsafe reducibility override is used.

This proves the actual series identity at every positive parameter. Integral
unfolding and radial Mellin/Gamma identification are separate proof obligations.

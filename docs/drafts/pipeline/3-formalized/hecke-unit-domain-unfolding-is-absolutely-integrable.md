# Absolute integrability of Hecke unit-domain unfolding

- **ID:** hecke-unit-domain-unfolding-is-absolutely-integrable
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [Hecke theta Mellin unfolding](hecke-theta-mellin-continuation-and-unit-unfolding.md)
- **Statement:** For each actual nonzero ideal element and positive Gaussian parameter, its Hecke kernel is integrable on the whole logarithmic space, and its unit-orbit average equals the torsion order times that whole-space integral.

## Dependency-closed proof

The actual unit-domain closure is compact. Restrict the existing summable
ideal Gaussian majorant along the injective map sending a logarithmic lattice
point to its reconstructed unit times the nonzero element. Unit covariance
turns this bound into a summable majorant for translated kernels, uniform on
the unit domain.

Every translated kernel is continuous, hence integrable on the domain.
Its integral norm is bounded by the majorant times the finite domain volume,
so these integral norms form a summable family. Nonnegative fundamental-domain
unfolding identifies the whole-space norm integral with the sum of these
finite domain norm integrals. `ENNReal.ofReal_tsum_of_nonneg` proves it finite.
This discharges whole-space integrability before complex unfolding is used.

Finally apply `integral_tsum_of_summable_integral_norm`, the complex
fundamental-domain identity, and the exact torsion/lattice reindexing of the
actual unit orbit. The torsion order is the cardinality of the actual torsion
subgroup. All analytic hypotheses in generic private helpers must be
discharged from these actual bounds and continuity theorems.

This fixed-parameter result does not yet justify the radial Mellin exchange.
That step still needs the absolute Gamma/ideal-series convergence argument.

## Full class-integral identity

Restrict the same ideal majorant along the injective map from pairs
`(inverse-class ideal, logarithmic lattice point)` to actual nonzero ideal
elements. The majorant is summable uniformly over the unit domain, so the
product series can be integrated and its integrals regrouped. Each inner
lattice sum unfolds by the preceding whole-space integrability argument.
Countability of the class-indexing set follows by its injection into the
number field through chosen nonzero generators.

The resulting exact identity, for every positive `t`, is

`averagedTheta(t) - regulator*physicalConstant = torsionOrder *
 Σ_I ∫_logSpace kernel(profile(x),t,g_I)`.

All data are the actual modulus, Hecke character, ideal, unit lattice,
regulator, and torsion group. No analytic input is left as a premise.

## Lean declarations and audit

Module: `GaloisForLFunctions/HeckeLFunctions/HeckeUnitOrbitsUnfoldOverTheLogSpace.lean`.

- `integrable_heckeThetaKernel_logCoordinates`
- `integral_heckeThetaLogPeriodization_unitDomain`
- `integral_heckeThetaUnitOrbit_unitDomain`
- `summable_norm_heckeThetaClassLogKernels`
- `exists_heckeThetaClassLog_unitDomain_majorant`
- `heckeUnitAveragedTheta_sub_constant_eq_classIntegrals`

The three main integrability, single-orbit, and full-class results passed
`#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound`.
Final direct source audit passed without warnings:

`lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeUnitOrbitsUnfoldOverTheLogSpace.lean`

The module is wired into the Hecke umbrella; no umbrella was compiled.
The radial Mellin/Gamma exchange and Hecke ideal-series identification remain open.

The existing `inverseClassIntegralIdeals_countable` theorem is now public
for the actual class Mellin consumer; its proof is unchanged. A fresh
direct source audit passed without warnings. The module's first olean is
being built solely for that written consumer.

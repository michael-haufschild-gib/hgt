# Actual dual Hecke unit orbits unfold absolutely

- **ID:** hecke-dual-unit-orbits-unfold-over-the-log-space
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Dual theta unfolding](hecke-dual-theta-unfolding-over-fractional-ideal-classes.md)
- **Statement:** The actual dual unit-averaged Hecke theta, minus its regulator-scaled zero mode, equals the torsion order times the sum of whole-log class-generator integrals. The class kernels are integrable and their absolute masses are summable at every positive theta parameter.

## Proof

The existing trace-dual Gaussian majorant proves absolute convergence of
the full Fourier-weighted frequency series. Remove its actual zero term
and use the proved fractional-ideal class/unit equivalence to reindex all
remaining frequencies.

The torsion/log-lattice unit equivalence and actual dual unit covariance
make each summand independent of torsion. Negative log coordinates
translate by `x+log(u)`, so the unit sum is the positive-translation
logarithmic periodization times the exact torsion order.

Choose trivial torsion for every paired class/lattice index. This embeds
the paired index injectively into the actual trace-dual frequencies.
Restricting the Gaussian majorant along this injection gives one
summable bound uniform on the actual unit fundamental domain. The
proved family-unfolding theorem therefore gives whole-space
integrability, summability of absolute class masses, and exact complex
unfolding.

The unit-domain volume is the regulator. Integrating the zero-mode
subtraction and then applying Haar negation yields

```
dualAverage(t) - regulator * dualZeroMode
  = torsionOrder * sum_I integral_whole_log
      finiteFourier(g_I) * parityKernel(weightedProfile(x), t, g_I).
```

Every sum and integral is the actual arithmetic one; neither convergence
nor unit covariance is an additional application hypothesis.

## Lean

Module: `GaloisForLFunctions.HeckeLFunctions.HeckeDualUnitOrbitsUnfoldOverTheLogSpace`.
Namespace: `GaloisForLFunctions.HeckeLFunctions`.

- `heckeDualClassUnitFrequency`, `heckeDualClassUnitFrequency_injective`
- `summable_norm_heckeDualThetaKernel`, `summable_norm_heckeDualClassUnitKernels`
- `heckeDualIdealTheta_sub_constant_eq_tsum_nonzero`
- `heckeDualIdealTheta_sub_constant_eq_classUnitSum`
- `heckeDualThetaKernel_torsionLogLattice`
- `tsum_heckeDualClassUnitOrbit_eq_logPeriodization`
- `summable_norm_heckeDualClassLogKernels`
- `heckeDualIdealTheta_sub_constant_eq_classLogSum`
- `exists_heckeDualClassLog_unitDomain_majorant`
- `heckeDualClassKernels_unfold_absolutely`
- `heckeUnitAveragedDualTheta_sub_constant_eq_classIntegrals_negative`
- `heckeUnitAveragedDualTheta_sub_constant_eq_classIntegrals`

All three main transitive axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`. Final direct source audit passes
without warnings:

```
lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeDualUnitOrbitsUnfoldOverTheLogSpace.lean
```

Wired into `HeckeLFunctions.lean`; the umbrella was not compiled.
The infinite Mellin exchange and completed reflection remain separate
obligations.

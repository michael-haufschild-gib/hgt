# Unit-averaged Hecke Mellin transform equals the actual ideal-class series

- **ID:** hecke-unit-averaged-mellin-is-ideal-class-series
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Actual archimedean Mellin integrals](hecke-archimedean-mellin-integrals.md)
- **Statement:** On `Re s>1`, the actual unit-averaged theta minus its regulator-weighted zero term has Mellin transform equal to the inverse-class ideal series times `torsionOrder*GammaFactor*heckeIdealTerm(b)/(degree*2^unitRank)`.

## Proof

For each selected generator `g_I`, the proved actual-element identity gives
the logarithmic Mellin density as `heckeIdealTerm(I)*heckeIdealTerm(b)`
times a translated archimedean kernel. Translation and the proved radial
Jacobian preserve its integral of the norm up to the same fixed positive
factor. Consequently these norm integrals form a summable family: the
existing `summable_norm_heckeIdealTerm` supplies the actual ideal-series
absolute convergence for `Re s>1`, restricted to the inverse ordinary class.

For each ideal, joint absolute integrability gives Fubini and an integrable
radial integral. Its norm integral is bounded by the joint norm integral.
The resulting summable majorant justifies both absolute convergence and
the infinite sum/integral exchange. The fixed-parameter theorem
`heckeUnitAveragedTheta_sub_constant_eq_classIntegrals` identifies this sum
with the actual averaged theta for every positive radial parameter.

The element Mellin value then gives the exact factor. No summability of
the complex theta alone is substituted for summability of norm integrals.

## Existing sources

- `HeckeLSeriesHaveEulerProducts.heckeIdealTerm` is multiplicative on actual
  nonzero ideals and equals `heckeValue(I)*N(I)^(-s)`.
- `summable_norm_heckeIdealTerm` proves absolute ideal-series convergence.
- `span_inverseClassGenerator` identifies `(g_I)=I*b`.
- `HeckeUnitOrbitsUnfoldOverTheLogSpace` proves countability of the
  inverse ideal class, now public for reuse.
- `exists_integral_rep` in `RayClassesOfPrincipalIdealsAreReadByResidues`
  supplies a representative prime to the modulus in every ordinary ideal
  class. This will allow division by the base-ideal coefficient later.

## Lean verification

Module: `HeckeLFunctions/HeckeUnitAveragedMellinIsTheIdealClassSeries.lean`.

- `summable_integral_norm_heckeClassLogMellinKernel` and
  `summable_integral_norm_heckeClassRadialMellinKernel` prove the absolute
  estimates required for both exchanges.
- `mellinConvergent_heckeUnitAveragedTheta_classSeries` proves actual Mellin
  convergence on `Re s>1`.
- `mellin_heckeUnitAveragedTheta_eq_inverseClassL` gives the exact ideal-class
  series value.
- `heckeUnitThetaMellinContinuation_eq_inverseClassL` identifies the already
  continued theta transform with that value on the full `Re s>1` domain.
  Zero parity uses the weak FE-pair bound; nonzero parity uses the proved
  strong FE pair's unrestricted Mellin agreement.

Four main transitive axiom audits returned only `propext`, `Classical.choice`,
and `Quot.sound`. Final direct source audit passed without warnings:
`lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeUnitAveragedMellinIsTheIdealClassSeries.lean`.
Wired into the Hecke umbrella; umbrella not compiled.

Full ordinary-class recombination, residue cancellation, and primitive
finite-Gauss/conductor normalization remain open.

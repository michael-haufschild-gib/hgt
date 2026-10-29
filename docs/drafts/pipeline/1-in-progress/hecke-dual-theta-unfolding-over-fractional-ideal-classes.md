# Dual Hecke theta unfolding over fractional-ideal classes

- **ID:** hecke-dual-theta-unfolding-over-fractional-ideal-classes
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Primitive Gauss and dual-character arithmetic](hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- **Statement:** Reindex the actual nonzero trace-dual frequencies into ordinary-class integral ideals and global units, and identify the actual dual unit-averaged Mellin transform with the inverse-character class series, including the fractional-ideal norm and torsion/Jacobian factors.

## Current dependencies

Arithmetic support and nonzero primitive reference frequencies are finalized
in `HeckeFourierSupportIsIdealCoprimality.lean`. Unit-fraction covariance
and exact transfer to the unit base are finalized in
`HeckeFourierCoefficientsScaleByRayResidues.lean`.
The corrected Gauss constant is finalized and audited in
`HeckePrimitiveGaussConstantsHaveExactNorm.lean`. The actual inverse-Hecke coefficient formula is
written in `/tmp/HeckeDualCoefficientCharacterScratch.lean` but is not yet
verified. This card does not assume that draft as a proved input.

Existing analytic sources, inspected:

- `NonzeroIdealElementsAreGlobalUnitOrbits.lean`: actual integral-ideal
  elements are inverse-class ideals times global units, with exact
  generator and norm formulas. Its base ideal is integral.
- `HeckeElementKernelsHaveExactMellinIntegrals.lean`: actual log profiles,
  parity splitting, translated archimedean kernels, exact Mellin value,
  and absolute mass. The profile and parity lemmas already accept field
  elements; the principal coefficient and norm lemmas use integral ones.
- `HeckeUnitOrbitsUnfoldOverTheLogSpace.lean`: summable Gaussian majorants
  prove absolute unit-domain unfolding before exchanging complex sums.
- `HeckeUnitAveragedMellinIsTheIdealClassSeries.lean`: absolute ideal-series
  convergence controls class Mellin masses; Fubini and the log radial
  Jacobian give the exact torsion/Gamma normalization.
- `HeckeThetaAveragesOverTheUnitDomain.lean`: the actual dual average
  integrates `heckeDualIdealTheta` at the **negative** weighted log profile.
  Its proved weak Mellin pair already has the required reflection.

## Orbit construction

For `J=dual(mb)`, index integral nonzero ideals by the ordinary class
`[J]⁻¹`. For each such ideal `I`, `IJ` is principal. Choose a nonzero
generator `g_I`. Since `I≤1`, it belongs to `J`.

The map `(I,u)↦u*g_I` is a bijection onto the nonzero elements of `J`.
For surjectivity, attach `I_a=(a)J⁻¹`, already constructed and proved
integral. Its product with `J` is `(a)`, so it has the required class.
Equality of two principal fractional ideals gives a global unit relating
their generators, by `FractionalIdeal.spanSingleton_eq_spanSingleton`.
For injectivity, equality of elements implies equality of principal ideals;
cancel `J`, then cancel the nonzero generator and use injectivity of the
ring-of-integers embedding to recover the unit.

Applying the fractional-ideal norm to `I_a J=(a)` gives
`|Norm_(K/ℚ)(a)|=Norm(I_a)Norm(J)`. Mathlib
`FractionalIdeal.absNorm_span_singleton (𝓞 K)` is the checked exact source.
This avoids assuming an integral generator for a fractional principal ideal.

## Unit unfolding and Mellin value

The drafted arithmetic coefficient law is
`F_b(a)sgnψ(a)=Cψ ψ(b)ψ⁻¹(I_a)`. With it proved, the actual Gaussian
Mellin density is the inverse ideal summand times
`Cψ ψ(b)Norm(J)^(-s)` and a translated archimedean log kernel.
Its norm integral is the ideal-summand norm times a common finite mass,
so the existing absolute Hecke series convergence gives summability for
`Re(s)>1`.

The dual average uses `-weightedLogProfile(x)`. Multiplication of the
frequency by a global unit translates this parameter by **plus** its
unit logarithm. Reindex the log lattice by negation to use the existing
fundamental-domain unfolding; then change the whole-space variable
`x↦-x`. Both steps must be formalized, with their measure statements,
before reusing the positive-profile element Mellin formula.

The target dual Mellin value, for the inverse class of `J`, is

```
torsionOrder * Cψ * ψ(b) * Norm(J)^(-s)
  * (inverse-character class series at s)
  * Γψ(s)/(degree * 2^unitRank).
```

Conductor and parity invariance under character inversion must also be
proved before replacing `Γψ` by `Γ_(ψ⁻¹)`.

## Global recombination

Since `[J_b]⁻¹=[different*m]*[b]`, the inverse dual classes permute all
ordinary classes when the original base classes do. Sum the actual class
Mellin formulas using this permutation. The checked Mathlib different
identities give `Norm(J_b)=1/(|disc K| Norm(m) Norm(b))`; a verification
scratch for the general norm formula is written but not yet checked.
The existing class weight and Poisson scalar then cancel the base norm
and character factors exactly, yielding the completed reflection recorded
on the parent card.

No fractional orbit equivalence, dual Mellin exchange, or normalized
reflection is yet claimed as formalized here. Raw completed zero-mode
cancellation remains on its separate active card.

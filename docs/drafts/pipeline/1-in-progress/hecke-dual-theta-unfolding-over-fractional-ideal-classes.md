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
`HeckePrimitiveGaussConstantsHaveExactNorm.lean`. The actual inverse-Hecke
coefficient formula is finalized in
`HeckeFourierCoefficientsAreInverseHeckeValues.lean`. All five main axiom
audits are standard only, and the final direct source check passes without
warnings. See [the coefficient proof](../3-formalized/hecke-fourier-coefficients-are-inverse-hecke-values.md).

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

The proved arithmetic coefficient law is
`F_b(a)sgnψ(a)=Cψ ψ(b)ψ⁻¹(I_a)`. Thus the actual Gaussian
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

Conductor and parity invariance under character inversion are now
finalized in `HeckeConductorsAndParitiesAreInvariantUnderInversion.lean`,
including equality `Γψ=Γ_(ψ⁻¹)` and both Mellin normalizations.
Final direct source audit passes without warnings; the main transitive
axiom audits are standard only.

## Global recombination

Since `[J_b]⁻¹=[different*m]*[b]`, the inverse dual classes permute all
ordinary classes when the original base classes do. Sum the actual class
Mellin formulas using this permutation. The checked Mathlib different
identities give `Norm(J_b)=1/(|disc K| Norm(m) Norm(b))`. The general norm
formula is finalized in
`HTGeometry/NumberFieldTraceDualsHaveDiscriminantNorms.lean`; final direct
source audit passes without warnings and the transitive axiom audit is
standard only. See [the norm proof](../3-formalized/number-field-trace-duals-have-discriminant-norms.md).
The existing class weight and Poisson scalar then cancel the base norm
and character factors exactly, yielding the completed reflection recorded
on the parent card.

The fractional orbit equivalence is now formalized. Dual Mellin exchange
and normalized reflection remain open. Raw completed zero-mode
cancellation remains on its separate active card.

The full fractional orbit construction is finalized in
`HTGeometry/FractionalIdealElementsAreClassUnitOrbits.lean`: principal
generators, integral inverse-class quotient for every nonzero element,
bijection with global units, and exact generator/orbit norms. Both main
transitive axiom audits pass with standard axioms only; the final direct
source audit passes without warnings. See
[the completed orbit proof](../3-formalized/fractional-ideal-elements-are-class-unit-orbits.md).
This is a reusable construction
for every invertible fractional ideal, independent of the Hecke Fourier
coefficients. It also proves countability of the inverse-class ideal index.

Its consumer `HeckeLFunctions/HeckeDualFrequenciesHaveClassGenerators.lean`
is finalized. It identifies the selected orbit generator's frequency
ideal with the orbit index and specializes both the exact norm and
inverse-character coefficient. All three main transitive axiom audits
are standard only; final direct source audit passes without warnings.
See [the exact dual-generator proof](../3-formalized/hecke-dual-frequencies-have-class-generators.md).
It now also proves the exact ordinary-class law
`[J_b]⁻¹=[J_1]⁻¹[b]` directly from `J_b*b=J_1`, and constructs the
resulting class permutation `c↦[J_1]⁻¹c⁻¹`.

The field-element Mellin extension is written in
`/tmp/HeckeFieldElementMellinScratch.lean`. It uses the actual parity kernel
at any nonzero `a∈K`, with coefficient `sgnψ(a)|Norm(a)|⁻ˢ`, and proves
the translated archimedean identity, joint integrability, exact absolute
mass, and whole-log Mellin value. Mathlib's checked weighted-log formula
already applies to arbitrary field elements. This scratch is not yet
fully verified and is not counted as a proved analytic dependency.

`/tmp/HeckeDualUnitCovarianceScratch.lean` now contains the actual dual
kernel, simultaneous unit/place-log covariance, and the negative-profile
translation formula. It uses the proved Fourier covariance and global
finite/sign relation; the expected translation is `x↦x+log(u)`.
This scratch has not yet been compiled. The existing public
`exists_uniform_heckeDualThetaKernel_majorant` supplies its summable bound
uniformly on the unit domain.

For the positive lattice translations in the negative-profile kernel,
Mathlib's `IsAddFundamentalDomain.integral_eq_tsum''` directly unfolds
`f(l+ᵥx)` and is available in `MeasureTheory/Group/FundamentalDomain.lean`.
Its source is checked, as is the matching nonnegative formula
`lintegral_eq_tsum''`. Together they replace an explicit negation reindex
in both integrals, while still proving whole-space integrability before
complex unfolding. A proposed
joint class/lattice majorant lemma will control all class integrals at
once, rather than exporting or copying the older private single-orbit
helpers.

That family lemma is now written in
`/tmp/HeckeUnitDomainFamilyUnfoldingScratch.lean`. A single summable bound
on `(class, lattice)` first bounds the sum of integral norms on the
compact unit domain. Nonnegative fundamental-domain unfolding proves
whole-log-space integrability for every class and summability of their
absolute masses. Only then does complex unfolding identify the integral
of the paired periodization with the sum of whole-space class integrals.
The proof uses the checked `summable_prod_of_nonneg` and both positive
translation tile formulas. It has not yet been compiled.

## Verification queue

- `HeckeConductorsAndParitiesAreInvariantUnderInversion.lean`: finalized;
  final source audit and main transitive axiom audits pass. Its generic
  conductor dependency is finalized and has its consumer olean built.
- `HTGeometry/FractionalIdealElementsAreClassUnitOrbits.lean`: finalized;
  final source and both main transitive axiom audits pass. Required
  consumer olean is built.
- `HeckeLFunctions/HeckeDualFrequenciesHaveClassGenerators.lean`: finalized;
  final source check and all three main transitive axiom audits pass.
  No consumer olean built yet.
- `/tmp/HeckeFieldElementMellinScratch.lean`: first check exposed a
  dependent rewrite, real-to-complex absolute-value casts, and an omitted
  explicit Haar measure. The second check leaves only the `Units.mk0`
  projection match in the kernel exponential identity; the concrete
  helper equality is now simplified before rewriting. Third check
  running. All other declarations elaborate, but their main proofs are
  not counted as formalized until this dependency is closed.
- `/tmp/HeckeDualUnitCovarianceScratch.lean`: written, unchecked; its
  inverse-coefficient dependency is built.
- `/tmp/HeckeUnitDomainFamilyUnfoldingScratch.lean`: written, unchecked;
  imports existing unit-domain and absolute-periodization infrastructure.

The inverse-coefficient and trace-dual-norm sources have passed final
audits, and both required consumer oleans are built.
No dual class Mellin identity or completed functional equation is yet
claimed from the unchecked files above.

## Actual-family unfolding after the queued checks

For each dual class ideal `I`, let
`F_I(x)=F_b(g_I)*heckeParityKernel(ψ,-weightedProfile(x),t,g_I)`.
For a lattice point `l`, choose the unit corresponding to `(1,l)` under
the proved torsion/log-lattice equivalence. The map
`(I,l)↦u_l*g_I` into the actual trace-dual ideal is injective by the new
fractional orbit equivalence. Composing the existing dual Gaussian
majorant with this injection gives a summable majorant on `(I,l)`.
On the unit domain, the bound for `-weightedProfile(x)` follows from
the existing absolute coordinate bound. The drafted negative-profile
covariance identifies its summand with `F_I(x+l)`.

Remove the actual zero term from the dual theta sum, reindex nonzero
frequencies by the class/unit equivalence, and reindex units by torsion
times the logarithm lattice. Covariance makes the torsion coordinate
constant, yielding its exact cardinality `torsionOrder K`. Apply the
joint-family unfolding theorem to obtain

```
dualAverage(t) - regulator*dualZeroMode
  = torsionOrder * sum_I integral_over_logSpace F_I.
```

The queued field-element Mellin proof now also contains Haar-negation
invariance, so these whole-space negative-profile integrals reduce to
the positive-profile Mellin formula with the same sign and norm factors.
The exact dual generator norm and coefficient then give the common
Gauss/base/fractional-norm factor times the inverse-character ideal term.
Absolute ideal-series convergence supplies the remaining Mellin exchange.

For comparison with the dual weak-pair continuation on all `Re(s)>1`,
follow the proved primal argument: parity degree zero gives the weak
pair's real-part inequality; nonzero parity gives a strong pair and hence
its Mellin identity at every argument. Apply this to the symmetric pair.

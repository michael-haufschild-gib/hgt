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
  A consumer is written in `/tmp/HeckeDualClassMellinScratch.lean`;
  its required olean is built.
- `HeckeFieldElementKernelsHaveExactMellinIntegrals.lean`: finalized; final
  direct source check passes without warnings, and all five main
  transitive axiom audits are standard only. Its consumer olean is built.
- `HeckeDualThetaKernelsAreUnitCovariant.lean`: finalized; final direct
  source audit passes without warnings, and both main transitive axiom
  audits are standard only. Its consumer olean is built.
- `HTGeometry/NumberFieldLogPeriodizationsHaveAbsoluteUnfolding.lean`:
  finalized; final direct source audit passes without warnings and its
  main transitive axiom audit is standard only. Required consumer olean
  is queued.

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

The consumer `/tmp/HeckeDualClassMellinScratch.lean` is now written.
It combines the actual generator coefficient with its exact fractional
norm, obtaining the inverse-character ideal term times
`Cψ ψ(b)Norm(J_b)^(-s)`. Its joint Mellin-density formula gives absolute
integrability, exact norm mass, summability over the ideal class for
`Re(s)>1`, and the exact Gamma integral. It remains unchecked until the
field-element and unit-covariance imports are finalized. This written
consumer requires their oleans and the dual-class-generator olean.

`/tmp/HeckeDualUnitUnfoldingScratch.lean` now contains the complete actual
family unfolding draft: nonzero-frequency reindexing, absolute
class/unit and class/log convergence, exact torsion factor, one joint
unit-domain majorant, whole-log absolute unfolding, zero-mode subtraction,
and conversion to positive logarithmic coordinates by Haar negation.
This is unchecked. It is the written consumer requiring the generic
family-unfolding module's olean after that module is finalized.

The field-element Mellin extension is finalized; see
[the exact field-element proof](../3-formalized/hecke-field-element-kernels-have-exact-mellin-integrals.md).
The earlier unverified scratch status is superseded by its successful
final source and transitive axiom audits.

The final analytic assembly is drafted in
`/tmp/HeckeDualAveragedMellinScratch.lean`: joint-to-radial absolute mass
bounds, infinite Mellin exchange, the exact inverse-character dual class
series, and comparison with the symmetric actual weak-pair continuation
on `Re(s)>1`. This remains unchecked and is a written consumer of the
queued class-Mellin, actual unit-unfolding, and inversion-invariance
modules. It does not yet perform finite class recombination or global
completed pole correction.

The actual dual kernel covariance is finalized; see
[the unit-covariance proof](../3-formalized/hecke-dual-theta-kernels-are-unit-covariant.md).
This supersedes its earlier unchecked scratch status.

## Exact scalar cancellation for global recombination

Write `D=|disc K|`, `N=Norm(m)`, `B=Norm(b)`, `delta=D*N`, and
`d=parityDegree`. The actual factors have the following product for
an inverse-class base representative:

```
weight_b(1-s) = psi(b)^(-1) B^(1-s),
PoissonScalar_b = (-i)^d/(N B sqrt(D)),
dualMellinFactor_b(s) = Cpsi psi(b) (delta B)^s.
```

Positive real complex-power multiplicativity and addition cancel both
base factors exactly. The common product is

```
Cpsi (-i)^d delta^s/(N sqrt(D)).
```

This form avoids premature splitting of the discriminant/conductor
powers. Multiplying by `delta^((1-s)/2)` and comparing with the inverse
completion factor `delta^(s/2)` leaves
`Cpsi (-i)^d/sqrt(N)`. The already proved normalized Gauss norm and
`||-i||=1` give root-number norm one. These identities are queued for
formalization after the analytic consumers; no normalized reflection
is claimed yet.

Checked source APIs for the queued symmetric-pair comparison:
`IsStrongFEPair.symm` and `WeakFEPair.symm` in Mathlib
`NumberTheory/LSeries/AbstractFuncEq.lean`. Positive real inverse powers
can use `Complex.inv_cpow` with the nonnegative real argument equal to
zero, hence unequal to pi. `NumberField.discr_ne_zero` is the checked
source for discriminant positivity.

The generic family unfolding is finalized; see
[absolute family unfolding](../3-formalized/number-field-log-periodizations-have-absolute-unfolding.md).
This supersedes its earlier unchecked scratch status. The actual dual
Gaussian consumer remains unchecked until its required imports are built.

The scalar assembly is now drafted in
`/tmp/HeckeCompletedReflectionFactorsScratch.lean`: completion norm and
entire nonzero completion factor, actual normalized root number with
norm one, exact dual fractional-norm power, arithmetic Poisson scalar,
base-character/base-norm cancellation, and the final conductor scaling
identity. It is unchecked and imports the queued exact dual-class
Mellin module. Positive-real inverse-power and square-root identities
are being verified in this scratch before permanent use.

## Final primitive reflection draft

`/tmp/HeckePrimitiveCompletedFunctionalEquationScratch.lean` now contains
class-fiber reindexing under the explicit dual permutation, finite class
recombination, the corrected conductor-scaled completion, and initial
right-half-plane reflection. To extend across the plane, it defines the
pole-cleared entire function from the regular part and the two constant
pole coefficients **before** totalized division. Analytic uniqueness
then gives global pole-cleared reflection, reflection away from the two
possible poles, and reflection at every point for nontrivial characters.
This is unchecked and imports the queued dual Mellin, scalar, and
completed removable-value modules. HL7 remains open until the full chain
passes final source and transitive axiom audits.

The dual-generator, arbitrary-field Mellin, and dual unit-covariance
consumer oleans are built. The first check of
`/tmp/HeckeDualClassMellinScratch.lean` is now running.

The dual class Mellin scratch check verifies its exact coefficient,
norm masses, summability, and integral formula with standard axioms.
Its sole error is pointwise rewriting beneath an unapplied function in
`Integrable`; an explicit eta-expanded lambda now exposes the density.
The corrected source is promoted to
`HeckeDualClassKernelsHaveExactMellinIntegrals.lean` for its final direct
check, with an added transitive audit of joint integrability. It is not
yet counted as finalized or wired into the umbrella.

## Current verification dependency graph

Finalized and built for their written consumers:
- `HeckeDualFrequenciesHaveClassGenerators`
- `HeckeFieldElementKernelsHaveExactMellinIntegrals`
- `HeckeDualThetaKernelsAreUnitCovariant`

Finalized, with required consumer oleans still pending:
- `HTGeometry/NumberFieldLogPeriodizationsHaveAbsoluteUnfolding`
- `HeckeConductorsAndParitiesAreInvariantUnderInversion`

Current final source check:
- `HeckeDualClassKernelsHaveExactMellinIntegrals` (the single eta-expansion correction).

Unchecked complete drafts and intended module names:
- `/tmp/HeckeDualUnitUnfoldingScratch.lean` →
  `HeckeDualUnitOrbitsUnfoldOverTheLogSpace`.
- `/tmp/HeckeDualAveragedMellinScratch.lean` →
  `HeckeDualAveragedMellinIsTheInverseClassSeries`; imports both preceding
  dual analytic modules and inversion invariance.
- `/tmp/HeckeCompletedThetaResidueCancellationScratch.lean` →
  `HeckeCompletedThetaResiduesCancel`; imports the already built global
  ordinary L-continuation.
- `/tmp/HeckeGammaCompletedContinuationScratch.lean` →
  `HeckeGammaCompletedFunctionsHaveRemovableValues`; imports residue
  cancellation.
- `/tmp/HeckeCompletedReflectionFactorsScratch.lean` →
  `HeckeCompletionFactorsHaveExactArithmeticNormalization`; imports
  the exact dual class Mellin module.
- `/tmp/HeckePrimitiveCompletedFunctionalEquationScratch.lean` →
  `PrimitiveHeckeLFunctionsHaveCompletedFunctionalEquation`; imports
  dual averaged Mellin, arithmetic normalization, and completed removable
  values.

Each finished dependency needs an olean only for the written consumers
listed here. Final source audits and transitive axiom audits precede
finalized status. No umbrella compilation is needed. The parent goal
remains active: finish finite-order Hecke L-functions before starting
class field theory.

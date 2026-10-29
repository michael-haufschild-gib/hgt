# Dual Hecke theta unfolding over fractional-ideal classes

- **ID:** hecke-dual-theta-unfolding-over-fractional-ideal-classes
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Primitive Gauss and dual-character arithmetic](hecke-primitive-gauss-sums-and-arithmetic-dual-character.md)
- **Statement:** Identify the actual dual unit-averaged Mellin transform with the inverse-character class series, including every Gauss, discriminant, conductor, torsion, and Jacobian factor; then derive the primitive completed functional equation.

## Current status

Arithmetic coefficients, fractional class/unit orbits, actual dual unit
unfolding, exact class Mellin integrals, infinite Mellin exchange, and
symmetric theta-continuation identification are finalized. Scalar/class
recombination, completed removable values, and global reflection have
complete drafts but remain under verification. **HL7 remains open. Class field theory has not begun.**

Every finalized module below passes its final direct source audit without
warnings. Its recorded transitive axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Finished modules are wired into their
umbrellas; no umbrella was compiled.

## Finalized arithmetic

- [Inverse Hecke coefficients](../3-formalized/hecke-fourier-coefficients-are-inverse-hecke-values.md):
  `HeckeFourierCoefficientsAreInverseHeckeValues` proves
  `F_b(a)sgnψ(a)=Cψ ψ(b)ψ⁻¹(I_a)` for every nonzero actual dual frequency,
  including unsupported ideals where both sides vanish.
- [Exact Gauss norm](../3-formalized/hecke-primitive-gauss-constants-have-exact-norm.md):
  `HeckePrimitiveGaussConstantsHaveExactNorm` constructs the actual
  reference frequency and proves `||Cψ||=sqrt(Norm(m))` for finite-primitive
  characters. No principal conductor or different is assumed.
- [Trace-dual norms](../3-formalized/number-field-trace-duals-have-discriminant-norms.md):
  `HTGeometry/NumberFieldTraceDualsHaveDiscriminantNorms` proves
  `Norm(dual(I))=(|disc K|Norm(I))⁻¹`.
- [Fractional class/unit orbits](../3-formalized/fractional-ideal-elements-are-class-unit-orbits.md):
  `HTGeometry/FractionalIdealElementsAreClassUnitOrbits` constructs
  nonzero generators, their class/unit equivalence, countability of the
  class-ideal index, and exact generator/orbit norms.
- [Actual dual generators](../3-formalized/hecke-dual-frequencies-have-class-generators.md):
  `HeckeDualFrequenciesHaveClassGenerators` identifies generator
  frequency ideals, specializes exact norms and inverse coefficients,
  and constructs the dual permutation `c ↦ [J_1]⁻¹ c⁻¹`.
- [Inversion invariance](../3-formalized/hecke-conductors-and-parities-are-invariant-under-inversion.md):
  `HeckeConductorsAndParitiesAreInvariantUnderInversion` proves conductor,
  sign, parity, Gamma, and Mellin-normalization invariance under `ψ ↦ ψ⁻¹`.

## Fractional orbit proof

Let `J_b=dual(mb)`. For each nonzero integral ideal `I` in class `[J_b]⁻¹`,
choose a generator `g_I` of the actual principal fractional product `I J_b`.
Since `I≤1`, this generator lies in `J_b`.

The map `(I,u)↦u*g_I` is a bijection onto nonzero elements of `J_b`.
For surjectivity, `(a)J_b⁻¹≤1` gives the required integral ideal. Equality
of principal fractional ideals gives the relating global unit, using
`FractionalIdeal.spanSingleton_eq_spanSingleton`. Injectivity follows by
cancelling `J_b`, then the nonzero generator and the ring-of-integers
embedding. Applying fractional norms gives

```
|Norm(g_I)| = Norm(I) Norm(J_b),
Norm(J_b) = (|disc K| Norm(m) Norm(b))⁻¹.
```

Multiplication `J_b*b=J_1` gives `[J_b]⁻¹=[J_1]⁻¹[b]`. The actual base
representative of class `c⁻¹` therefore indexes dual ideals of class
`[J_1]⁻¹c⁻¹`, an explicit permutation of all ordinary classes.

## Finalized analytic inputs

- [Field-element Mellin formula](../3-formalized/hecke-field-element-kernels-have-exact-mellin-integrals.md):
  `HeckeFieldElementKernelsHaveExactMellinIntegrals` extends the actual
  parity-kernel formula to every nonzero `a∈K`. It includes the translated
  archimedean identity, joint integrability on `Re(s)>0`, exact absolute
  mass and Gamma/Jacobian value, and Haar negation for negative profiles.
- [Actual unit covariance](../3-formalized/hecke-dual-theta-kernels-are-unit-covariant.md):
  `HeckeDualThetaKernelsAreUnitCovariant` proves finite Fourier/parity
  cancellation on actual global units. The negative profile of the dual
  average translates by `x+log(u)`.
- [Absolute family unfolding](../3-formalized/number-field-log-periodizations-have-absolute-unfolding.md):
  `HTGeometry/NumberFieldLogPeriodizationsHaveAbsoluteUnfolding` uses one
  summable paired family/lattice majorant to prove whole-space
  integrability, summability of absolute masses, and exact unfolding.
- [Exact class Mellin integrals](../3-formalized/hecke-dual-class-kernels-have-exact-mellin-integrals.md):
  `HeckeDualClassKernelsHaveExactMellinIntegrals` proves the actual
  inverse ideal coefficient, joint integrability, exact Gamma integral,
  and summability of all joint absolute masses on `Re(s)>1`.
- [Actual dual unit unfolding](../3-formalized/hecke-dual-unit-orbits-unfold-over-the-log-space.md):
  `HeckeDualUnitOrbitsUnfoldOverTheLogSpace` proves the exact full averaged
  dual theta identity below, including absolute convergence.

## Actual unit unfolding

For each selected generator set
`F_I(x)=F_b(g_I)*parityKernel(ψ,-weightedProfile(x),t,g_I)`.
Choose the unit corresponding to `(1,l)` under the actual torsion/log
lattice equivalence. The map `(I,l)↦u_l*g_I` into actual dual frequencies
is injective by the fractional orbit equivalence. Restricting the proved
uniform dual Gaussian majorant along this injection gives one summable
bound on every `F_I(x+l)` over the unit domain.

Mathlib's positive-translation formulas
`IsAddFundamentalDomain.lintegral_eq_tsum''` and `integral_eq_tsum''`
unfold this directly. Nonnegative unfolding first proves whole-space
integrability and summable masses; complex unfolding follows. No lattice
negation reindex is needed. Torsion independence gives its exact order,
and unit-domain volume gives the regulator. Haar negation then yields

```
dualAverage(t) - regulator*dualZeroMode
  = torsionOrder * sum_I integral_whole_log
      F_b(g_I)*parityKernel(ψ,weightedProfile(x),t,g_I).
```

All identities above are now formalized. The actual carrier needs an
explicit zero element, since its fractional-ideal subtype has no zero
instance. Typed projection maps and typed continuous factors avoid
unnecessary definitional unfolding; all checks use default limits.

## Infinite Mellin exchange — formalized

The proved arithmetic coefficient and norm give

```
A_b(s) = Cψ ψ(b) Norm(J_b)^(-s),
density_I = idealTerm(ψ⁻¹,s,I) A_b(s)
              * archimedeanKernel(s, radialLog(p)+logProfile(g_I)).
```

The exact joint absolute mass is the inverse ideal-term norm times one
common archimedean mass. Absolute ideal-series convergence makes these
masses summable on `Re(s)>1`. Fubini bounds radial masses by joint masses,
so integral/sum exchange gives the target

```
Mellin(dualAverage - regulator*dualZeroMode)(MArgψ(s))
  = torsionOrder * inverseCharacterClassSeries(s) * A_b(s)
      * Γψ(s)/(degree * 2^unitRank).
```

The symmetric actual weak pair has this Mellin value throughout
`Re(s)>1`. Zero parity gives the weak-pair real-part inequality; nonzero
parity gives an actual strong pair and its symmetric strong pair.
`IsStrongFEPair.symm` and `WeakFEPair.symm` are checked in Mathlib
`NumberTheory/LSeries/AbstractFuncEq.lean`.

The infinite exchange and symmetric continuation comparison are finalized
in `HeckeDualAveragedMellinIsTheInverseClassSeries`. Both main transitive
axiom audits and the final direct source audit pass without warnings.
See [the exact averaged Mellin proof](../3-formalized/hecke-dual-averaged-mellin-is-the-inverse-class-series.md).

## Exact global scalar — draft

Write `D=|disc K|`, `N=Norm(m)`, `B=Norm(b)`, `delta=D*N`, and
`d=parityDegree`. The factors are

```
weight_b(1-s) = ψ(b)^(-1) B^(1-s),
PoissonScalar_b = (-i)^d/(N B sqrt(D)),
A_b(s) = Cψ ψ(b) (delta B)^s.
```

Positive-real complex-power multiplication and addition cancel the base
norm and character, leaving

```
Cψ (-i)^d delta^s/(N sqrt(D)).
```

After multiplying by `delta^((1-s)/2)` and extracting the inverse
completion factor `delta^(s/2)`, the remaining scalar is
`Wψ=Cψ(-i)^d/sqrt(N)`. The proved Gauss norm gives `||Wψ||=1`.
All scalar identities are drafted, not yet verified, in
`/tmp/HeckeCompletedReflectionFactorsScratch.lean`.

Checked sources include `Complex.inv_cpow`, `Complex.mul_cpow_ofReal_nonneg`,
`Complex.ofReal_cpow`, `NumberField.discr_ne_zero`, and `Nat.cast_natAbs`.
New uses remain in scratch until verified.

## Completed removable values and global reflection — drafts

Raw completed-theta numerators must be treated before reciprocal Gamma
removal. The [completed residue card](hecke-unramified-character-descent-and-residue-cancellation.md)
tracks physical cancellation by ordinary-class orthogonality and dual
cancellation by the proved ordinary L-pole coefficient plus nonvanishing
of Gamma at one. Entire divided differences supply both removable values.
The residue scratch check passes with standard-only transitive axioms;
its final source audit is running. The corrected-completion draft remains unchecked.

Finite class recombination uses the proved permutation and the exact
scalar above. The final draft defines the pole-cleared entire function
from the regular part and both constant pole coefficients before
performing totalized division. Analytic uniqueness gives global
pole-cleared reflection and reflection away from zero and one. For
nontrivial characters, entireness gives reflection at every point.
No normalized reflection is claimed until the full chain is verified.

## Verification queue and consumer oleans

Finalized with consumer oleans built:
- `HeckeDualFrequenciesHaveClassGenerators`
- `HeckeFieldElementKernelsHaveExactMellinIntegrals`
- `HeckeDualThetaKernelsAreUnitCovariant`
- `HTGeometry/NumberFieldLogPeriodizationsHaveAbsoluteUnfolding`
- `HeckeDualUnitOrbitsUnfoldOverTheLogSpace`
- `HeckeDualClassKernelsHaveExactMellinIntegrals`
- `HeckeConductorsAndParitiesAreInvariantUnderInversion`

Finalized, required consumer olean pending:
- `HeckeDualAveragedMellinIsTheInverseClassSeries`.

Current check:
- `HeckeCompletedThetaResiduesCancel`: final direct source audit running.
  Its scratch check passes with standard-only transitive axioms; the sole
  correction was using `Units.val_inv_eq_inv_val` for inverse coercion.

Unchecked complete drafts and intended module names:
- `/tmp/HeckeGammaCompletedContinuationScratch.lean` →
  `HeckeGammaCompletedFunctionsHaveRemovableValues`; imports residue
  cancellation.
- `/tmp/HeckeCompletedReflectionFactorsScratch.lean` →
  `HeckeCompletionFactorsHaveExactArithmeticNormalization`; imports the
  exact dual class Mellin module.
- `/tmp/HeckePrimitiveCompletedFunctionalEquationScratch.lean` →
  `PrimitiveHeckeLFunctionsHaveCompletedFunctionalEquation`; imports
  dual averaged Mellin, arithmetic normalization, and completed removable
  values.

Each finished dependency needs an olean only for these already written
consumers. Final source and transitive axiom audits precede finalized
status. All completed scratch files and logs have been removed.

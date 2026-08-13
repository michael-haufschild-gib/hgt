# Five-shift Euler--Gamma submicroscopic separator and critical-kernel source anatomy

- **Stage:** 3-formalized
- **Date:** 2026-08-13
- **Status:** unconditional finite/pointwise theorem; no zeta-density improvement claimed
- **Axioms:** no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration

## Statement

For `r>0`, put

```text
q=e^(-2r),  t=e^(-(6/5)r),  u=e^(-(21/10)r),  x=e^(-2ar),
P_r(a)=x(1-x)(x-t)(x-q)(x-u).
```

The literal prime gap

```text
3/5 < log 2 < 1 < 21/20 < log 3
```

gives one polynomial with four simultaneous properties:

1. `P_r(a)>0` for every zeta displacement `0<a<=1/2`;
2. `P_r(0)=0`, so critical-line diagonal multiplicity is annihilated exactly;
3. `P_r(log n)<=0` for every Euler depth `n>=2`;
4. its coefficients have both zero ordinary sum and zero `e^(-2r)`-weighted sum, cancelling two
   independent Gamma-tail modes.

Functional-equation symmetrization

```text
D_r(a)=-(P_r(a)+P_r(-a))
```

has quadratic contact at `a=0`.  The forced inverse-square normalization satisfies

```text
a^(-2) D_1(a) >= 1/81,       0<a<=1/2,
```

and is totalized to zero at `a=0`.  On every actual strict-right Xi multiplicity copy this is
exactly a weighted combination of five reflection-difference norm squares of exponential Weil
tests.  Hence it lands in the multiplicity-exact negative Weil--Krein sector.

The Hedenmalm critical feature centered at real `t` has the exact kernel

```text
K_t(z)=2/[1+(z-t)^2]
      = i/(z-(t-i)) - i/(z-(t+i)).
```

The poles `t-i` and `t+i` are respectively in Deninger's lower and upper absolute-Euler Cauchy
sectors.  Lean proves:

- lower/upper cross correlations are literal Deninger prime--Gamma source cups;
- lower/lower and upper/upper correlations fold, by oddness of `XiC'/XiC`, into divided
  differences of `primeArchSourceRelativeTrace` at lower absolute-Euler points;
- the complete critical-feature Weil polarization is therefore the sum of four explicit
  absolute-Euler prime--Gamma source expressions.

## Boundary rigidity

The normalized separator is necessarily discontinuous at the critical boundary.  More strongly,
no coefficient continuous at zero, vanishing there, and agreeing with the normalized five-shift
feature throughout `0<a<=1/2` exists.  Thus a successful global landing cannot be a bounded
regular matrix coefficient.  It must use an unbounded inverse-Green/tangent graph, a discontinuous
index channel, or a completed four-leg correlation.

## Lean modules

- `XiWardFiveShiftEulerGammaPrimeGap.lean`
- `XiWardFiveShiftEulerGammaQuantitative.lean`
- `XiWardFiveShiftPairedSubmicroscopicSeparator.lean`
- `XiWardFiveShiftWeilKreinLanding.lean`
- `HedenmalmCriticalFeatureKernel.lean`
- `HedenmalmCriticalFeaturePrimeGammaDecomposition.lean`
- `XiWardFiveShiftCriticalEvaluationLanding.lean`
- `XiWardFiveShiftBoundaryRigidity.lean`

Headline declarations include:

- `fiveShiftEulerGammaFeature_pos`
- `fiveShiftEulerGammaFeature_vonMangoldt_nonpos`
- `fiveShiftEulerGammaPairedRenormalizedFeature_one_ge`
- `fiveShiftEulerGammaRenormalizedKreinDefectCombination_right_ge`
- `criticalEvaluation_criticalFeature_eq`
- `xiWeilPolarization_criticalFeatureCauchyKernelTest_eq_primeGammaSource`
- `not_exists_continuous_boundaryLanding_fiveShiftEulerGamma`

## Exact open core

This formalization does **not** prove `N_0(T)/N(T)>=3/4`, nor any improvement over the external
`0.6725007...` theorem.  Pointwise Euclidean pair-difference energy is the negative Krein sector;
the four-term source formula above is a holomorphic Weil polarization.  A density theorem still
requires an unconditional, height-local Hermitianization/rank--trace estimate that bounds the
five-shift inverse-Green charge by at most `N(T,2T)/8` after its normalization.

The theorem named `fiveShiftCriticalEvaluationEnergyCurrent_vonMangoldt_nonpos` is only a formal
implication under `-Im z=log n`.  Since a critical-rigging evaluation has `|Im z|<1/2` while
`log 2>1/2`, it is not an Euler sampling theorem.  Euler sign is valid for the polynomial/source
symbol; it must not be advertised as a literal strip evaluation.

No novelty claim against published literature is made for partial fractions, functional-equation
folding, or elementary polynomial inequalities.  Corpus contribution is their exact combination
and axiom-clean formal landing at the stated RH-density interface.

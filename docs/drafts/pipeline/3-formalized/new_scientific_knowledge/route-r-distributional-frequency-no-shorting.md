# Route R: scalar distributional frequency separation cannot short the Gamma orbit

- **Stage:** 3 — formalized in Lean 4
- **Status:** `[NO-GO]` with dependency-closed positive survivor
- **Route:** R — primitive-current singular continuation
- **Date:** 2026-08-03

## Frontier question

After unconditional scalar `HasSum` closure, Route R still allowed a
“relative/distribution-valued” source before frequency separation.  This phrase hid two distinct
possibilities:

1. a genuinely pre-frequency relation retaining prime/depth/divisor incidence; or
2. an ordinary scalar distribution already supported on separated modular frequencies.

Only the first can survive.

## Exact theorem

Let `lambda : Nat -> Real` have pointwise isolated range, and let `c : Nat -> Complex`.  Suppose
the scalar spectral distribution vanishes on every smooth compactly supported real test function:

```text
for every phi in C_c^infinity(Real),
  sum'_j c_j phi(lambda_j) = 0.
```

Then every `c_j=0`.  No separate summability premise is needed: existence of the displayed
distributional action is the whole hypothesis.  A bump supported in an isolating neighbourhood of
`lambda_i` and equal to one at `lambda_i` extracts `c_i` exactly.

For canonical cross-prime/depth edges

```text
lambda_(p,e;q,f) = log(p^(e+1) q^(f+1)),  p<q,
```

the spectrum is isolated.  Exponentiation sends it injectively to positive integers, and the
preimage of `(N-1/2,N+1/2)` isolates the frequency `log N`.  Unique factorization gives injectivity.
Multiplication by the actual cooriented Gamma amplitude does not alter the conclusion because that
amplitude is strictly positive.

## Hostile audit

This theorem does **not** prove RH, the Ward sign, or arithmetic annihilation.  It cannot be used
when coefficient evaluation on arbitrary compactly supported tests is unavailable or
discontinuous.  It also does not touch a relation whose coefficients depend on a divisor before
frequency separation.

The underlying distribution fact is classical.  External audit found only standard distribution
theory: Dirac mass is evaluation on smooth compactly supported tests, and distributional support is
defined by local test-function vanishing.  No novelty is claimed for independence of isolated
Dirac masses.  Corpus and targeted external searches found no prior application closing this exact
Route-R loophole.  New content is the canonical prime/depth isolation theorem and its consequence
for the actual cooriented Gamma source.

References used for this audit:

- Encyclopedia of Mathematics, “Dirac delta-function”:
  https://encyclopediaofmath.org/wiki/Dirac_delta-function
- Encyclopedia of Mathematics, “Support of a generalized function”:
  https://encyclopediaofmath.org/wiki/Support_of_a_generalized_function

## Positive survivor

The phrase “distribution-valued” must now be read strictly.  A surviving Route-R producer must do
at least one of the following **before** any scalar distribution on modular frequency exists:

1. remain a relative/operator-valued prime--depth relation whose full compact-test evaluation is
   undefined or discontinuous;
2. use an independently justified source ordering/renormalization not represented by an unordered
   scalar distribution;
3. couple coefficients to Xi-divisor provenance before the fixed-frequency decomposition.

This is stronger than the prior unordered-sum no-go.  Removing positive-real evaluation does not
help once smooth frequency localization is available.

## Lean

Module:

```text
formal/GaloisForLFunctions/RHTower/GammaSignedDistributionalOrbitNoShorting.lean
```

Main unconditional declarations:

```text
isolatedSpectrum_coeff_eq_zero
xiGammaEulerCanonicalCrossPrimeFrequency_isolated
xiGammaEulerCanonicalCrossPrime_distributional_noShorting
xiGammaEulerCanonicalCrossPrimeCooriented_distributional_noShorting
```

The module is imported by `GaloisForLFunctions/RHTower.lean`.


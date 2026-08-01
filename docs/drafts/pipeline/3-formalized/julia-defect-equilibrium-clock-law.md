# Julia defect equilibrium-clock law

- **ID:** `julia-defect-equilibrium-clock-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / SOURCE-SIDE SPECTRAL REPRESENTATION / SHARP NO-GO
- **Statement:** The continuous extension of the normalized Gamma--Julia defect is a
  characteristic function: the compression square is a boundary compound-Poisson law and the
  attenuation kernel is its square-biased triangular equilibrium clock.
- **RH used:** no
- **Computation used:** no

## Goal

Determine whether the universal attenuation profile isolated by the corpus is merely a decreasing
prime weight or carries unapplied positive spectral structure. This question is internal to
HTGeometry; possible use in RHTower was not a selection criterion.

## Corpus synthesis

The proof combines four previously separate HTGeometry mechanisms:

1. `JuliaDefectAttenuation` identifies the compression square and proves strict attenuation.
2. `CoshFourierTransform`, `CoshFourierInversion`, and `GammaCyclicSpectralMeasure` realize
   hyperbolic half-powers as exact Gamma spectral laws.
3. `ConvolutionAtomBounds`, `CompoundPoissonWitnesses`, and
   `LaplaceTransformConvolution` provide the compound-Poisson/infinite-divisibility language.
4. `PrimeDirichletPositiveDefinite` and `UniversalClockSamplingPhaseLaw` provide finite-matrix
   Bochner positivity and characteristic clock transfer.

New result is exact weld among these mechanisms for the Julia profile.

## Statement and complete proof

Put

```text
kappa(y) = cosh(y/2)^2 / sqrt(cosh(2y)),
D(y)     = 1-kappa(y).
```

For `a>0`, standard hyperbolic Lévy--Khintchine identity is

```text
log cosh(a y)
  = integral_0^infinity (1-cos(t y)) /
      (t sinh(pi t/(2a))) dt.                                (JSE1)
```

It follows by differentiating under the integral twice and using value and derivative at zero;
integrand is quadratic at zero and exponentially decaying at infinity.

Hence

```text
-log kappa(y)
  = (1/2)log cosh(2y)-2log cosh(y/2)
  = integral_0^infinity (1-cos(t y)) rho(t) dt,               (JSE2)

rho(t)
  = 1/(2t sinh(pi t/4))-2/(t sinh(pi t)).                    (JSE3)
```

For `t>0`, set `v=pi t/4`. Then

```text
rho(t)
 = [sinh(4v)-4sinh(v)] / [2t sinh(v)sinh(4v)] > 0,            (JSE4)
```

because

```text
sinh(4v)=4sinh(v)cosh(v)cosh(2v)>4sinh(v).
```

Apparent `t^-2` singularities in `(JSE3)` cancel: expansion at zero gives
`rho(t) -> 5pi/16`; tail is exponential. Thus

```text
lambda = integral_0^infinity rho(t) dt < infinity.
```

Riemann--Lebesgue in `(JSE2)` and elementary limit
`kappa(y)->1/(2sqrt(2))` give

```text
lambda = log(2sqrt(2)) = (3/2)log 2.                          (JSE5)
```

Let `Q` be symmetric probability law obtained by normalizing `rho(t)dt` on positive half-line and
adjoining an independent fair sign. Then `(JSE2)` is exactly

```text
kappa(y)=exp(lambda*(char_Q(y)-1)),                            (JSE6)
```

so `kappa` is characteristic function of a symmetric compound-Poisson variable `X`. Law has atom

```text
P(X=0)=exp(-lambda)=1/(2sqrt(2)),                             (JSE7)
```

matching nonzero limit of `kappa` at infinity. This is finite-activity boundary case of
hyperbolic-power infinite-divisibility criterion: numerator and denominator exponential slopes
are exactly equal.

Second logarithmic derivative at zero is

```text
(log kappa)''(0)=2*(1/2)^2-(1/2)*2^2=-3/2.
```

Since `kappa'(0)=0`,

```text
E[X^2]=-kappa''(0)=3/2.                                      (JSE8)
```

Define continuous attenuation extension

```text
R(0)=1,
R(y)=(4/3)*(1-kappa(y))/y^2  for y!=0.                       (JSE9)
```

Let `Xhat` have square-biased law `(2/3)x^2 Law(X)(dx)`, and let `U,V` be independent uniform
variables on `[-1/2,1/2]`, independent of `Xhat`. Identity

```text
(1-cos(xy))/y^2 = (x^2/2)*sinc(xy/2)^2                       (JSE10)
```

and `(JSE8)` give

```text
R(y)
 = E[sinc(Xhat*y/2)^2]
 = E[exp(i y Xhat(U-V))].                                    (JSE11)
```

Therefore `R` is normalized characteristic function. In particular, for every finite real packet
`(a_i)` and complex coefficients `(c_i)`,

```text
sum_i sum_j conj(c_i) R(a_j-a_i) c_j >= 0.                   (JSE12)
```

This supplies joint positive-semidefinite kernel on prime logarithms, not only pointwise
monotonicity of individual prime weights.

## Sharp no-go and positive survivor

Lean's existing

```text
juliaDefectAttenuationProfile(y)=(4/3)D(y)/y^2
```

uses totalized division, so its value at zero is `0`, not `1`. It cannot be positive definite:
two-point packet at times `0,1` with coefficients `1,-1` has quadratic form
`-2*juliaDefectAttenuationProfile(1)<0`.

- **Exact killing mechanism:** raw totalized profile has wrong diagonal value.
- **Strongest positive survivor:** canonical extension `(JSE9)` is characteristic function
  `(JSE11)` and has PSD law `(JSE12)`.
- **New insight:** Julia attenuation is a random equilibrium clock, not merely scalar damping.
  Prime-log attenuation values are one-point shadows of a full covariance kernel.

Separate candidate, complete monotonicity of `R(y)` in aperture `y`, is false. Extended kernel is
even, nonconstant, and has derivative zero at origin. A completely monotone function with that
derivative would have derivative both nonpositive and nondecreasing from zero, hence would be
constant. Complete monotonicity of `R(sqrt(z))` remains unclaimed.

## Novelty audit

- Hyperbolic-secant infinite divisibility, `(JSE1)`, and general operator-mean criteria for ratios
  of hyperbolic cosines are parent mathematics.
- Square-biasing and triangular equilibrium transforms are parent probability theory.
- Exact-form searches found no indexed occurrence of
  `cosh(y/2)^2/sqrt(cosh(2y))` as characteristic function or of its normalized defect as
  equilibrium law `(JSE11)`.
- Candidate-new content is corpus-specific identification of Gamma--Julia compression with
  boundary compound-Poisson law, its exact intensity/atom, and square-biased clock weld. Search
  noncollision is not a priority claim.

Primary external comparisons: Hiai--Kosaki--Petz--Ruskai on positive-definite and infinitely
divisible hyperbolic kernels; classical Schoenberg/Bochner theory; standard hyperbolic-cosine
Lévy--Khintchine formula.

## Lean status

Unconditionally formalized, dependency-closed, and built in:

```text
formal/GaloisForLFunctions/HTGeometry/JuliaDefectSpectralEquilibrium.lean
formal/GaloisForLFunctions/HTGeometry/HyperbolicLevyKhintchine.lean
formal/GaloisForLFunctions/HTGeometry/JuliaDefectLevyKhintchine.lean
formal/GaloisForLFunctions/HTGeometry/CharacteristicEquilibriumDefect.lean
formal/GaloisForLFunctions/HTGeometry/JuliaDefectProfileDerivatives.lean
formal/GaloisForLFunctions/HTGeometry/JuliaDefectEquilibriumPositiveDefinite.lean
```

Load-bearing theorem inventory:

- `log_cosh_eq_hyperbolicLevyIntegral`: `(JSE1)`;
- `neg_log_juliaCompressionSquareProfile_eq_integral`: `(JSE2)`--`(JSE3)`;
- `juliaCompressionLevyDensity_pos`: `(JSE4)`;
- `juliaCompressionLevyDensity_mass`: `(JSE5)`;
- `charFun_juliaCompressionJumpProbabilityMeasure` and
  `charFun_juliaCompressionEquilibriumProbabilityMeasure`: `(JSE6)`;
- `juliaCompressionEquilibriumProbabilityMeasure_zero_mass`: `(JSE7)`;
- `integral_sq_juliaCompressionEquilibriumProbabilityMeasure` and
  `iteratedDeriv_two_juliaCompressionSquareProfile`: `(JSE8)`;
- `normalizedCharacteristicDefect_juliaCompressionEquilibriumProbabilityMeasure`: `(JSE9)`;
- `sq_mul_sinc_sq_eq_normalized_cosDefect`: `(JSE10)`;
- `juliaCompressionSquareBiasedProbabilityMeasure_toMeasure`,
  `integral_sinc_sq_juliaCompressionSquareBiasedProbabilityMeasure`, and
  `charFun_juliaDefectEquilibriumDifferenceProbabilityMeasure`: exact square-biased
  `Xhat * (U - V)` construction `(JSE11)`;
- `positiveDefiniteOnReal_juliaDefectAttenuationKernel`: `(JSE12)`;
- `not_positiveDefiniteOnReal_juliaDefectAttenuationProfile`: sharp raw-profile no-go.

`#print axioms` for every load-bearing theorem reports only `propext`, `Classical.choice`, and
`Quot.sound`; no project axiom, `sorry`, `admit`, `opaque`, or conditional hypothesis remains.

## RH boundary and next risky test

No RH conclusion follows from characteristic-kernel positivity alone. Applied at prime logarithms,
`R(x log p)` gates every `p`-tower by same random scalar; it is not a vertical character on prime
powers because vertical twist would multiply exponent `e`. Next falsifiable question is whether
full Julia Gram kernel `(JSE12)`, rather than its diagonal gate, has an exact source-side action on
reduced first-clock good-minus-bad tower functional. Failure must retain PSD prime-log covariance
theorem as positive survivor.

## Gates

- [x] 0 → 1: well-posed source theorem and exact corpus synthesis
- [x] 1 → 2: dependency-closed paper proof, no RH or numerical input
- [x] 2 → 3: full compound-Poisson and equilibrium-clock identities formalized in Lean
- [ ] 3 → 4: standalone novelty-reviewed preprint

## Log

- 2026-08-01 — Whole-HTGeometry audit exposed Fourier--Gamma, compound-Poisson, Bochner, and clock
  mechanisms previously not applied to Julia attenuation profile. Hostile test killed raw profile
  at zero and produced canonical equilibrium-clock survivor. Paper proof completed; exact density
  positivity and raw-profile no-go formalized.
- 2026-08-01 — Closed `(JSE1)`--`(JSE12)` unconditionally in Lean. Added reusable hyperbolic
  Lévy--Khintchine, square-bias, triangular-difference, atomless-convolution, and equilibrium-clock
  infrastructure. Built leaf modules in foreground and audited load-bearing theorem axioms.

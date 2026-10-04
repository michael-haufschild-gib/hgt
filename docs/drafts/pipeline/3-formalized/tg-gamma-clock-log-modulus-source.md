# TG C9.15: exact Gamma clock symbol and its source normalization

- **ID:** TG-C9.15
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** TG, identification of the Gamma logarithmic-clock source
- **Statement:** For every real xi, the absolutely convergent clock-divided cosine multiplier equals twice the normalized quarter-line Gamma log modulus.

## Corpus basis

`CCMPublishedSourceSineCoefficient` defines the exact density
 gamma(u)=exp(u/2)/(exp(u)-exp(-u)).
`DigammaIntegralRepresentation.digamma_eq_integral_gauss` and
`integrableOn_digammaGaussIntegrand` give the actual Gauss integral and
its absolute integrability for Re z>0.
`GammaXiResponseGapOneCutSpectrum.hasDerivAt_log_norm_Gamma_vertical`
gives the vertical log-norm derivative with no hypothesis beyond Re z>0.
`SoninGammaClockEndpoint` supplies the exact principal/remainder estimate
near clock zero. These are checked corpus statements, not literature inputs.

## Dependency-closed paper proof [PROVED HERE]

Take z=1/4+i xi/2. The imaginary part of the Gauss integrand at 2u is
exactly exp(-u/2) sin(xi u)/(1-exp(-2u))=gamma(u)sin(xi u).
The real e^(-2u)/(2u) counterterm contributes zero to this imaginary part.
Absolute Gauss integrability, real scaling by two and the bounded imaginary
projection therefore give absolute sine integrability and the exact identity

 integral_0^infinity sin(xi u)gamma(u)du = (1/2) Im digamma(1/4+i xi/2).

Define w(u)=u gamma(u) on (0,1/2] and w(u)=gamma(u) on (1/2,infinity).
The C9.14 estimate gamma(u)/u-1/(2u^2)<=5/(2u) bounds w by 2 near zero.
At infinity, gamma(u)<=exp(-u/2)/(1-exp(-1)). Thus w is positive and
integrable on the positive ray.

Define S(xi)=integral_0^infinity 2(cos(xi u)-1)gamma(u)/u du.
The exact cosine half-angle identity and |sin x|<=|x| give
|cos x-1|<=x^2/2. Hence the absolute integrand is bounded by xi^2 w
near zero and 8w on the tail. This proves absolute scalar integrability.
Its xi derivative is -2 sin(xi u)gamma(u). On any bounded xi-neighborhood,
this is bounded by a fixed multiple of w: use |sin(xi u)|<=|xi|u near
zero and |sin(xi u)|<=1 on the tail. Dominated differentiation gives
S'(xi)=-2 integral sin(xi u)gamma(u)du=-Im digamma(1/4+i xi/2).

The corpus vertical log-norm derivative and the chain rule show the same
derivative for G(xi)=2(log||Gamma(1/4+i xi/2)||-log||Gamma(1/4)||).
Both S and G vanish at zero. The derivative of S-G vanishes everywhere
on the real line, so S=G for every real frequency. No frequency sign,
cutoff selection, source estimate, RH premise or meromorphic continuation
hypothesis is added.

## What this closes and what it does not

This identifies the complete scalar multiplier of the explicit C9.14 Gamma
family, including parity, clock factor and normalization at zero. It is a
Gamma log-modulus identity, distinct from the already existing Gamma
phase-rate identity without clock division. Full functional calculus on
the actual Sonin carrier, the homogeneous reference domain, the admitted
remainder response in Schatten one, complete prime/polar assembly,
Hardy compatibility and strict sub-unit control remain separate gaps.

## Lean status

Production leaf `formal/GaloisForLFunctions/RHTower/SoninGammaClockSymbol.lean`
passes `lake --old env lean GaloisForLFunctions/RHTower/SoninGammaClockSymbol.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SoninGammaClockSymbol.olean`.
Exit 0; two nonfatal tactic suggestions, no errors or warnings. All seven public foundation queries in `/tmp/tg-c915-axioms.lean` pass
with only propext, Classical.choice and Quot.sound. No added axioms or holes.
Umbrella wired; index exits 0 and all seven declarations are present.
Global lint exits 1 on thirteen unrelated unreachable leaves; none is this module.
The prior twelve plus `ThetaTailPositiveBalancePrimitive` are listed in
`/tmp/tg-c915-lint.log`. No unrelated leaf was modified. Main result:
`gammaClockSymbol_eq_log_Gamma`, together with `gammaClockSymbol_integrable`.
The two derivative theorems retain the exact actual Gamma sine integral.

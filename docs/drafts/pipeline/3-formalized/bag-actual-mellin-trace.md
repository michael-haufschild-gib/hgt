# BAG actual Mellin traces from common compact log support

2026-10-06,01ax. Dependency-closed paper proof and production closure.
ChiCubicMellinTrace306lines/API2, public234/274. Actual selected trace
scratch78938/log04 terminal0standard3. Production76357/log01emptyPASS with
lake --old env lean and explicit leaf olean, including the full difference
trace. Both imported production axioms43613/log01standard3. Index26282/log01
PASS/API2, RHTower importonce23596, scoped diffcheckPASS. No admissions,
new axioms or resource increases. Authoritative lint38906/log01 terminal1:
362warnings/14unrelated unreachable modules; noownedfinding.
Global lint is NOT clean. Exact errors:
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.KuznetsovBesselIdentity
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergCoefficient
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergFactorization
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergForms
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergGcdLog
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergGcdLogForms
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergRatioForms
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergSummability
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionFarey
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionOffResonance
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionRatioFibers
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionRatioForm
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionResonantBounds
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionSecondMomentExpansion

Logs /tmp/bag-mellin-trace-*01ax.log and compact scratch audit01–04 retained.

New actual-family theorem: every0<theta<1/2 has ONE positive C bounding
(1+|xi0|+|xi1|)^(1+theta)*|Fourier(localizedMellin_sigma f_N)(xi)|
for EVERY sigma in[1,2]^2, EVERY frequency and all sufficiently largeN.
f_N is the literal selected normalized original cone. No Schwartz seminorm
budget, trace regularity or stationary profile is a premise.

Second theorem: for every0<=s<=2, ONE positive constant bounds the weighted
pointwise Fourier norm of the EXACT difference of ANY two localized profiles,
even with different Mellin parameters, by the square root of that difference's
actual weighted Fourier energy. All Schwartz inputs are admitted. This
preserves strong Cauchy control at the shrinking arithmetic axis bands.

Proof. Actual physical localization is supported strictly in(1/8,8)^2.
The exact exponential log chart places all localized profiles in the SAME
closed logarithmic box[-log8,log8]^2. A source-constructed smooth compact
cutoff b equals one on a neighborhood of that entire box; its complexified
Schwartz realization is fixed, independent ofN, parameters and input.
Exact Fourier inversion and literal Schwartz convolution prove
Fourier(F)=Fourier(b)*Fourier(F) for every such localized F.

The complete planar weightw=1+|xi0|+|xi1| is submultiplicative. Its powers
through order4 are dominated by an explicit polynomial in the Euclidean
norm. Native Schwartz decay and polynomial-moment integration admit every
weighted square needed here. Thus both factors are inL2 BEFORE Cauchy is
used. Pointwise weight submultiplicativity, the exact convolution integral,
real Holder at exponent2 and full Haar translation/reflection give
w(x)^s|G(x)| <= sqrt(int w^(2s)|Fourier(b)|^2)*sqrt(int w^(2s)|G|^2).
No slice or convolution integral is totalized without admission.

Applying the already proved actual local energy yields the first public
trace theorem. The difference of two localized profiles is fixed by the
SAME cutoff, irrespective of their parameters, giving the second theorem.
Constants from the fixed cutoff are derived; noN-uniform high derivative
budget is assumed. Pure weightedL2 alone would not imply this trace bound;
common physical log support is the additional proved source structure.

Hard frontier: full source pairing norm on these differences, exterior
pairing vanishing, actual physical Hs Cauchy transfer and fixed-input Mellin
parameter continuity; then signed moving-test cancellation. Native Mellin
lines use2*pi*xi, which must be retained in the arithmetic source and both
dilation Jacobians of the fixed-test law. Full original sharp-action bridge,
growing moments/cofactors/common-height return and RH remain open. Detailed
next proof route P1 bag-moving-mellin-trace-transfer.

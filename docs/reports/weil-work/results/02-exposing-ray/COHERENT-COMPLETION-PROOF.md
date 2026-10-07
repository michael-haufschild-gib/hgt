# Finite coherent completion by a positive geometric filter

Status: dependency-closed paper construction, now Lean-verified as `RHTower.ExposingRayCompletion.bounded_coherent_completion` in module `WeilWorkExposingRayCoherentCompletion`. This proves the finite-mixture version needed by WeilDualBound. The earlier single-test factorization conjecture is stronger and is not claimed proved here.

## Exact source statement

There exist fixed constants C and B such that every X>=4 has a finite nonnegative mixture of actual complex C2 polar tests h_i, all at aperture <=X+B, with

atomCoeff(farPolarTest X,n)+sum_i alpha_i atomCoeff(h_i,n)=0 for EVERY n>=2,

and sum_i alpha_i archEnergy(h_i)<=C. In fact B=17/50 and an exact total-energy identity is available.

## Positive finite filter

Use the existing Fejer profile psi and f_x=farPolarTest x. Choose N=ceil(200X), s=X/N. Then 1/201<=s<=1/200 and Ns=X. Put q=exp(-s/2), A=(1+q^2)/(1+q^(2N)), and for 0<=j,k<N put

w_jk=A q^(j+k), x_jk=(j-k)s, g_jk(u)=f_s(u-x_jk), M=sum_jk w_jk.

Every weight is positive. The finite geometric identity proves

f_X=sum_jk w_jk g_jk.

For the proof it suffices to use its Fourier identity. On the real line let z=exp(i s t). Then

1-cosh(s/2)^(-1)cos(st)=(1-qz)(1-q/z)/(1+q^2).

Multiplying by the two geometric sums (sum_{j<N}(qz)^j)(sum_{k<N}(q/z)^k) produces the analogous multiplier at Ns, with denominator 1+q^(2N). This is finite algebra. It is not an assumed spectral factorization, quadrature limit or numerical approximation.

Moreover

0<M=A(sum_{j<N}q^j)^2<=2/(1-q)^2<=M0,

where M0=2/(1-exp(-1/402))^2 is fixed. This is the critical uniform bound.

## Actual polar completion

Define h_jk=M g_jk-f_X and alpha_jk=w_jk/M. All are actual C2 polar tests: translation, real scaling and subtraction preserve the two zero pole moments. Since |x_jk|<X and f_s has aperture s+17/50, each g_jk and h_jk has aperture at most X+17/50.

Weighted variance gives, for every real t,

|f_X-hat(t)|^2+sum_jk alpha_jk |h_jk-hat(t)|^2=M^2 |f_s-hat(t)|^2.

Here all translates g_jk have the same Fourier modulus and their weighted Fourier mean is f_X-hat. Both sums are finite. The cosine-moment formula consequently gives the identical equation for every actual integer atom. Because 2(s+17/50)<log 2, f_s has ZERO integer trace for all n>=2; hence the completion cancels the entire trace, with no omitted high atoms.

The same identity, integrated against the literal archimedean symbol, yields

E(f_X)+sum_jk alpha_jk E(h_jk)=M^2 E(f_s).

All terms are integrable by actual C2 compact support. No sign of individual energies or of the Weil form is assumed.

## Uniform energy bound

For x>=0, 0<=1/cosh(x/2)<=1. The real multiplier of f_x therefore has absolute value at most 2. Thus |E(f_x)|<=4 Eabs(psi), where Eabs is the existing finite absolute archimedean energy. Consequently

sum_jk alpha_jk E(h_jk)<=4(M0^2+1) Eabs(psi).

This is a fixed upper bound. Total energy remains M^2 E(f_s); no claim that it tends to zero is made. The theorem does not prove PBAP or the exposing-ray lower inequality.

## Attack and significance

This explicitly tests the limitation of the completed X exp(X) box-budget obstruction. Coherent completion uses only finitely many actual polar tests at the original aperture and bounded total repair energy. Its coefficients arise from a positive finite Green filter, not independent atom corrections. Every integer atom is handled by an exact Fourier identity.

The common-profile lattice no-go candidate is not contradicted: these sources use lattice spacing s<1/200, where correlation windows strongly overlap. Their cancellations cannot be isolated one lag at a time as in the widely spaced lattice ansatz.

The earlier differential-majorant regularity concern is resolved at source level: flatBump uses Real.smoothTransition, so its order-2 theorem is a restricted statement, not an intrinsic smoothness limit. Nevertheless the finite-filter construction needs only the existing C2 theorems and bypasses the infinite spectral-factorization infrastructure. Scientific novelty beyond the corpus remains unestablished; the finite geometric/variance mechanisms are classical.

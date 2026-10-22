# Gamma pole-profile boundary integral and actual operator domain

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Modules:** `RHTower.CCMRestrictedWeilGammaPolarBoundary` (10 public theorems, 3 definitions), `RHTower.CCMRestrictedWeilPolarFourierRegularity` (7 public theorems, 1 definition), and `RHTower.CCMRestrictedWeilPolarOperatorDomain` (10 public theorems, 4 definitions); all wired into `RHTower.lean`.
- **Corpus sources:** `CCMActualHeadGammaAutocorrelationEnergy`, `DigammaIntegralRepresentation`, `EulerMascheroniGaussKernel`, `HardyZ`, the actual compression identity in `CCMRestrictedWeilPrimeOuterShell`, `SuzukiApertureFourierDecay`, `SuzukiH01FormDomain`, `CCMArchimedeanLogWeightEquivalence`, and `SuzukiH01OperatorDomain`.

## Full proof chain and boundary
Exact prime–Gamma action → control of constrained ground forcing → exclusion of a zero ground → positive floor at every aperture → weighted pole exclusion → RH. These modules prove the actual translation-increment representative, its complete scalar Gamma integral, and unrestricted Weil operator-domain membership of every truncated real exponential. The exact spectral-plus-bounded operator value is formal. The subsequent [physical-action and source-cancellation theorem](weil-gamma-physical-action-and-pole-source-cancellation.md) identifies that value with the physical logarithmic boundary formula. No RH sign follows from the positive boundary term alone.

## Conjecture loop
1. **Candidate:** the Gamma profile ratio consists of a linear bulk term, the constant `-EulerGamma-log(2pi)`, and two logarithmic endpoint terms.
2. **Pivot in proof method:** separate truncated exponential integrals have divergent origin terms. Retain cancellation through a universal integrable Gauss core instead.
3. **Stronger statement exposed by the decomposition:** that universal core is strictly between zero and one on the positive ray, and the two retained boundary tails are positive. **Proved.**
4. **Source normalization and complete integral:** both predicted constant and boundary formula are verified; the integrand is tied to actual compressed translations. **Proved.**
5. **Domain conjecture:** despite the hard endpoints, every truncated exponential has finite squared exact Gamma-weight energy. Endpoint-retaining Fourier integration by parts and the corpus square-logarithmic envelope theorem prove this. **Proved.**
6. **Operator-domain conjecture:** spectral regularity can be lifted to the actual unrestricted Weil Friedrichs domain. Construct the literal weighted form vector, compress the Fourier multiplier representative, and add the exact bounded remainder. **Proved.**
7. **Physical identification:** the pointwise boundary integral equals the constructed actual operator representative. This is proved in the subsequent physical-action card by an absolute mixed-integral bound, compact-test Fubini, and locally integrable smooth-test separation.

## Dependency-closed paper proof [PROVED HERE]
Put

`rho(h)=exp(-h/2)/(1-exp(-2h))`,

`g(h)=exp(-h)/(1-exp(-h))`,

`C(h)=2rho(h)-g(h)`.

For `h>0`, let `t=exp(-h/2)`, so `0<t<1`. Algebra gives

`C(h)=t(t²+t+2)/[(1+t)(1+t²)]`.

Its numerator is positive and the denominator minus numerator is `1-t`, hence `0<C(h)<1`.

Let `K_s(t)=(exp(-t)-exp(-st))/(1-exp(-t))`, the real Gauss difference. The corpus proves its absolute integrability and integral `digamma(s)+EulerGamma` for real `s>0`. The exact identity

`C(h)=-2K_(1/4)(2h)+K_(1/2)(2h)`

therefore proves absolute integrability of `C`. Substitution and the current exact digamma-half value give

`integral_0^infinity C(h) dh = -Re digamma(1/4)-EulerGamma-log 2`.

For positive endpoint distances `R,L`, define the literal pole-profile jump ratio

`J(R,L,h)=rho(h)[2-exp(h/2)1_{h≤R}-exp(-h/2)1_{h≤L}]`.

The exact positive-ray decomposition is

`J=C-1_{h≤R}+1_{h>R}g(2h)+1_{h>L}[g(h)-g(2h)]`.

Every displayed term is absolutely integrable on the positive ray: the indicator has finite length, the core is already integrable, and each tail starts at a strictly positive endpoint. The existing geometric Gauss tail formula supplies

`integral_R^infinity g(2h) dh = -(1/2)log(1-exp(-2R))`,

`integral_L^infinity [g(h)-g(2h)] dh = -log(1-exp(-L))+(1/2)log(1-exp(-2L))`.

Writing their sum as `B(R,L)`, exponential factorization proves

`B(R,L)=-(1/2)log(1-exp(-2R))-(1/2)log(tanh(L/2))>0`.

The normalization in the actual corpus is

`2 gammaHardyPhaseRate(0)=Re digamma(1/4)-log pi`.

Consequently the complete source integral is

`2 gammaHardyPhaseRate(0)+integral_0^infinity J(R,L,h) dh`

`= -R-EulerGamma-log(2pi)+B(R,L)`.

No divergent integral is evaluated separately, and no numerical constant or asymptotic estimate is inserted.

## Exact source connection
Let `p+(x)=1_{[-a,a]}exp(x/2)` and `S_h` be the actual compressed symmetric translation. For every `h>0`, `ccmGammaPolarJump_source_coeFn` proves the almost-everywhere identity

`rho(h)(2p+-S_h p+)(x)=1_{[-a,a]}exp(x/2)J(a-x,a+x,h)`.

Thus the kernel is the representative of the literal source increment, not an unrelated positive model. At strict interior points, both endpoint distances are positive and the integral theorem applies. This statement has quantifier order `for every h, almost every x`; the subsequent physical-action card supplies the joint measurability, absolute integrability, and compact-test interchange needed for operator identification.

## Dependency-closed spectral and operator-domain proof [PROVED HERE]
For any real slope `s`, let `p_s=1_{[-a,a]}exp(sx)` and let `F_s` be its classical Fourier transform. The compact profile is integrable. Exact interval Fourier compatibility and integration by parts give

`|F_s(xi)| ≤ min(C_s,M_s/|xi|)` for `xi≠0`,

where `C_s` is the profile's interval L¹ norm and `2pi M_s` is the sum of both endpoint norms and the interval L¹ norm of its derivative. No zero endpoint value is assumed. The corpus general-envelope theorem gives

`integral suzukiLogWeight(xi)^2 |F_s(xi)|^2 dxi < infinity`.

The global exact-weight comparison then gives `integral W^2 |F_s|^2 < infinity`, with `W=ccmArchimedeanFormWeight≥1`. The L¹/L² Fourier compatibility theorem identifies `F_s` almost everywhere with the actual unitary Fourier transform of `ccmPolarL2Vector a s`, so this proves regularity of the literal vector.

Since `W≤W²`, the same transform belongs to `L²(W dxi)`. Define its canonical weighted vector and prove that forgetting the weight gives the actual unitary Fourier transform. Fourier inversion recovers precisely `p_s`; the existing support projection identity therefore puts this vector in `CCMArchimedeanFormDomain a`.

The product `W F_s` belongs to ordinary L². Its inverse unitary Fourier transform represents the complete weighted form pairing, by `inner_ccmArchimedeanOperatorRepresentative`. Adjoint compression to the aperture yields `ccmPolarArchimedeanRepresentative`. Adding the literal `ccmRestrictedWeilBoundedRemainder` gives `ccmPolarWeilRepresentative`, representing the full restricted Weil form against every complete form-domain vector. The generic converse representation theorem now gives

`p_s in domain(ccmRestrictedWeilOperator a)`,

`ccmRestrictedWeilOperator a p_s = ccmPolarWeilRepresentative a s`.

These are unconditional for every positive aperture and every real slope. The archimedean representative here uses the shifted weight `W`; the fixed scalar in the bounded remainder restores the actual Gamma symbol. No RH premise, smooth endpoint replacement, or numerical certificate enters the proof. The subsequent physical-action card identifies the explicit logarithmic coefficient with this representative and combines the full prime, polar, and Gamma actions.

## Verification
- Scratch `lake env lean /tmp/hgt-gamma-pole.6YS4omj7/Final.lean`: PASS.
- Named final audit `lake --old --log-level=error build GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGammaPolarBoundary`: PASS (14 seconds).
- Scratch `Audit.lean`: all 10 public theorems use exactly `[propext, Classical.choice, Quot.sound]`; actual mathlib `RiemannHypothesis` printed.
- Scratch `PoleDomain.lean` and `Friedrichs.lean`: PASS with `lake env lean`.
- Named final audits of `CCMRestrictedWeilPolarFourierRegularity` and `CCMRestrictedWeilPolarOperatorDomain`: PASS (8.5 and 6.0 seconds).
- Scratch `DomainAudit.lean`: all 7 public theorems use exactly `[propext, Classical.choice, Quot.sound]`; actual mathlib RH printed.
- Scratch `FriedrichsAudit.lean`: all 10 public theorems use exactly `[propext, Classical.choice, Quot.sound]`; actual mathlib RH printed.
- `git diff --check`: PASS.
- Final `python3 scripts/formal_tools.py lint`: PASS (`formal lint passed`); existing large-file warnings remain. The concurrent quartic Jensen umbrella gap was resolved before the final gate.
- All owned Lean/build processes are terminal. No full or umbrella build, numerical experiment, computational oracle, or added axiom.

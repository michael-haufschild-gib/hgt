# HB: native principal integrals equal the physical causal responses

Status: the original native response equals `principalTimeResponse` in all three principal channels. Complete angular inverse identification, physical current extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target remains `2 Omega(B(p,p)/2,B(m,m)/2)=0`, with independent SS/SV/VV amplitudes and every onset, horizon, AdS, temporal and cusp current. This result closes the principal-channel identification needed to compare the native full-source inverse with the physical response entering that pairing.

## Exact result

Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativePhysicalIdentification`. Namespace: `RHTower.D4BMNativeResponse`.

`nativePrincipalResponse_eq_principalTimeResponse` proves, for the original `q`, branch, source amplitude and each `i : Fin 3`, equality of the entire time-dependent L² functions:

```
principalAmplitude(q,i) •
  radialResponseVector(-principalExponent(q,i),physicalRate(q,branch),a)
  = principalTimeResponse(q,branch,a,i).
```

Both sides are the existing constructed objects. The theorem has no inverse-identification, weak-source-equation, domain-admission or nonvanishing assumption. Every time is included, including the source onset and negative times. It preserves all three original complex exponents, amplitudes and forcing coefficients. This is an equality of principal responses; it does not assert equality of the complete angular responses.

## Proof mechanism

Set `m=2*pi`. Define the zero-mass sine multiplier at frequency `xi` by `t*sinc(2*pi*t*xi)`. Its value at zero frequency is `t`. The physical `unitWaveSine` has multiplier `t*sinc(2*pi*t*sqrt(1+xi^2))`, with its original normalization. The frequencies therefore satisfy `Omega^2-omega^2=m^2` exactly.

For `s_omega(t)=t*sinc(t*omega)`, differentiate

```
W(t)=cos(Omega*(T-t))*s_omega(t)
     +s_Omega(T-t)*cos(omega*t).
```

Its derivative is `(Omega^2-omega^2)*s_Omega(T-t)*s_omega(t)`. Its endpoint difference is `s_omega(T)-s_Omega(T)`. FTC proves the scalar mass identity for all real frequencies, including zero. Multiplier norm bounds and Fubini against arbitrary L² inner-product test vectors lift this identity to the actual Fourier L² space:

```
S0(T)f = Sm(T)f + m^2 integral_0^T Sm(T-t)S0(t)f dt, T>=0.
```

This is `freeWaveSine_mass_conversion`. The multiplier integral interchange is proved; no interchange or spectral endpoint identity is assumed.

The original translation/Fourier exchange and the symmetric exponential integral give

```
S0(T)f = (1/2) integral_-T^T translateL2(t)f dt, T>=0.
```

`freeWaveSine_translation` proves this as a Bochner integral in L². A private representative theorem passes continuous scalar families through L² integrals by testing against every L² vector. Product integrability follows from the actual slice representatives and the bound `|inner(g,u)| <= |g|^2+|u|^2`; the integrals of those squares are the exact L² norms. For continuous compactly supported data this identifies the representative with `1/2 integral_(x-T)^(x+T) f(y) dy`. No point evaluator on L² is used.

Define `D0 F(T)=integral_0^T S0(T-t)F(t) dt`. Integrating the sine identity and reversing the causal integration triangle proves

```
D0 F(T)=Dm F(T)+m^2 Dm(D0 F)(T), T>=0,
```

for every continuous L² source. This is `freeWaveDuhamel_mass_conversion`. The Bochner triangle interchange retains the jointly dependent integrand, and the time shift is proved exactly.

The prior scalar native source equation now passes through the representative theorem to give, in the actual L² space,

```
U=D0 G,
G=F+P U-m^2 U,
P(x)=m^2+alpha(alpha-1)/cosh(x)^2.
```

The proof identifies `G` with the original forcing plus the original potential using `principalForcing_ae_oddSource`, `principalWavePotentialOp_ae` and the actual native representative. Continuity, compact spatial support on each required slice, and zero response before onset are discharged. Mass conversion gives `U=Dm F+Dm(P U)` for nonnegative time; zero onset gives the same identity for negative time. The existing `principalTimeResponse_unique` then proves the displayed function equality for every principal channel.

## Remaining hard step

The native cutoff-subtracted full angular response must still be admitted to the original joint wave domain, with modular side identifications, cusp control and the physical Dirichlet trace. Its forced equation and zero initial data must be matched to `causalJointForcedResponse`. The principal coefficients in that comparison are now identified. The complete physical current pairing still requires evaluation with all boundary currents retained. RH is not proved by the present theorem.

## Search and audit

Broad `sinc`, convolution and shifted-frequency searches and deep interval/Fourier and Bochner-representative searches exposed the symmetric exponential integral, translation-modulation exchange, multiplier continuity and Fubini arguments used here. The shifted massive identification had a strict parameter bound and did not cover the zero-mass endpoint; the direct Wronskian supplies that endpoint. The generated representative ingredient group did not prove L² integral interchange, so the exact inner-product proof was built.

Candidate declarations, source arguments and generated ingredient groups were inspected. The final deep search inventoried 55,972 files with complete file inventory but incomplete semantic coverage, 48 compiled snapshots and 43 stale snapshots; candidates were predominantly source-only. Every ingredient used in this leaf was checked by Lean.

Foreground scratch `lake env lean` passed. The final audit ran only `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativePhysicalIdentification`, using 4038 frozen own-module caches and 11 package caches. The 864-line new leaf built in 45 seconds; Lake reported three jobs. No old dependency, full or umbrella build ran. Lean emitted one informational `ring_nf` suggestion; the build completed successfully.

Only the four new public theorems received `#print axioms` checks. Each reports exactly `propext`, `Classical.choice`, and `Quot.sound`. All six installed source/artifact files match the audited files byte for byte. A unique import was added to the `GaloisForLFunctions.RHTower` area umbrella; the umbrella was not built.

Global formal lint passed with the existing corpus file-size warnings. The module-filtered lexical search returned all four public theorems. The inverse-identification card records the closed principal comparison and the remaining full angular residual. The frontier map and route-independent STATUS ledger were unchanged. No mathematical computations ran.

All owned Lean/Lake, search and lint processes completed. Scratch files and the frozen audit tree were removed.


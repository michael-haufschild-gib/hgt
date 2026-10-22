# HB: native forced integral in the original L² space

Status: 11 public theorems formalized and audited. Equality with the existing causal evolution, complete physical current extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target remains `2 Omega(B(p,p)/2,B(m,m)/2)=0`, with independent SS/SV/VV amplitudes and all physical boundary currents. This result constructs the actual principal integrals whose comparison with the physical evolution is needed in that pairing.

## Exact construction

Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeForcedIntegral`. Namespace: `RHTower.D4BMNativeResponse`.

The actual reduced source satisfies `timeReducedCoefficient(s,a,tau,0)=0` for every complex `s,a` and every real time. The proof evaluates the original radial polynomials and lift at their endpoint. Hence its continuous odd representative is exactly

```
F(s,a,tau,x)=b(s,a,tau,min(x,0))-b(s,a,tau,min(-x,0)).
```

This keeps the original onset and its derivative. It equals the original source on the negative ray and vanishes for `|x|>max(tau,0)`. In particular, the actual source has no jump at its odd-extension endpoint; higher spatial regularity is not asserted by this result.

Write `T=max(tau,0)` and let `R_nu` be the existing Gauss Riemann kernel. The constructed function is

```
U_nu(tau,x)=T²/2 integral_0^1 (1-r) integral_-1^1
  R_nu(T(1-r),x,x+T(1-r)z) F(s,a,T r,x+T(1-r)z) dz dr.
```

Every integrated point lies on its original causal cone. Two affine integral substitutions prove the exact retarded formula

```
U_nu(tau,x)=1/2 integral_0^T integral_(x-(T-sigma))^(x+(T-sigma))
  R_nu(T-sigma,x,y) F(s,a,sigma,y) dy dsigma.
```

The normalization and both Jacobians are part of the Lean equality, including `T=0`. A private continuous extension `P_nu(max(1,Z))` is used only to prove continuity; it equals the original kernel at every integrated point.

## Proved properties

The public theorems establish the endpoint source identity; joint continuity of `U_nu`; zero response at nonpositive times; support in `|x|<=T`; membership of each slice in the actual whole-line `Lp ℂ 2 volume`; the exact retarded formula; oddness and zero Dirichlet trace; and strong L² continuity in time.

Strong continuity uses a common compact spatial support on each bounded time interval. Joint continuity supplies a common finite bound there. The existing dominated-L² continuity theorem then applies to a locally clamped time family, which agrees with the original family near the chosen time. This proves norm continuity without a hypothetical global bound in time.

`principalForcing_ae_oddSource` proves that `principalAmplitude q i * F(physicalRate q branch,a,tau,x)` represents the existing `principalTimeForcing q branch a i tau` almost everywhere. `nativePrincipalResponse` uses this exact amplitude and physical rate, and degree `-principalExponent q i`, for each of the three original channels. Its strong continuity is proved. No equality with `principalTimeResponse` is asserted.

## Remaining mathematical obligation

The [comparison card](../1-in-progress/hb-native-cusp-inverse-identification.md) records the exact weak-source calculation and the operator comparison. The kernel's already proved characteristic identity must be integrated against this original forcing with the source vertex retained. One must then derive the original Duhamel equation, including the free mass `2*pi`, or prove an equivalent uniqueness statement with its hypotheses discharged. For the complete angular response, the original modular domain and boundary admission remain necessary. The complete physical current still has to be evaluated.

## Validation

Foreground scratch `lake env lean` passed without warnings. The final audit ran only `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeForcedIntegral`, with 4028 frozen own-module caches and 11 package caches. The new leaf built in 50 seconds; Lake reported three jobs. No old dependency, full or umbrella build ran.

Only the 11 new public theorems received `#print axioms` checks. Each reports exactly `propext`, `Classical.choice`, and `Quot.sound`. All six installed source/artifact files match the audited files byte for byte. The unique import is in the `GaloisForLFunctions.RHTower` area umbrella; no umbrella build ran.

Global formal lint passed. The module-filtered lexical corpus search returned all 11 public theorems. The frontier map and route-independent STATUS ledger were unchanged. No mathematical computations ran.

All owned Lean/Lake, search and lint processes completed. Scratch files and the frozen audit tree were removed.

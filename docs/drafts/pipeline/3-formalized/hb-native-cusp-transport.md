# HB: exact native cusp transport

Status: five public theorems formalized. Native/physical inverse identification, full physical-current extinction and RH remain unproved.

For the actual complete theta half-square `Q` at any Xi occurrence, retain all three original cusp powers and completed amplitudes:

```
alpha=(2rho,1,2-2rho),  A=(a^2/2,ab,b^2/2).
P_alpha(d)=average_theta (cosh(d)-sinh(d)cos(theta))^(-alpha).
```

The new leaf proves the exact native mean expansion

```
mean(Q,d,X,log Y)=sum_i A_i Y^(alpha_i) P_(alpha_i)(d)
                  +average_theta (squareRemainder(circle)/2).
```

For every natural `N`, a nonnegative constant depending only on the occurrence and `N` bounds the full remaining mean by `C exp(Nd)/Y^N` whenever `d>=0` and `Y>=exp(d)`. The entire signed Fourier remainder remains. No supplied decay premise or angular projection enters the proof.

For each fixed nonnegative radius, the native mean minus its transported principal sum times the original modular cutoff belongs to the original modular L² space. Continuity controls the compact lower cell; the uniform tail estimate controls the high cusp. This is admission of the actual value function, not joint operator-domain membership.

## Lean statements

Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCuspTransport`.
Namespace: `RHTower.D4BMNativeCircle`.

- `mean_cusp_expansion`: exact complete-source expansion.
- `cuspMeanRemainder_integral`: the difference equals the original remainder integral.
- `cuspMeanRemainder_rapid_bound`: every inverse-height decay order, with explicit radius dependence.
- `mean_base_continuous`: continuity in the original upper-half-plane basepoint.
- `nativeCutoffResidual_memLp`: original cutoff-subtracted mean is in modular L².

## Connection to the physical inverse

The identity `P_alpha(d)=legendreKernel(-alpha,cosh(d))` is now [formalized separately](hb-native-circle-gauss.md), including the full-source three-channel expansion. The [comparison card](../1-in-progress/hb-native-cusp-inverse-identification.md) also derives the residual wave forcing as the original square residual plus all three cutoff commutators, and gives a sharper principal-kernel bound and a finite-time Duhamel comparison argument. Those further equations are paper work. Matching the principal causal integrals, proving the complete native response's joint-domain membership and boundary traces, and evaluating the complete physical pairing remain necessary.

## Validation

Foreground `lake env lean` scratch check passed. Final audit ran only `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCuspTransport`: 16 seconds, three jobs, with 3943 existing own-module caches and 11 package caches frozen. No old dependency, full or umbrella build ran.

Only the five new public theorems received `#print axioms` checks. Each reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The six installed source/artifact files match the audited files byte for byte. The umbrella contains one new import and was not built.

`scripts/formal_tools.py lint` passed with existing large-file warnings. Module-filtered lexical research returned all five public theorems. The frontier map and universal ledger were not edited. No mathematical computation ran.

The proposed complex binomial-series APIs also passed a separate `lake env lean` scratch check, including specialization to the required complex exponent. All owned Lean/Lake processes completed; the scratch and frozen audit tree were removed.

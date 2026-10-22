# HB: native elliptic L2 admission and exact energy localization

Stage: 3-formalized. Six new public theorems close actual joint-L2 admission of the native time primitive and complete elliptic forcing, exact compact angular energy localization, and vanishing of both joint cutoff-gradient errors. The joint radial/angular energy identity, native form-domain admission, complete physical inverse identification, physical-current extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target remains cancellation of the complete physical current with independent SS/SV/VV amplitudes. These results advance the [native elliptic energy construction](../1-in-progress/hb-native-cusp-inverse-identification.md#native-elliptic-energy-construction) needed to identify the complete native and constructed physical evolutions.

## Actual L2 fields

The declarations in [ThetaCuspHawkingBMNativeResidualAdmission.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMNativeResidualAdmission.lean) use the original product of radial measure on `x<0` and angular measure on the modular fundamental cell. Write

```
W(t,x,z) = integral_0^t (t-u) nativeResidual(u,x,z) du,
Fint(t,x,z) = integral_0^t (t-u) nativeResidualStaticForcing(u,x,z) du,
G(t,x,z) = Fint(t,x,z) - nativeResidual(t,x,z).
```

For every native `q`, arbitrary complex `s,amplitude`, and real `t`, the following are closed without energy, regularity, frequency-chamber or field-equation premises:

| Declaration | Result |
| --- | --- |
| `nativeJointTimePrimitiveField_memLp` | `W` belongs to the original joint L2 space. |
| `nativeJointIntegratedForcing_memLp` | The full `Fint` belongs to that same space. |
| `nativeJointEllipticForcing_memLp` | The actual right-hand side `G` belongs to that same space. |

The existing uniform bounded-time majorant for the native residual bounds the primitive by `2 abs(t)^2` times that majorant. This gives the first result. For the forcing, define the actual radial coefficients

```
h(t,x) = integral_0^t (t-u) oddSource(u,x) du,
p_i(t,x) = integral_0^t (t-u) A_i radialResponse(-alpha_i,u,x)/cosh(x)^2 du.
```

The proof establishes the exact identity

```
Fint(t,x,z) = h(t,x) squareResidual(z)
             + sum_(i : Fin 3) p_i(t,x) cutoffCommutator(alpha_i,z).
```

Continuity and finite causal support make each radial coefficient L2. The actual angular residual and all three cutoff commutators already have L2 admission; the separated-product theorem and finite addition give the full forcing. No principal amplitude is deleted. Subtracting the admitted native residual gives `G`. The prior pointwise theorem `nativeResidualTimePrimitive_elliptic_equation` identifies this exact `G` with `A W`, where `A=-partial_x^2-sech(x)^2 Delta_H`.

## Exact angular localization and escaping error

The new [ThetaCuspHawkingBMNativeAngularLocalization.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMNativeAngularLocalization.lean) uses the actual global native primitive, its original complete modular germs, and `eta_N=modularCuspCutoff(n+1)`.

`nativeTimePrimitive_compact_angular_localization` proves, at each real radial coordinate,

```
integral_fd abs(grad_H(eta_N W))^2
  = -Re integral_fd conj(Delta_H W) eta_N^2 W
    + integral_fd abs(W grad_H eta_N)^2.
```

Both the cutoff energy and the nonnegative error are integrable in the original angular measure. The proof applies the full product rule to `eta_N W` and `eta_N^2 W`. Reality of the actual cutoff lets their real cross terms recombine exactly. Existing native compact Green then supplies the equation. Integrability of the error follows from the pointwise difference of the two already-integrable energy pairings. No global native gradient estimate is supplied.

`nativeJointCutoffError` is the original product-space function

```
err_N(x,z) = sum_(i : Fin 2) abs(D_i eta_N(z) W(t,x,z))^2,
D_0 = weightedDeriv 1, D_1 = weightedDeriv I.
```

| Declaration | Result |
| --- | --- |
| `nativeJointCutoffError_tendsto_zero` | Every `err_N` is integrable and its joint integral tends to zero. |
| `nativeJointCutoffError_weighted_tendsto_zero` | Every `sech(x)^2 err_N` is integrable and its joint integral tends to zero. |

The complete cutoff germ gives the actual frame formula on the original cell. The horizontal derivative is zero; the vertical derivative is `y eta_N'(y)`. Its established scale-independent bound gives `err_N <= C^2 abs(W)^2`. Each point eventually lies in the region where the entire cutoff germ is one, so the derivative error eventually vanishes. Dominated convergence uses the newly proved native L2 admission. Finally `0<=sech(x)^2<=1` supplies the physical weighted result by integral comparison and squeezing.

## Surviving construction target

The precise stronger joint target is

```
F_N = Re integral eta_N^2 conj(W) G + integral sech(x)^2 err_N,
F_N = integral (abs(partial_x(eta_N W))^2
                 + sech(x)^2 abs(grad_H(eta_N W))^2).
```

Combining the angular identity with the actual radial Green identity and elliptic equation still requires joint integrability and the radial/angular integral interchange for the original derivative fields. Once proved, Cauchy-Schwarz would give `F_N <= norm(W)_2 norm(G)_2 + integral sech(x)^2 err_N`. The error limit is now closed. Fatou would give finite native gradient energy; then cutoff-gradient convergence and the forcing-pairing limit would give the exact global energy identity. First-derivative graph approximation, native joint-domain admission and the bounded-resolvent identity remain to be constructed.

## Discovery and applicability

Own broad corpus terms were `Caccioppoli`, `Minkowski`, `regularization` and `IMS`. Deep mechanism searches tested cutoff/Fatou energy admission and angular-resolvent regularization. Candidate statements, source methods and proposed ingredient groups were inspected. Search outputs were partial, with predominantly source-only compiler metadata, incomplete semantic coverage, and deadline-limited deep results. No proposed group supplied the native estimate. The `IMSLocalizationWeilForm` corpus argument suggested exact recombination of localization cross terms; its convolution identity was not applied as a differential identity. The actual hyperbolic product rule, compact native Green identity and native L2 source assembly were checked in this toolchain.

Own broad arXiv terms were `exhaustion` and `coercivity`, using newest-first results. [Li, 8 September 2026](https://arxiv.org/html/2609.08255v1), proves a coercivity-threshold residual bound using a forced Helmholtz circle mean and a sphere constraint. That constraint is not established for the native field, so the paper supplies no admission theorem here. [Jakobsen et al., 7 September 2026](https://arxiv.org/html/2609.07388v1), separates conservative and dissipative couplings in a poroelastic system and derives their adjoints with boundary terms accounted for. This supported examining the exact mixed-term algebra; neither paper is a premise in Lean.

## Validation

- Both scratch files passed with `lake env lean`, without warnings.
- Final targeted build of `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeResidualAdmission`: 163 seconds, two jobs, 4099 cached local dependencies and 11 cached dependency packages.
- Final targeted build of `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeAngularLocalization`: 97 seconds, two jobs, 4133 cached local dependencies and the same 11 dependency packages.
- Neither audit rebuilt an old dependency or umbrella. Each used an isolated audit root containing only its target source and cached dependencies.
- Only the six new public theorems were checked with `#print axioms`; each uses only `propext`, `Classical.choice`, `Quot.sound`.
- Audited source and all five emitted artifacts per target were installed byte for byte. The existing module was protected by an original-source equality check; the new module by a destination-absence check.
- `scripts/formal_tools.py lint` passed with existing large-file warnings.
- The new module is wired into `formal/GaloisForLFunctions/RHTower.lean`; that umbrella was not built. Frontier map and universal-law ledger were not modified.
- Owned scratch files, search outputs and process handles were cleaned up. No mathematical computation or external numerical result enters either proof.

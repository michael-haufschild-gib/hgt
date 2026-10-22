# HB: exact native joint cutoff energy

Stage: 3-formalized. Six public theorems close the exact joint cutoff energy identity for the literal native time primitive in the original radial/modular measure. Global native gradient energy and the exact global identity are now [formalized separately](hb-native-global-energy.md). Form-domain admission, complete physical inverse identification, physical-current extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target remains cancellation of the complete physical current with independent SS/SV/VV amplitudes. This construction attacks the native energy-domain admission needed to identify the complete native and constructed physical evolutions. It is part of the [native elliptic energy construction](../1-in-progress/hb-native-cusp-inverse-identification.md#native-elliptic-energy-construction).


The new public declarations are:

| Module | Declaration | Result |
| --- | --- | --- |
| [FullNativeWave](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMFullNativeWave.lean) | `nativeResidualTimePrimitive_radial_hasDerivAt` | Actual radial first and second derivatives everywhere. |
| FullNativeWave | `nativeResidualTimePrimitive_joint_spatial_jets` | Joint continuity of the value and six pure spatial derivatives. |
| [NativeJointEnergy](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMNativeJointEnergy.lean) | `nativeTimePrimitive_frame_derivatives` | Both original hyperbolic frame derivatives on the closed cell. |
| NativeJointEnergy | `nativeTimePrimitive_chart_laplacian` | Exact original chart Laplacian in log-height coordinates. |
| NativeJointEnergy | `nativeTimePrimitive_original_elliptic_equation` | Original operator applied to the native primitive equals complete forcing. |
| NativeJointEnergy | `nativeTimePrimitive_compact_joint_energy` | Joint integrability and the exact cutoff energy identity. |

## Exact fields and operator

Write `W` for `nativeResidualTimePrimitive`, `G` for the already admitted `nativeJointEllipticForcing`, `k=log(y)`, and `eta=modularCuspCutoff(n+1)`. All product integrals use radial measure on `x<0` and angular measure on the original closed modular cell. `G` retains the complete time-integrated forcing, including all three principal cutoff commutators, minus the native residual.

The actual frame derivatives and chart Laplacian satisfy, on the entire closed cell,

```
D_0 W = y W_X,
D_1 W = W_k,
Delta_H W = y^2 W_XX + W_kk - W_k,
-W_xx - sech(x)^2 Delta_H W = G.
```

These identities use the actual native angular smoothness and full modular germs. The second derivative of `f(log y)` is `(f''(log y)-f'(log y))/y^2`; the first-derivative term is retained. Entire germs transfer the two directional derivatives and their second derivatives across every seam. No equation for a surrogate chart field is substituted for the original operator.

## Joint regularity and compact integrability

The extension of `ThetaCuspHawkingBMFullNativeWave.lean` proves actual radial first and second derivative existence and joint continuity of seven fields: `W`, `W_x`, `W_xx`, `W_X`, `W_XX`, `W_k`, `W_kk`. Joint continuity includes time, radius, horizontal coordinate and logarithmic height. It does not assert mixed spatial/time derivatives.

The explicit full response jets and both height jets already have joint continuity in the corpus. Their weighted time integrals give the angular derivatives. The exact radial equation gives continuity of `W_xx`. Outside the causal support, `W_x` is zero. Integrating `W_xx` from the exterior basepoint `-max(t,0)-1` then gives joint continuity of `W_x` without assuming a mixed derivative.

For each finite cutoff the relevant original derivative fields have continuous representatives on the product coordinates. On the original measure their support lies in

```
[-max(t,0)-1,0] × {z in fd : im(z) <= 3(n+1)}.
```

This is compact. Finite causal propagation supplies the left support bound for the value and all first derivatives used in the energy. The cutoff's full zero germ supplies both its value and derivative support bounds in the high cusp. A compact indicator therefore proves actual joint integrability of both energies and the two Green pairings. Fubini is used only after these product-measure hypotheses are proved.

## Exact energy identity

Define the original cutoff contributions

```
R_n(x,z) = abs(eta(z) W_x(t,x,z))^2,
A_n(x,z) = sech(x)^2 sum_i abs(D_i(eta W)(t,x,z))^2,
err_n(x,z) = sum_i abs(D_i eta(z) W(t,x,z))^2.
```

`nativeTimePrimitive_compact_joint_energy` proves integrability of `R_n`, `A_n` and the complete forcing pairing, and the exact identity

```
integral (R_n+A_n)
  = Re integral conj(G) eta^2 W
    + integral sech(x)^2 err_n.
```

Because `eta` is real, the real forcing pairing equals `Re integral eta^2 conj(W) G`. This is the joint localization identity, including every product-rule term.

For the radial contribution, the actual trace at zero and finite causal support make both endpoint products vanish. The previously proved interval Green identity transfers to the original negative-half-line measure. For the angular contribution, the already proved compact modular localization identity keeps the full cutoff-gradient error. Joint integrability then permits the required opposite integral orders. The actual elliptic equation combines the two real Green pairings into the complete forcing pairing. The previously audited physical weighted error integral tends to zero.

## Remaining construction

The [global energy construction](hb-native-global-energy.md) proves integrability of the actual gradient density and its exact identity with the complete source-response pairing. Dominated convergence handles the forcing pairing; two Fatou passes establish finiteness and exclude an escaping energy defect using the full cutoff error.

The original first-derivative graph admission remains open. Each fixed cusp cutoff already gives an actual angular `CoreField`. Continuity in the angular energy space, zero extension at the proved Dirichlet trace, a negative radial shift and radial mollification should construct the smooth families accepted by `RadialEnergyFamily.graph_mem`. Convergence of the original value and radial/angular gradients must still be formalized. The bounded-resolvent identity and complete current cancellation remain later obligations.

## Search and proof choices

Own broad corpus terms included `Fubini`, `logarithmic`, `Fatou` and `relaxation`; deep mechanism searches examined parameter derivatives of compact integrals and joint elliptic Green integration. Candidate lemmas, source methods, proposed proof ideas, ingredient groups and freshness metadata were inspected. Results were partial with predominantly source-only compiler metadata and incomplete semantic coverage. No proposed ingredient group was assumed valid.

A generic new joint smoothness construction was abandoned before implementation after source inspection found the stronger applicable response-jet continuity already present in `FullNativeWave`. Its actual derivative formulas closed the needed pure jets. The original chart calculation was then proved directly. The `DiskSmirnovRadialL1` method supplies a concrete Fatou pattern for the next step: bound approximating integrals, apply lower semicontinuity of the nonnegative integral, and recover integrability of the limit. Its Smirnov hypotheses are not imported into the native problem.

Own newest-first arXiv queries were `hypoellipticity` and `symmetrization`. [Coriasco–Kleinhenz–Wunsch, 1 September 2026](https://arxiv.org/html/2609.01774v1), assumes a spatial graph-norm equivalence in its time-periodic problem; it does not supply the native admission estimate. [Huang–Zhao, 9 September 2026](https://arxiv.org/html/2609.10331v1), treats a distributional mixed Brinkman formulation with tangential-normal stress coupling. Neither paper is a premise in Lean.

## Validation

- Both scratch proofs passed with `lake env lean`, without warnings.
- Final targeted build of `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullNativeWave`: 134 seconds, two jobs, 4091 cached local dependencies and 11 cached dependency packages.
- Final targeted build of `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeJointEnergy`: 161 seconds, two jobs, 4134 cached local dependencies and the same 11 dependency packages.
- Each audit contained only its target source and cached dependencies. No existing dependency or umbrella was rebuilt.
- Only the six new public theorems were checked with `#print axioms`; all depend only on `propext`, `Classical.choice`, `Quot.sound`.
- Audited source and five emitted artifacts per target were installed byte for byte. The existing source had an original-source equality guard; the new module had a destination-absence guard.
- `scripts/formal_tools.py lint` passed with existing large-file warnings.
- The new module is imported by `formal/GaloisForLFunctions/RHTower.lean`; that umbrella was not built. Frontier map and universal-law ledger were not modified.
- Owned scratch files, search outputs and process handles were cleaned up. No mathematical computation or external numerical result enters these proofs.


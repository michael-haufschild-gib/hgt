# HB: native angular regularity and compact Green identity

Stage: 3-formalized. Eight new public theorems close joint angular smoothness and compact angular integration by parts for the literal native time primitive. Global gradient energy, joint-domain admission, complete physical inverse identification, physical-current extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target remains the complete physical current with independent SS/SV/VV amplitudes. This result closes the angular integration-by-parts prerequisite in the [native elliptic energy construction](../1-in-progress/hb-native-cusp-inverse-identification.md#native-elliptic-energy-construction), without presupposing global finite gradient energy.

## Exact result

All declarations are in `RHTower.D4BMNativeResponse`, in [ThetaCuspHawkingBMNativeAngularGreen.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMNativeAngularGreen.lean).

For arbitrary native `q`, complex `s,amplitude`, real `t,x`, and natural `n`, let

```
W(z) = globalNativeTimePrimitive(q,s,amplitude,t,x,z),
eta(z) = modularCuspCutoff(n+1,z),
g(z) = eta(z)^2 W(z),
D_0 = weightedDeriv 1, D_1 = weightedDeriv I.
```

`W` has the complete germ of `nativeResidualTimePrimitive(q,s,amplitude,t,x,Re(z),log(Im(z)))` at every point of the original closed modular cell. The theorem `nativeTimePrimitive_compact_angular_green` proves integrability of both displayed pairings and the complex identity

```
integral_fd sum_i conj(D_i W) D_i g dmu
    = -integral_fd conj(Delta_H W) g dmu.
```

It has no regularity, energy-domain or field-equation premise. The measure, derivatives, primitive and all three principal amplitudes are the original objects.

| Declaration | Closed statement |
| --- | --- |
| `fullNullResponse_angular_smooth` | Joint `ContDiff` of every order in both angular coordinates for the literal full response. |
| `fullNullResidual_angular_smooth` | Same joint smoothness after all three principal cutoff subtractions. |
| `nativeResidualTimePrimitive_angular_smooth` | Same joint smoothness for the actual double time primitive. |
| `nativeResidualTimePrimitive_cell_compatible` | Complete modular overlap germs survive the time integral. |
| `globalNativeTimePrimitive_smooth` | The constructed extension is globally chart-smooth. |
| `globalNativeTimePrimitive_germ` | Its full germ equals the literal primitive at each closed-cell point. |
| `globalNativeTimePrimitive_invariant` | Every original modular transformation preserves the extension. |
| `nativeTimePrimitive_compact_angular_green` | Both compact pairings are integrable and obey the displayed identity. |

`nativeTimePrimitiveCutoff(q,s,amplitude,t,x,n,j)` constructs the actual original `CoreField` with field `eta^(j+1) W` for every natural `j`.

## Proof mechanism

The source characteristic radius `arcosh(max(1,Z))` is continuous; smoothness of that radius is not needed. A compact-parameter integral preserves smoothness in separate finite-dimensional variables when its integrand is a smooth function composed with a continuous parameter map. The proof bounds the partial Frechet derivative on a compact product, applies dominated differentiation, and inducts on derivative order. This controls mixed angular derivatives, not only repeated derivatives along one coordinate.

First apply that theorem to the literal circle mean. Rescale each source interval and the time interval to `[0,1]`, keeping every signed Jacobian and the original odd source. The triple integral has fixed compact parameter domain, and angular variables enter only through the smooth circle mean. The rescaling identity also holds for negative and zero endpoints. The three principal terms form a separate smooth finite-dimensional angular map composed with continuous time coefficients.

For modular overlap germs, translations preserve the residual globally. On nonparabolic overlaps, both relevant heights stay below the cutoff threshold in a neighborhood determined solely by geometry. That same neighborhood works at every integration time. Thus integration preserves the full overlap germ, including seams and elliptic corners, and the existing cell-extension construction gives the actual global smooth field.

Set the outer cutoff scale to `3(n+1)`. It equals one on a neighborhood of every point below height `3(n+1)`, covering the inner cutoff support. Apply the existing `CoreField.completed_green` to this outer-cutoff primitive and `g`. Above the inner support, `g` and its first derivatives vanish locally. Below it, the outer-cutoff field and its first and second derivatives equal those of `W`. Consequently both original core pairings equal the desired native pairings almost everywhere. Their integrability transfers too. No assertion about the uncut primitive's completed energy graph is used.

The mixed term from differentiating `eta^2 W` remains present. Combining its real part with the radial energy identity, assembling the actual L2 forcing, proving the cutoff estimate, then taking the cusp limit and constructing first-gradient approximants are the remaining tasks.

## Discovery and applicability

Broad corpus searches used `regularization averaging` with OR matching, followed by deep mechanism searches for compact parameter differentiation and smooth currying. Candidate lemmas, source methods and proposed ingredient groups were inspected. Results were partial: compiler metadata was predominantly source-only and semantic coverage was incomplete; the last deep query also reached its deadline. Its proposed smooth-currying approach did not establish the required angular theorem. The usable construction came from the corpus's compact derivative-bound induction and actual planar periodization/core Green identities, with candidate applicability checked in Lean.

Own broad arXiv queries were `gluing` and `dilation`. [Cho, revised 5 September 2026](https://arxiv.org/html/2608.26598v2), retains a coupling and combines frame inequalities to close an eight-dimensional gluing argument. The revised paper leaves seven-dimensional gluing open. The method suggests retaining coupled terms when constructing estimates; it supplies no HB estimate. [Brar--Chen--Ghosh Hajra--Kandel, 26 August 2026](https://arxiv.org/html/2608.26458v1), gives a finite-graph gluing formula with a shared-interface correction. That motivates exact interface accounting, but its finite graph theorem does not identify native cusp currents. Neither paper is a Lean premise.

## Validation

- Scratch: `lake env lean /tmp/hb-native-angular.LyrTjNfX/Candidate.lean`, passed without warnings.
- Final: `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeAngularGreen` in an isolated audit root, passed in 31 seconds, two jobs. It reused 4127 cached local-module dependencies and 11 cached dependency packages. No old dependency or umbrella was rebuilt.
- Only the eight new public theorems were checked with `#print axioms` in a scratch file. Every theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.
- The audited source and all five emitted artifacts were installed byte for byte, with checks that the destination files did not already exist.
- `scripts/formal_tools.py lint` passed, with existing large-file warnings.
- The new module is imported by `formal/GaloisForLFunctions/RHTower.lean`. That umbrella was not built. The root umbrella, universal-law ledger and frontier map were not modified by this work.
- Owned temporary files and completed-process handles were cleaned up.

No mathematical computation, added axiom or external numerical result enters the proofs.

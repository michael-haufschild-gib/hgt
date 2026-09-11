# HB: original native Darboux primitive

Stage: 3-formalized for the original Darboux integral and closed physical source-radius derivative; complete physical-current cancellation and RH remain unproved. Frontier map read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Hard target and direct attack

The remaining target is the complete physical current, including principal angular terms, under the original transposed source producer. That producer differentiates the actual causal kernel in its source radius. The corpus already proves the scalar first characteristic contact in `ThetaCuspHawkingBMNativeCharacteristicContact`; do not reproach that theorem as missing. What is still needed here is an exact nonsingular integral representation of the same derivative, with the full source action retained, suitable for source-coordinate transfer and differentiated estimates.

## Conjecture and analytical proof

Fix an actual Xi copy and original angular base point. Let `M(Z)` be the native full-source angular kernel and `H(Z)=Delta M(Z)` its full angular action. The original Darboux equation is

```
((Z^2-1) M'(Z))' = H(Z),  Z>1.
```

The already proved finite first characteristic derivative makes the lower weighted current tend to zero. Continuity of the full angular action and the fundamental theorem give

```
(Z^2-1) M'(Z) = integral(r=1..Z) H(r) dr.
```

An affine substitution therefore gives

```
M'(Z) = 1/(Z+1) integral(t=0..1) H(1+t*(Z-1)) dt,  Z>1.
```

The right side has a continuous extension at `Z=1`, equal to `Delta Q/2`. Integrating this actual derivative reconstructs `M(Z)-Q` on the entire closed physical interval. The identity keeps all three principal powers and the infinite remainder; it does not substitute a separated eigenvalue or erase any physical boundary current.

## Search applicability

Broad and deep searches covered Darboux/endpoints, radial integration, even-function division and principal flux. Coverage is partial; candidates require source and Lean verification. The existing native characteristic contact and native Goursat theorem supply the source-specific lower limit and the endpoint FTC method. The spin-two Legendre primitive suggests the same integration mechanism but only applies directly to separated scalar-degree kernels.

Broad recent arXiv search found [Hou, Fuchsian-type singularity for the Finsler p-Laplacian with potential](https://arxiv.org/abs/2606.24700) (June 2026), concerning positive solutions near isolated boundaries, and [Zuevsky, VOA bundles and automorphic forms](https://arxiv.org/abs/2607.10483) (July 2026), concerning cusp-dependent automorphic constructions. Neither supplies the required complex full-source current identity; neither is a proof premise.

## Formal status

Both exact-module builds passed without warnings: the characteristic extension in 27 seconds (three jobs), and the new source-derivative module in 132 seconds (four jobs). The isolated audit froze 4,133 cached own-module imports and 20,521 available artifact links, plus 12 source-free dependency packages. Only exact target libraries were declared, so no old dependency or umbrella build ran. A separate scratch audit of exactly the eleven new public theorems reported only `propext`, `Classical.choice`, and `Quot.sound` for each. Both verified sources and ten artifacts were installed byte-identically. The new source-derivative module is wired into `RHTower.lean`; no umbrella build ran. Corpus indexing completed; formal lint passed with existing large-file warnings. Edited local document links and target umbrella imports passed. All owned search, Lean and Lake handles reached terminal status; a process check found no owned Lean/Lake process remaining. Owned scratch and search files were removed.

The physical application uses the existing exact affine invariant `Z(y)=A-S*radialUnit(y)` and `radialUnit'(y)=radialUnit(y)^2-1`. Therefore its original ingoing-delay source derivative is

```
partial_y K(y)=S*(1-radialUnit(y)^2)*characteristicFirst(Z(y)).
```

This varies both original static-time separation and the direct/image source radius. The proofs cover `h>=0`, `target<=0`, and the complete closed ray beginning at each branch's actual characteristic, including zero delay. The endpoint retains `S*(1-u^2)*Delta Q/2`. The full transposed spin-two action, principal angular flux and complete cancellation remain open.

## Next derivative conjecture for the retained spin-two current

Differentiating the actual interior Darboux equation `n` times in `Z`, with the full base Laplacian retained, gives for `F_n = partial_Z^n M`

```
partial_Z[(Z^2-1)^(n+1) partial_Z F_n]
  = (Z^2-1)^n [Delta-n(n+1)] F_n.
```

If the original lower weighted current is admitted at each step, its rescaled integral is

```
F_(n+1)(Z) = integral(t=0..1)
  t^n (2+t*(Z-1))^n/(Z+1)^(n+1)
  * [Delta-n(n+1)] F_n(1+t*(Z-1)) dt.
```

Thus the predicted original endpoint is `F_(n+1)(1)=[Delta-n(n+1)]F_n(1)/(2(n+1))`. In particular, the retained spin-two source would equal `-8 partial_Z^2 M(1)`. This is a next proof target, not a Lean result here. It requires the actual base/radius derivative commutations, full angular integral admission and characteristic regularity of the differentiated native source; a scalar Legendre eigenvalue substitution does not discharge them. The current first-derivative result is the `n=0` source-specific integral step.

## Full-source spin-two primitive

The next current transfer does not require proving every invariant derivative at once. Put `w=Z^2-1`. Direct differentiation of the original invariant operator `L_Z=w partial_Z^2+2Z partial_Z` gives

```
L_Z(L_Z-2)M = partial_Z^2(w^2 partial_Z^2 M).
```

The [full native spin-two primitive](hb-native-spin-two-primitive.md) now proves actual base-Laplacian commutation and identifies the retained spin-two kernel as the negative second derivative of this primitive. Its first derivative is

```
partial_Z(w^2 M_ZZ) = w*((Delta M)_Z-2*M_Z).
```

The linked proof derives finite original first characteristic derivatives of every angular-Laplacian iterate, including `Delta M`, then proves both zero primitive limits and the full-source double-integral identity. It also identifies the original physical radius-frozen trace and proves quadratic/linear characteristic bounds. A separate global third-invariant-derivative bound is unnecessary for these contacts. The remaining direct target is the source-delay transpose and complete physical-current comparison, with principal angular terms retained.

## New public Lean statements

[ThetaCuspHawkingBMNativeCharacteristicContact](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeCharacteristicContact.lean), namespace `RHTower.D4BMNativeCircle`, appends:

- `angularCurrent_integral`: exact original weighted current equals the full angular-action integral.
- `argumentFirst_volterra`: the actual interior invariant derivative equals its rescaled nonsingular integral.
- `characteristicFirst_continuousOn`: continuity of that integral throughout the closed invariant chart.
- `characteristicFirst_at_one`: the complete source Laplacian contact.
- `angularKernel_closed_derivative`: the integral is the actual derivative within the physical chart.
- `angularKernel_source_integral`: reconstruction of the full kernel from the original source and admitted derivative.

[ThetaCuspHawkingBMNativeSourceDerivative](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeSourceDerivative.lean), namespace `RHTower.D4BMNativeSourceDerivative`, adds:

- `kernelField_source_derivative`: actual source-radius derivative on each closed physical ray.
- `sourceFirst_continuousOn`: continuity of the admitted original source derivative.
- `kernelField_source_integral`: original characteristic value plus full source-radius integral reconstructs the kernel.
- `kernelField_source_characteristic_derivative`: explicit original geometric-slope/Laplacian contact for both branches.
- `kernelField_source_derivative_tendsto`: the ordinary interior source derivative tends to that contact.

The old characteristic declarations are unchanged. Their axioms are not re-audited. The full source is retained throughout; these results do not claim the spin-two angular-operator transfer, complete physical-current cancellation, fixed-clock extinction, or RH.

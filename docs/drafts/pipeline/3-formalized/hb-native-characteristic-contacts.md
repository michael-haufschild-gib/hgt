# HB: actual native characteristic contacts

Status: five unconditional source identities formalized. Complete physical pairing, fixed Hawking-clock extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Positive result

The full original theta half-square has the exact first right characteristic jet `Delta Q/2`. Transport through the original direct and reflected causal coordinates gives both source-normal traces with their distinct geometric factors. These fix the characteristic data needed when the common producer acts on both legs of the native causal kernel.

The proof starts from the actual circle mean and its previously proved Darboux equation. Compact domination gives continuity of the actual Laplacian mean at radius zero. Removing one factor of `sinh d` and taking the limit proves `m'(0)=0`; removing both factors then proves `2m''(0)=Delta Q`. A derivative-limit argument on `Z>1` supplies the right derivative at `Z=1`. No boundary derivative, source regularity or kernel equation is supplied as a hypothesis.

## Exact Lean scope

All five declarations are in `RHTower.D4BMNativeCircle`.

`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCharacteristicContact`:

- `mean_second_at_zero`: the actual second radial derivative of `mean q` at zero equals half `scalarLaplacian (fullSquarePotential q)` at the original angular point.
- `argumentFirst_tendsto_characteristic`: the actual interior derivative expression tends from `Z>1` to that same source contact.
- `angularKernel_right_derivative`: `HasDerivWithinAt` on `Ici 1` gives the exact first right characteristic derivative. No assertion is made about the totalized kernel below one.

`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCausalSourceContacts`:

- `nativeRiemannKernel_direct_source_contact`: at fixed positive ingoing delay `h`, the function `y ↦ R(h-x+y,x,y)` has right derivative `sinh(h/2) Delta Q/[cosh x cosh(x-h/2)]` at `y=x-h/2`.
- `nativeRiemannKernel_image_source_contact`: for `x<=0`, the function `y ↦ R(h-x+y,x,-y)` has right derivative `sinh(h/2-x) Delta Q/[cosh x cosh(h/2)]` at `y=-h/2`.

Positive delay and the closed exterior target are bundled in their original domain sets. The direct theorem permits every real target coordinate. In both theorems `Delta Q` is evaluated at `(X,exp k)`. The proofs establish that the actual invariant maps the one-sided source domain into `Z>=1` and differentiate that map.

## Direct cancellation work exposed

The [active pairing calculation](../1-in-progress/hb-native-circle-green-kernel.md) now gives explicit two-leg delta and delta-prime contacts, retaining the moving direct endpoint and fixed image endpoint. It also retains the original master factor `-1/(2uw)`: the scalar kernel difference vanishes at AdS, but its linear coefficient supplies the finite master trace

```
G_AdS(w)=(1/sinh h) partial_w[H(eta-w) M_Q(cosh h-sinh(h)w)],
eta=tanh(h/2).
```

The complete source-transpose action on this trace is written explicitly on that card, including its smooth, delta and delta-prime parts. A further finite-time paper argument uses smoothness of the divided candidate response to exhibit the original mixed radial current's `u^2` factor, with both temporal terms retained. These distributional and integrated statements are analytical; the five Lean theorems above prove their actual first characteristic data only.

The remaining target is the complete physical pairing. Physical response identification, the infinite-time and cusp limits, the other boundary terms and all independent SS/SV/VV coefficients remain required. No extinction theorem follows merely from the AdS calculation.

## Validation

Both scratch sources passed foreground `lake env lean` checks without warnings. Final audits used only the two exact `lake build` leaf targets, sequentially, with 3942 existing own-corpus dependency modules frozen. The characteristic leaf completed in 4.7 seconds and the original-coordinate contact leaf in 3.6 seconds. No old dependency, full or umbrella rebuild ran.

Only these five new public theorems were axiom-audited; each reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Both installed sources and their four olean/ilean artifacts were byte-compared with the audited files. Both imports are wired into RHTower without building it. No mathematical computation was used.

Both new modules appear in the refreshed corpus index. Static `scripts/formal_tools.py lint` and scoped whitespace checks passed; lint retained 141 existing file-size warnings. All owned Lean/Lake processes exited. The owned scratch and frozen-cache audit workspace were removed. The frontier map was not edited.

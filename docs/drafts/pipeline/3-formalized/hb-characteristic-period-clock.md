# HB: radial pole period, regular clock equation and zero-delay contact

Status: ten analytic identities formalized. Complete physical current cancellation, fixed Hawking-clock extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Result and relation to the remaining cancellation

The positive-delay characteristic source calculation reduces its radial contact moments to one scalar period per ordered branch and elementary endpoints. This leaf formalizes that period's source normalization, clock equation, regular realization, lower contact and pole-order recurrence. The five original source-density reductions and their finite coefficient formulas remain analytical on the [current comparison card](../1-in-progress/hb-positive-delay-characteristic-current.md).

Put `c=exp(-h)`, `nu=delta-2`, and use positive-base complex powers. The literal normalized period is

`F_delta(h)=c^(4-delta) integral[(1+c)/2,1] r^(delta-2)/(r-c) dr`.

For positive delay it equals

`R_delta(h)=exp(-2h) integral[1/2,1] (1+(exp(h)-1)y)^(delta-2)/y dy`.

The latter is continuous and differentiable for every real delay and every complex frequency, with

```
R_delta'(h)+2R_delta(h)
 = (delta-2)exp(-h) integral[1/2,1] (1+(exp(h)-1)y)^(delta-3) dy
R_delta(0) = log 2
R_delta'(0) = (delta-2)/2-2 log 2.
```

Thus the lower-endpoint contribution in the finite-clock transfer is fixed. The degenerate integral defining `F_delta(0)` has value zero; its positive-delay limit is `log 2`. The proof retains that limit rather than using the degenerate value as a boundary trace.

For the pole moments `Ij(nu,c)=integral[(1+c)/2,1] r^nu/(r-c)^j dr`, the division-free recurrence is

```
(j+1)c I(j+2)
 = (nu-j) I(j+1)
   - [r^(nu+1)/(r-c)^(j+1)] at the two endpoints.
```

It holds for every natural `j` and `0<c<1`, without a frequency nonresonance assumption. Repeated use removes each higher pole in the characteristic density while retaining its endpoint terms.

## Exact Lean scope

Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCharacteristicPeriod`.
Namespace: `RHTower.D4BMCharacteristicPeriod`.

- `clockPeriod_hasDerivAt`: moving-endpoint period's clock equation at every positive delay, with explicit endpoint forcing.
- `sourcePeriod_eq_clockPeriod`: original pole integral and its source prefactor equal the moving-endpoint realization.
- `sourcePeriod_hasDerivAt`: the same clock equation for the literal normalized pole period.
- `poleMoment_recurrence`: division-free successive-pole reduction with both original endpoints.
- `sourcePeriod_eq_regularPeriod`: the fixed-interval realization equals the original period at positive delay.
- `regularPeriod_continuous`: continuity through zero for every complex frequency.
- `regularPeriod_zero`: exact logarithmic lower contact.
- `sourcePeriod_tendsto_zero`: the original period's positive-delay limit is that contact.
- `regularPeriod_hasDerivAt`: the regular clock equation for every real delay, including zero.
- `regularPeriod_hasDerivAt_zero`: the exact first derivative at zero.

The proof uses the corpus's `hasDerivAt_parametric_intervalIntegral` from `HTGeometry.ClockParametricDerivative`. Positive power bases, regularity, domination on compact rectangles and interval integrability are discharged internally. No causal extinction, spectral-line conclusion or coefficient cancellation is assumed.

## What remains

For the actual contact's explicit period coefficients, clock integration by parts leaves `C_Q+C11'-2C11`, the regular endpoint forcing, the original terminal-clock term and the first circle-mean jet. Their signed comparison with the physical bulk, image contact and cross-currents remains open. The independent SS/SV/VV amplitudes and all physical boundary faces remain required. These period theorems do not establish vanishing of the complete current.

## Validation

Foreground `lake env lean` scratch verification passed without warnings. The final audit used only `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCharacteristicPeriod`; it built the actual leaf in 10 seconds and reported three jobs. Forty-seven existing own-corpus dependencies and eleven external package caches were frozen and reused. No old dependency, full or umbrella build ran.

Only the ten new public theorems were axiom-audited. All report exactly `propext`, `Classical.choice`, and `Quot.sound`. The installed source, olean and ilean are byte-identical to the audited artifacts. The module is wired into RHTower without building that umbrella. No mathematical computation, frontier-map edit, launcher invocation or Git command was used.

Corpus search finds the installed source-period declarations. Scoped whitespace checks passed. Global static lint reported unrelated umbrella reachability errors for `HTGeometry.AtomicResponseMoments`, `BinaryFisherClock`, `FisherQubitClock`, `FisherRecordClock`, `PathResponseAnchoring`, `ThermalFisherClock`, and `HilbertMetric.ResponseCompression`, alongside existing large-file warnings. It reported no finding in this leaf; those other modules were left unchanged. All owned Lean/Lake and search processes exited, and the owned scratch/audit directory was removed.

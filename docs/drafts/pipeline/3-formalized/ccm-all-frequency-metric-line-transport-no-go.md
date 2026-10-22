# CCM all-frequency metric-line transport no-go

- **ID:** ccm-all-frequency-metric-line-transport-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Verdict:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` pending independent expert review
- **Proof chain attacked:** connected nondegenerate metric-compatible cross-frequency line transport → exact matched-source reporter orientation → fixed source Ward law → shared HB/FZZ-P/PW-B/RBH endpoint → RH.

## Exact claim

For every literal prime power, assign the Boolean orientation `ratio > 1` at its explicit outer-phase `2π` and `π` frequencies. Any nonzero real line-form field matching those two orientations places the witnesses on opposite signatures. Hence edgewise isometric transport cannot put them in one connected component. In particular, no connected nondegenerate metric-compatible line carrier realizes the exact reporter orientation.

## Frontier

- `[CORPUS]` `ccmActualHeadMatchedPhaseAllFrequencyProjectiveFockPrimePowerReporterSignStraddle`: the same all-frequency PSD kernel has ratio `>1` at `1/log n` and `<1` at `1/(2 log n)`.
- `[CORPUS]` `compatibleOrientation_signOrientation` and `compatibleOrientation_eq_of_preconnected`: nondegenerate one-dimensional edge isometries preserve sign, so orientation is component-constant.
- `[FALSIFIED]` Mixed-frequency Gram positivity alone supplies no orientation; the preceding formal no-go forced this stronger transport test.
- `[LITERATURE]` Suzuki's [screw-kernel](https://arxiv.org/abs/2206.03682) and [localized Weil-form operators](https://arxiv.org/abs/2606.09096) provide positivity/self-adjoint machinery, while [Connes--Consani--Moscovici](https://arxiv.org/abs/2511.22755) provide finite Euler-product spectral operators; none states this prime-power frequency/signature obstruction.
- Generic component collapse is `[REDISCOVERED]`; only its exact arithmetic weld and route consequence survive preliminary audit.

## Hostile tests

- Different components evade contradiction; therefore claim kills only connected transport and records component separation as positive survivor.
- Degenerate forms or non-isometric/singular edges evade the theorem; these are the exact surviving mechanisms, not hidden exclusions.
- Threshold `ratio > 1` is the sign of the exact logarithmic reporter because all Fock ratios are positive exponentials.
- No RH statement, Xi divisor, or source-Ward premise enters the claim.

## Proof `[PAPER-PROVED]`

Fix a prime power `n`. The exact sign-straddle theorem gives reporter orientation `true` at `xi+=1/log n` and `false` at `xi-=1/(2 log n)`. Let `c_v x²` be nondegenerate real line forms on a graph and suppose each edge map `x ↦ t_e x` is an isometry. The one-dimensional isometry identity implies `c_u` and `c_v` have the same sign on every edge, hence the induced Boolean sign orientation is constant on every connected component. A carrier matching the arithmetic reporter at vertices over `xi+` and `xi-` would therefore place `true` and `false` in one component, impossible. Without connectedness, the same argument proves the two witness vertices are not reachable. Thus faithful transport must split components or cross a degenerate/non-isometric edge. ∎

## Positive survivor

The arithmetic reporter forces a genuine signature wall: positive and negative reporter frequencies cannot be joined by regular metric-compatible line transport. Any surviving oriented source connection must carry a singular/non-isometric transition, a disconnected sector with an independent gluing law, or higher-rank indefinite data whose orientation is not component-constant.

## Lean certificate `[LEAN-PROVED]`

- Module: `GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedAllFrequencyMetricLineTransportNoGo`
- Positive survivor: `ccmActualHeadMatchedPhasePrimePowerReporterFaithfulLine_signatureSplit`, `ccmActualHeadMatchedPhasePrimePowerMetricLineTransport_not_reachable`
- Route kill: `ccmActualHeadMatchedPhaseConnectedMetricLineWardRouteKilled`
- Direct check and target-only build: pass.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Wired into `GaloisForLFunctions.RHTower`.
- Global lint sees this module through its umbrella; remaining failures are unrelated unwired concurrent modules.

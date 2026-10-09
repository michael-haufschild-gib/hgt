# BAG actual Gaussian/logarithmic derivative budgets

- **Stage:** 3-formalized

01ax. Paper and production Lean proof COMPLETE.

For every natural order n, one C_n>0 controls every selected normalized
slice F_(delta,h)(x)=eta_delta(x)*V(x)/(1+h*log x), 0<delta<1/2 and0<=h<=1:
its nth derivative is integrable and integral|F^(n)|<=C_n/delta^(n-1),
with natural subtraction. Thus mass and first variation are uniform.
The full amplitude is globally smooth with exact support in[1,2].

Proof: parameter-dependent Frechet differentiation and evaluation at1
show every partial x derivative of the core is jointly smooth near the
compact parameter rectangle[0,1]x[1,2]. The denominator is at least1.
Compactness supplies uniform core derivative bounds. Leibniz's rule plus
the previously audited selected-cutoff edge-mass budgets pays all terms.
Outside[1,2] every derivative vanishes; smoothness at both edges is retained.
No numerical experiment, guessed derivative estimate or resource hack.

Exact equality attaches F_(H/N,1/logN)(x) to
 logN*bagCubicMellinSliceValue N (bagCubicControlledBandCutoff N H) 0 (N*x)
for everyN>1 and0<H<N/2. The original actual slice therefore has the same
all-order budgets for everyN>=exp1 and every admissibleH. This covers the
original selectedH=N^1/4 whenever admissible, without replacing it.

Source: ChiCubicPhysicalAmplitudeBudgets284lines/API5. Full scratch7804
emptyPASS; production70720emptyPASS; finalaxiom83857 all5standard3.
Index8173PASS/API5/importonce; lint19711terminal1: two unrelated unreachable
modules(KuznetsovKernelIntegral,ThetaCuspRatioTerminalAmplitudeReverse),
362warnings,noownederror. Diff checkPASS. No full/umbrella build.

This closes actual derivative admission and budgets. Exact normalized
Fourier scaling is in scratch49555. Full low/high frequency Sobolev energy,
log-coordinate/Mellin tails and moving signed transfer remain open; full
sharp-action bridge, growing moments and common-height recurrence remain
hard. No RH conclusion.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiCubicPhysicalAmplitudeBudgets` | `bagCubicNormalizedSlice_properties`, `bagCubicNormalizedSlice_derivative_budgets`, `bagCubicNormalizedSlice_eq_actual`, `bagCubicControlledSlice_derivative_budgets` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.

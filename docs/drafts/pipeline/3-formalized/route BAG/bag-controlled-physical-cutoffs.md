# BAG controlled shrinking physical cutoff family

- **Stage:** 3-formalized

01ax. Paper and production Lean proof COMPLETE. Relative production40228
and selected sharp/smooth production38864 emptyPASS. Combined final
axiom7869 PASS: all six audited public results standard3 only. Index61984
PASS; leaf umbrellaonce. Lint62496 terminal1: three unrelated unreachable
modules (ZetaSquareStirlingAFE, ZetaSquareStirlingCarrier, UnframedPromoterNoGo),
362warnings, no owned error. No full/umbrella build.

Canonical eta_delta=blockWindow(1+delta,2-delta,delta), 0<delta<1/2.
It is smooth, compactly supported in[1,2], zero outside(1,2), one on
[1+delta,2-delta], and takes values in[0,1]. Corpus pointwise derivative
bounds are C_j/delta^j. For j>=1, local constancy kills derivatives on
the open plateau, and existing support control kills them outside[1,2].
Thus derivative mass lies only in two closed strips of total length at
most2delta. Integral comparison gives integral|eta_delta^(k+1)|<=C_k/delta^k,
with integrability proved. First variation is uniform in delta.

The selected physical family is eta_N,H(x)=eta_(H/N)(x/N). For0<H<N/2,
it retains exact band support and plateau[N+H,2N-H]. The original sharp
comparison has a general internal finite-edge bound. A shared private
band-comparison lemma applies it to any range[0,1] cutoff equal1 on that
plateau: count the two ceil(H) edge sets and obtain C(H+1)^2N(1+log(N+1)).
Applying it to this explicit family and H=N^1/4, the original square-error
majorant tends tozero after normalization log^4N/N². Nonnegative square
roots give the exact original sharp/smooth norm error*log²N/N ->0.
No replacement of the paid edge width or unspecified existential cutoff.

Sources: ChiCubicControlledCutoff151lines/API5; shared helper and selected
error theorem in ChiPrimeGaussianCubicSharpEdges. First scratch20304 and
scaled scratch3704 PASS; relative production40228emptyPASS. Selected
attachment scratch96304PASS; optimized scratch28763PASS. No increased
resource limit, new axiom, numerical experiment or full/umbrella build.

Actual Gaussian/log amplitude derivative bounds, exact reciprocal-phase
Fourier identity, energy/Minkowski/high-frequency/log-map assembly still
open. This does not yet prove uniform physical H^s or signed cubic saving.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiCubicControlledCutoff` | `bagCubicControlledCutoff_properties`, `bagCubicControlledCutoff_derivative_budgets`, `bagCubicControlledBandCutoff_properties` |
| `GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicSharpEdges` | `primeGaussianCubicMainEntry_norm_le`, `primeProfileBand_card_le_twice`, `exists_primeGaussianCubic_smooth_band_comparison`, `exists_primeGaussianCubic_smooth_band_negligible_error`, `primeGaussianCubic_controlled_cutoff_negligible_error` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.

# HCF source alias budget

- **ID:** HCF-SOURCE-ALIAS-BUDGET
- **Stage:** 1-in-progress (source alias theorem formalized; arithmetic ceiling open)
- **Type:** THEOREM (Lean) + falsified unsigned shortcut
- **Source:** HCF sharp Poisson lattice ripple / source-Plemelj covariance route
- **Statement:** The full periodized HCF pole--Gamma observable differs from its exact `2π` zero mode by at most `37/200` times the compact source `L¹` mass.

## Goal

Turn the sharp Poisson ripple into a literal zero-independent pole--Gamma inequality before any
divisor scalarization, and determine exactly which arithmetic estimate is still needed for the
`21 N / 100 + o(N)` producer ceiling.

## Gates

- [x] 0 → 1: source-pure observables, exact alias split, existing HCF endpoint identified
- [x] Paper proof: bounded Poisson ripple paired against an arbitrary integrable signed source
- [x] Lean component: `HedenmalmCriticalFeatureSourceAliasBudget.lean`; targeted build and axiom audit pass
- [ ] Arithmetic normalization: control source zero mode and signed `L¹` contribution on growing height windows
- [ ] Producer gate: corrected HCF budget at most `21 N / 100 + o(N)`
- [ ] Endpoint transfer: unconditional lower density at least `3/4`

## Corpus audit

Repeated whole-corpus `formal_tools.py research` searches covered HCF periodizations, exact zero
modes, source-only covariance, positive-shift pole--Gamma density, compact integrability,
Plemelj boundary identities, Gamma/von-Mangoldt bounds, and signed `L¹` source estimates. Existing
corpus supplies the source density and its almost-everywhere Plemelj identification, but no theorem
separating the full integer HCF lattice into its zero mode and a sharp source alias budget.

## Proved component

In `HedenmalmCriticalFeatureSourceAliasBudget.lean`:

- `abs_integral_criticalFeatureRealBoundaryPeriodization_mul_sub_zeroMode_le` works for every
  measure and every integrable real signed source `g`:
  `|∫ P g - 2π ∫ g| ≤ (37/200) ∫ |g|`.
- `criticalFeatureFullLatticePoleGammaObservable` and
  `criticalFeaturePoleGammaZeroModeObservable` are finite, zero-independent source definitions.
- `abs_criticalFeatureFullLatticePoleGammaObservable_sub_zeroMode_le` specializes the abstract
  inequality to the continued positive-shift pole--Gamma density on a compact height window.
- `abs_criticalFeatureFullLatticePoleGammaObservable_sub_zeroMode_le_of_noZero` discharges compact
  integrability on any zero-free subcritical displacement segment.

## No-go closure

- **Exact killing mechanism:** The conjecture that the numerical inequality `37/200 < 21/100`
  directly closes the producer gate is false. Its right side is `37/200` times source `L¹` mass,
  not `37 N/200`; the exact `2π ∫g` zero mode also survives. Replacing the signed source by its
  absolute value can enlarge the main term and destroys the required cancellation.
- **Strongest positive survivor:** All nonzero lattice aliases are now isolated by a source-only
  inequality. If the growing-window source normalization proves `∫|g_T| ≤ N(T) + o(N(T))`, the
  remaining allowance for the zero mode at the `21/100` endpoint is exactly
  `21/100 - 37/200 = 1/40` of `N(T)` (or a stronger joint signed estimate may bypass separate
  bounds).
- **New insight:** Research target is no longer a generic lattice/window estimate. It is a
  quantitative pole--Gamma theorem controlling the zero-frequency integral jointly with signed
  source variation. Any route that only sharpens nonzero Fourier aliases is a dead end for `75%`.
- **Status:** Positive survivor is dependency-closed and formalized. No `21/100`, `4/25`, or `75%`
  theorem is claimed.

## Verification

- `lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureSourceAliasBudget`: PASS
  (`13735/13735`).
- `#print axioms` for all 11 public declarations: only `propext`, `Classical.choice`, `Quot.sound`.
- Frontier map and concurrently edited Route HCF files were not modified.

## Log

- 2026-08-30 — exact source zero/nonzero-mode split and `37/200 · L¹` alias budget formalized;
  direct constant-comparison shortcut retired with quantitative `1/40` zero-mode survivor.

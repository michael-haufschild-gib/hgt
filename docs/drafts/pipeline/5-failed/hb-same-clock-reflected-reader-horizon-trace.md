# HB same-clock reflected-reader horizon trace

- **ID:** HB-SCRR-HORIZON
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `../1-in-progress/rh-current-frontier-map.md` · HB literal-current producer
- **Statement:** No same-clock reflected-reader radial Green horizon trace, including any finite leading-power renormalization, can be an RH-extinction observable.

## Goal

Test the natural horizon extraction obtained by pairing original radial readers at one physical clock before attempting a full causal two-leg Peierls incidence. A viable outcome had to retain a finite trace whose zero locus could detect the critical line.

## Approach

Use the literal radial Green current `radialGreen q side`, retain both differentiated Gauss factors, classify every leading-power subtraction which has a finite horizon limit, then inspect its forced coefficient and residual limit.

## No-go closure

- **Exact killing theorem/mechanism:** `radialGreen_no_finite_horizon_limit` proves the raw trace has no finite horizon limit. `radialGreen_finite_subtraction_iff` proves any finite leading-power subtraction is forced to use `center q / (4 * (1 + physicalFundamentalFrequency q side))`; `radialGreen_sub_source_counterterm_tendsto_zero` proves that subtraction leaves limit `0` for every `q, side`.
- **Strongest positive survivor:** Exact unique source-derived counterterm classification, with nonzero coefficient at every Xi copy (`radialGreen_horizon_coefficient_ne_zero`) and a decaying renormalized remainder.
- **New insight:** Horizon finiteness fixes a nonvanishing source coefficient but erases all spectral discrimination. The first live HB producer cannot be a homogeneous same-clock radial horizon trace; it must retain a genuinely causal two-leg current and its independent left-QNM leg.
- **Status:** Dependency-closed Lean source in `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMRelativeReaderHorizon.lean`; source inspected. Local re-audit is blocked by missing transitive `ThetaCuspHawkingBMLiteralSourceReflection.olean`; an attempted single-dependency build replayed thousands of modules and was stopped under the no-long-build rule. No new unaudited theorem was added.

## Log

- 2026-09-15 — retired after source-grounded horizon-limit classification.

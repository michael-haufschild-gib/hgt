# HB perturbatively regular time-dependent nonlinear repair

- **ID:** HB-VAC-DIFF-TIME-REPAIR
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** HB live source-dynamical core
- **Statement:** Time-dependent nonlinear Einstein--Teukolsky corrections, regular at vacuum and with centered BM QNM first variation, might restore literal source-FE covariance even when linear BM clock is not covariant.

## Goal

Test strongest ordinary perturbative escape left after static nonlinear source-gauge no-go. Intended chain was nonlinear FE covariance → HB fixed-clock Ward → RH.

## Gates

- [x] 0 → 1  in-progress: corpus-first route and exact RH chain
- [x] 1 → 2  fully-proven: dependency-closed no-go and sharp survivor
- [x] 2 → 3  formalized: Lean module and targeted build green
- [ ] 3 → 4  publication-ready

## No-go closure

- **Exact killing theorem/mechanism:** `hbXiPeierlsVacuumDifferentiableNonlinearEvolution_forces_linearClockCovariance`. Exact nonlinear source-FE equivariance differentiates along real source amplitudes. Its vacuum first variation must commute with literal anti-linear FE transport. If first variation is centered BM finite-time clock, existing clock classification forces RH at every nonzero time. Nonlinear terms cannot repair off-wall linear defect.
- **Strongest positive survivor:** successful source-dynamical producer must change linearized clock/source-FE law, be singular or non-differentiable at vacuum, or prove only isolated finite-amplitude source covariance with no accumulating vacuum family. These are mathematically distinct from perturbative nonlinear evolution.
- **New insight:** genuine time dependence is not an escape from static nonlinear rigidity within any perturbative Einstein--Teukolsky solution map. Remaining HB route, if any, is nonperturbative/source-changing already at first order or isolated-amplitude.
- **Status:** formalized in `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVacuumDifferentiableNonlinearEvolutionNoGo`; certificate `d4HBVacuumDifferentiableNonlinearEvolutionRouteKilled`; targeted build passes; axioms only `propext`, `Classical.choice`, `Quot.sound`.

## Log

- 2026-08-31 — route killed after C1→C2 corpus-guided conjecture loop; positive survivor audited and formalized.

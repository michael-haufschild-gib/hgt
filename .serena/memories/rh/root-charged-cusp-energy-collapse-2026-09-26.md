# Root C10: charged-cusp energy collapse, complete

Mission remains unconditional proof/falsification of RH. RH and the unsubtracted complete theta tail kernel's all-rank sign remain unresolved. User: no git, no numerical mathematical experiments, no raised heartbeat/recursion limits, one owned Lean foreground process at a time, scratch first, only required/final named leaf builds, no umbrella/full builds. Existing persistent goal stays active.

## New verified knowledge
Let Phi be thetaCuspStripSource, z_N=chargedPoint(1/N^2), J=completeThetaSource.realization.kernel (J=2K on real nodes).
- `chargedSource_compact_integral_le`: for every S>=0, integral_0^S |Phi(z_N+s)|^2 <= B_S*N^9 uniformly N>=1. Exact damped quadratic series retain arithmetic phase cancellation; Gaussian coefficient energy is N^(2k+1).
- `chargedPoint_kernel_diagonal_normalized_tendsto`: J(z_N,z_N).re/N^10 ->0.
- `chargedPoint_kernel_source_ratio_tendsto`: J(z_N,z_N).re/|Phi(z_N)|^2 ->0 (C10).
- `chargedPoint_comparison_rate_tendsto_atTop`: c>0 and eventual c|Phi|^2<=u_N J force u_N->+infinity. Strengthens C9's fixed boundary floor. Necessary diagonal condition only; no sufficiency.
- `scalar_comparison_charged_boundary_vanishing`: any analytic f dominated with positive coefficient by all finite actual tail packets on any real tail has f(z_N)/Phi(z_N)->0.
- `chargedPoint_weighted_source_energy_tendsto`: integral_(s>0) (1+s)|Phi(z_N+s)/Phi(z_N)|^2 ->0. Uses uniform Re z_N>=log(2)/2 and actual integrability.

Whole route: bounded charged-boundary comparison repairs are excluded. Need a compatible all-rank representation or a negative finite packet for actual K; more bounded rates/fixed-rank asymptotics do not settle the sign. No RH decision, no claim of novel generic Schur/tightness calculus.

## Files / audit
New leaves (all namespace RHTower.ThetaCuspBoundaryAudit):
- formal/GaloisForLFunctions/RHTower/ThetaCuspQuadraticMeanSquare.lean (19 public theorems)
- formal/GaloisForLFunctions/RHTower/ThetaCuspChargedSourceMeanSquare.lean (7)
- formal/GaloisForLFunctions/RHTower/ThetaTailChargedEnergyCollapse.lean (7)
All named builds pass; all 33 public #print axioms reports standard only (propext, Classical.choice, Quot.sound), none missing. All wired exactly once. Index refreshed; final lint --check-generated passes. Initial lint only had stale generated API/overview, resolved by index rerun. No owned jobs remain.
Closed card: docs/drafts/pipeline/3-formalized/rh-charged-cusp-energy-collapse-root-2026-09-26.md. Own fact log: docs/drafts/pipeline/1-in-progress/rh-reflection-source-sign-2026-09-26-facts.md through F82. Own parent reflection/nonlocal cards updated. Do not alter other agents' logs.

## Optimization
Removed unused ThetaTailReflectedBoundaryObstruction import from compact-source module: Lake graph 9834->8957 jobs (877 fewer). Its prerequisite quadratic module imports only charged growth plus needed mathlib. Explicit monotonicity/associativity avoids broad automation. No raised limits. Prior Gaussian optimization remains recorded in mem:rh/root-charged-cusp-comparison-and-proof-optimization-2026-09-26 (14 common proof times 7.677->3.402s; C9 eliminated 1203 project modules by shared scalar form refactor).

## Artifacts / pitfalls
/tmp/rh-c10-energy-build.log, /tmp/rh-c10-source-build.log, /tmp/rh-c10-axioms.log, /tmp/rh-c10-expected-axioms.txt, /tmp/rh-c10-index-final.log, /tmp/rh-c10-lint-final.log.
All intermediate sessions terminal. Final code under 500 lines each. No ongoing scratch obligation.
`convert ... <;> ring` can normalize local constants and expose irrelevant goals; prefer explicitly typed inequalities and `simpa only [mul_assoc, mul_div_assoc]`. Give IntervalIntegrable an explicit `volume` to avoid unresolved measure metavariables. Membership hs:Ioi0 should use hs.le, not linarith on opaque membership. `simp only [Nat.cast_ofNat]` preserves coefficients that `norm_num only` may evaluate. Reciprocal function filter proof needs Pi.inv_apply.

Corpus/method searches completed: quadratic deep, oscillatory method deep, lexical meansquare, Schur, compact tightness; late rate deep partial/no useful hit, local reciprocal filter API read and verified. Cardinal/compile metadata scripts only, no numerical math experiments. No need repeat finished audit.
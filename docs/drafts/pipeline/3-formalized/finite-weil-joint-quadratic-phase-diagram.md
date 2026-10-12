# Finite Weil joint quadratic exponential phase diagram

Status: fully proved and formalized from the local Lean corpus. Five clean native leaf builds and final native axiom audit pass. Global formal lint has three errors outside this increment.

## Target

For the actual normalized joint Weil law at `k_r = 2*(r+1)^2 + t r`, the expectation of `exp(a*x^2 + 2*b*x*y + d*y^2)` is classified for every real coefficient triple. Set `s = a + 2*b + d`. Its limit is `sqrt(2/(2-s))` when `s < 2`, and positive infinity when `2 ≤ s`. The unconditional extended-integral formula and boundedness iff `s < 2` are proved. This includes indefinite forms and the transverse kernel `s=0`, not just positive radial forms.

## Local evidence and novelty

Only local Lean sources are mathematical evidence. `WeilLogShiftQuadraticExponentialLimit` and `WeilLogShiftQuadraticExponentialCriticality` classify scalar index quadratic exponentials at coefficient 2. `WeilLogShiftJointQuantileLimit` supplies common-space joint convergence and a uniform transverse bound `2/sqrt(r+1)`. `WeilLogShiftUniformResidual` proves this bound for every atom. `HTGeometry.IntegralVariableEnvelope` transfers pointwise convergence through converging varying envelopes. Corpus searches for joint quadratic exponentials and quadratic diagonal results found no existing phase-diagram theorem.

## Paper mechanism

Write `y=x+e`. The quadratic observable equals `s*x^2 + 2*(b+d)*x*e + d*e^2`. The actual support satisfies `|e|≤2`. For any `epsilon>0`, Young's square inequality bounds this above by `(s+epsilon)*x^2 + 4*(b+d)^2/epsilon + 4*abs(d)`. When `s<2`, choose `epsilon=(2-s)/2`; the scalar envelope remains subcritical. On common quantiles, its integral converges by the existing scalar theorem. A varying-envelope dominated convergence argument then yields the exact joint expectation limit. For `s≥2`, Fatou and nonintegrability of the diagonal Gaussian quadratic exponential force divergence. The positive survivor is the complete half-space classification, including all indefinite and transverse directions.

## Completed work and verification

1. Algebraic envelope and actual coordinate bound formalized.
2. Gaussian and common-quantile integrability and exact integrals transferred.
3. Subcritical convergence, critical divergence, and exact boundedness classification proved.
4. Every leaf built natively with an empty-log gate; umbrellas wired; every declaration's axioms, all direct/incoming imports, corpus index coverage, and global formal lint audited. No full builds, experiments, web, external papers, heartbeat increases, commits, or subagents.

Artifacts use `/tmp/hgt-joint-quadratic-*`; native leaf logs use `/tmp/hgt-<Leaf>.log`.

## Formal roots and positive survivor

`RHTower.tendsto_finiteWeilCanonicalJoint_quadratic_exponential_subcritical` proves the finite limit; `RHTower.tendsto_finiteWeilCanonicalJoint_quadratic_exponential_critical` proves real divergence. `RHTower.tendsto_finiteWeilCanonicalJoint_quadratic_exponential_extended` covers all real coefficients without hypotheses. `RHTower.bddAbove_finiteWeilCanonicalJoint_quadratic_exponential_iff` gives the exact boundedness half-space. All are unconditional for the actual finite law, with branch subtypes encoding only coefficient ranges.

Two exact consequences are formalized: `exp(c*‖z‖^2)` has bounded expectations iff `c<1`; `exp(c*(z 0-z 1)^2)` has expectation tending to one for every real `c`. The phase boundary therefore depends on the restriction of the quadratic form to the limiting diagonal, even when the form is indefinite in the ambient plane. This half-space classification and the entire transverse family are the positive survivor; both paper proof and Lean proof are complete.

As in the scalar increment, the Gaussian Bochner integral has default value zero outside integrability. Criticality is established separately through Fatou and divergence of the actual finite expectations; the unconditional extended integral records infinity.

## Native closure

Five leaves compile with exit zero and empty logs: `HTGeometry.IntegralVariableDomination` (2 theorems), `RHTower.WeilLogShiftJointQuadraticEnvelope` (1 definition, 7 theorems), `RHTower.WeilLogShiftJointQuadraticLaw` (8 theorems), `RHTower.WeilLogShiftJointQuadraticLimit` (2 theorems), and `RHTower.WeilLogShiftJointQuadraticCriticality` (4 theorems). Each leaf is imported once by its theorem-area umbrella; no umbrella build ran.

Final native audit `lake --old env lean /tmp/hgt-joint-quadratic-final-audit.lean` exits zero. All 24 declarations use only `propext`, `Classical.choice`, and `Quot.sound`; all 24 local API probes pass, with no residual output. Metadata has no issues across five leaves, eight direct import edges, and nine incoming imports, all inspected. Refreshed local corpus search, including its second page, finds every one of the 22 joint declarations with no coverage markers or partial-results flag. Scoped `git diff --check` passes.

Authoritative global lint exits one: unreachable `RHTower.CCMPolarOddPrimeJumps` and `HTGeometry.QKrawtchoukCompanionTriangular`, plus `sorry` at `RHTower.CCMPolarOddPrimeJumps.lean:104` in `ccmPolarOddSource_eq_core_add_atoms`. It also reports 367 warnings. No error or warning names any leaf in this increment; unrelated files were not modified.

Artifacts: `/tmp/hgt-joint-quadratic-{metadata.json,incoming-imports.txt,final-audit.lean,final-audit.log,audit-summary.json,index-summary.json,lint.log}`. Native API lessons: normalize `4*u^2/epsilon` to `4*(u^2/epsilon)` before the final polynomial inequality; supply `integral_map`'s integrand explicitly when rewriting a lambda integral from a continuity proof expressed as function composition.

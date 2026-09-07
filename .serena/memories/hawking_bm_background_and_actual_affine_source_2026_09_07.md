# HB proved BM background and literal affine field source

Goal remains ACTIVE, unbounded, NOT achieved: unconditional RH proof/falsification via HB. Full chain: theta-cusp literal source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. This turn made verified progress, not a wait or blocker. Do not mark complete/blocked. No subagents authorized.

## Two new audited leaves
1. `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMBackgroundMetricTwoJet.lean`,257 lines,11 public theorems. Namespace `RHTower.D4BMBackground`. Imports last turn's FullMetricTwoJet. Complex rational background in real coordinates (t,r,x,y): diag[-(r²−1),(r²−1)^−1,r²*y^−2,r²*y^−2]. `jet` explicitly contains all first/ordered second coordinate derivatives, including mixed r/y. Scalar expression calculus proves jet equality with actual `D4BMMetricReconstruction.ofMetricField`.
- `metric_det`: determinant=−r^4*y^−4 if r²−1≠0.
- `metric_inverse`: actual diagonal inverse, r≠0,y≠0,f≠0.
- `jet_ricci`, `jet_scalar`, `jet_einstein`: symbolic full curvature gives Ricci=−3g, scalar=−12, Einstein=3g.
- `jet_correct`: actual full coordinate derivative realization; needs y≠0,f≠0.
- `ExteriorPoint := {x:Fin4→ℝ //1<x1 ∧ 0<x3}` contains only chart geometry, no dynamics/spectral assumption.
- `exterior_metric_det_ne_zero`, `exterior_metric_contDiffAt`: nondegeneracy/all local smoothness from explicit metric on exterior.
- `actualJet` is actual field jet; `actualJet_eq` identifies explicit array.
- `exterior_vacuum` (line242): actualJet.einstein−3actualJet.metric=0, no supplied vacuum premise.
- `exterior_source_contDiffAt`: all-order complex smoothness of actual Einstein function at this background, nondegeneracy proved.

Explicit derivatives: first only k1,k3; second only11,13,31,33. No angular derivatives omitted from perturbation; background is x-independent. Exact background is local upper-half-plane chart, no global quotient/causal completion claimed.

Primary source verified this turn after corpus searches: BM https://arxiv.org/pdf/hep-th/0609028 (v2). Eqs1–4 metric f=−1−ω_d M/r^(d−3)+r²/ℓ², Λ=−(d−1)(d−2)/(2ℓ²), Ricci=−(d−1)g/ℓ². Specialize d4,M0,ℓ1. Paper also identifies constant-curvature hyperbolic horizon quotient; global quotient is NOT formalized here. Corpus actual horizon Laplacian verified in ThetaCuspHawkingBMEisensteinActualEigenEquation around1078: y²(fxx+fyy)=s(s−1)f.

2. `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMActualAffineMetricSource.lean`,227 lines,6 public theorems. Namespace `RHTower.D4BMActualMetricSource`.
- `MetricField := (Fin4→ℝ)→Matrix Fin4 Fin4 ℂ`.
- `perturbedMetric h ε := backgroundMetric+ε•h` as actual tensor FIELD.
- `source p h i j ε` is Einstein of its actual full coordinate jet minus3 times metric component.
- `backgroundSpace`, `fieldSpace` are actual background/field jets in ComplexMetricTwoJetSpace.
- `perturbedMetric_jet`: extracting complete coordinate jet commutes with literal affine field variation, for local real C2 h entries. Proof uses ScalarTwoJet actual add/mul/constant calculus.
- `source_eq`: literal field cosmological source equals derived Einstein function on affine jet line minus3metric.
- `source_zero`: source at0 vanishes for EVERY h, no C2 hypothesis needed, from actual background vacuum.
- `amplitudeDomain`: actual perturbed metric determinant≠0; private open-domain and zero-membership proofs, no fitted domain.
- Private successive complex HasDerivAt certificates give actual first/second/third source derivatives throughout amplitudeDomain. Cosmological term retained in first derivative and proved absent from higher derivatives.
- `source_quadratic`: iteratedDeriv2 source0/2 = actual complex B(background)(fieldJet,fieldJet)/2.
- `source_cubic`: iteratedDeriv3 source0/6 = actual complex C(background)(fieldJet³)/6.
- `reconstructed_source_coefficients` (line207): BOTH identities for full covariant KI reconstruction, with slots exactly toSpace(metricJet ω kSq (actual primitive scalar jets)). Primitive C2 and radius/f nonzero explicit. Uses Expression.eval_jet_correct's smoothness part and metricJet_correct. No independent source tensor/derivative array supplied.
- This is DIRECT AFFINE source only. Higher-order corrections to metric family (h2,h3), nonlinear gauge, exceptional mixed-sector constraints, causal turn-on/boundary terms and physical projection remain open. Generic smooth reconstruction does not instantiate literal Xi/BM profiles or prove a linearized mode equation.

## Validation completed; do not repeat
Both scratch lake env lean checks passed without warnings. Final exact sources match scratch/audit-package bytes. Both wired EXACTLY ONCE in RHTower.lean after FullMetricTwoJet in order background then actualsource.
Final sequential targeted lake builds used isolated exact-source local package and absolute cached leanLibDir dependency paths, because imported prior FullMetricTwoJet installed artifact has no main rebuild metadata. Preflight required only each new leaf. Background final19s (2jobs only leaf); actualsource final5.4s (3jobs only source; reused background). No full/umbrella/dependency rebuild. Installed ONLY respective .olean and .ilean into main cache, NO trace/hash manipulation.
ONE scratch axiom audit all17 new public theorems: only propext,Classical.choice,Quot.sound. Previous theorem axioms not re-audited. Symbolic curvature proofs use simp finite sums/field_simp/ring, no computational certificates/native_decide.
Index generation and scoped git diff --check passed. Global lint --check-generated had132 large-file warnings and3 unrelated concurrent unwired modules: RHTower.ThetaCuspAllOrderLikelihoodCooling, RHTower.ThetaCuspFirstAtomAllOrderApproximation, RHTower.ThetaCuspFirstAtomReflectionJets. New leaves reachable; unrelated modules untouched. No need repeated lint without relevant change.
Owned /tmp/hb-bm-background.vJLRXO including isolated audit removed. All owned Lean/Lake handles terminal; no owned processes left. No commit/push.

## Current docs / NEXT
Updated current HB frontier paragraph, source card docs/drafts/pipeline/1-in-progress/hb-actual-einstein-metric-jet-source.md, and route-independent STATUS F20i-i: verify zeroth-order equation and actual varying object's full derivative data; distinguish affine coefficients from higher-order family corrections.
NEXT: match reconstructed HorizonFields metric00,metric01,metric11 to this upper-half-plane background; instantiate literal Xi/BM radial and horizon profiles with required C3/C2 (prior primitiveFields_contDiffAt already converts master C3 to primitive C2). Reduce actual B,C on those fields; derive higher-order field/gauge corrections, exceptional sectors, causal turn-on and boundary terms; identify physical causal source domain and final left-QNM projection; prove fixed-clock extinction. Do not mistake general field-source coefficient identification for these physical reductions. Whole full proof objective unchanged.

## Lean efficiency / technical fixes
Keep one owned Lean/Lake process, foreground, no full/umbrella builds. Build finished dependencies only if needed. Use exact-source cached-dependency audit for new RH leaves; dependencies maincache directories from lake env printenv LEAN_PATH, empty local packages with absolute leanLibDir, local root lean_lib roots new modules. Do not fake main traces.
Background symbolic Ricci proof worked with explicit diagonal jet and inverse, unfolding finite sums; maxHeartbeats1600000 local for curvature,800000 local for diagonalValues_jet realization. Ring-normalize BEFORE field_simp in expression-jet equality: otherwise equivalent f-denominators expand differently and cause pointless rational goals. coordinateJet_correct uses linear Complex.ofRealCLM.comp(proj k), Pi.single directions; constant second derivatives need explicit function equality. For generic real C∞ inverse of complex field, `simpa [metric] using hF.inv hf` caused instance diamonds; `change ContDiffAt ... explicit reciprocal function; exact hF.inv hf` passed.
Source private `line`, `first`, `second`, `third` are abbrevs to reduce instance-transparency trouble. Nested complex derivative `.const_add`/`.clm_apply` certificates still needed `convert! ... using 1`, then small simp; plain simpa failed due ℂ/complex product module instance diamonds. Temporary backward transparency options did not help and were REMOVED. Avoid generic simp of source_zero (unfolds huge derivative formulas); prove perturbedMetric h0 function identity, rewrite it, apply exterior_vacuum. Post-simp private assemble remaining goals close by rfl. No additional FaaDiBruno imports needed; local derivative equality on open amplitudeDomain gives iteratedDeriv2/3 directly.

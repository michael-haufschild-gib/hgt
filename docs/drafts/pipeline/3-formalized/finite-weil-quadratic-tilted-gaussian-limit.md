# Finite Weil quadratic tilts and their explicit Gaussian limit

Status: fully proved and formalized from local Lean sources. Five clean native builds and final native axiom audit pass. Global formal lint reports eight errors outside this increment.

## Target

For every quadratic `Q(x,y)=a*x^2+2*b*x*y+d*y^2` with `s=a+2*b+d<2`, the actual finite joint probability law tilted by `exp(Q)` is constructed and converges weakly to the diagonal image of `N(0,1/(4-2*s))`, along every depth sequence `2*(r+1)^2+t r`. Normalized exponential weights converge in L1 on the existing common quantile probability space. Every analytic premise is discharged at the actual finite laws; the coefficient subtype records only the subcritical parameter range.

## Local evidence

`WeilLogShiftJointQuadraticLimit` proves convergence of the partition function to `sqrt(2/(2-s))`. `WeilLogShiftJointQuadraticLaw` supplies common-quantile integrability, exact integral transfer and AE convergence. `HTGeometry.IntegralVariableDomination` transfers bounded continuous tests under varying envelopes. Local mathlib `MeasureTheory/Measure/Tilted.lean` defines the normalized tilt and proves probability, integral and integrability formulas. `HTGeometry.GaussianQuadraticExponential` supplies the Gaussian normalizer and density multiplication identity. Searches found no existing finite-Weil quadratic tilt limit or generic tilted convergence theorem.

## Paper proof

The finite exponential weight is integrable and strictly positive, so its normalized tilt is a probability measure. Common joint quantiles converge AE; their exponential weights converge AE and in integral. Multiplying by a bounded continuous test has a varying integrable envelope equal to its sup norm times the exponential weight. Thus weighted expectations converge. Divide by the positive limiting partition function to obtain weak convergence of tilted laws. Normalized common-quantile densities are nonnegative, integrate to one, and converge AE; the corpus Scheffe lemma gives L1 convergence.

For explicit identification, centered Gaussian precision changes by the quadratic tilt: tilting `N(0,v)` by `(1/(2*v)-1/(2*w))*x^2` yields `N(0,w)` for positive `v,w`. The density factor is `sqrt(w/v)` and cancels its partition function. With `v=1/4`, choose `w=1/(4-2*s)`. Push this scalar identity along the diagonal via exact bounded-test integral formulas.

## Completed work

1. Exact Gaussian precision-change identity and bounded weighted-test convergence proved.
2. Actual tilted finite laws and explicit Gaussian target constructed; exact integral identities proved.
3. Common-quantile normalized-density L1 convergence and weak convergence of actual tilted laws proved.
4. Native leaf builds and final native axiom audit passed; umbrellas wired; every dependency and incoming import inspected; corpus indexing and global formal lint checked.

Only local Lean sources. No web, papers, numerical experiments, subagents, full builds, heartbeat increases or commits. Artifacts use `/tmp/hgt-weil-quadratic-tilt-*` and native logs `/tmp/hgt-<Leaf>.log`.

## Formal roots and insight

`RHTower.tendsto_finiteWeilCanonicalJointQuadraticTilt_gaussian` proves weak convergence of actual probability measures. `RHTower.tendsto_finiteWeilCanonicalJointQuadraticTilt_integral` gives every bounded continuous observable. `RHTower.tendsto_finiteWeilCanonicalQuadraticTiltQuantileDensity_L1` proves convergence of the normalized quantile densities; both finite and limiting densities are integrable and have integral exactly one.

The new relation is exact Gaussian precision renormalization: the diagonal precision changes from `4` to `4-2*s`. All ambient quadratic coefficients enter the limit solely through `s=a+2*b+d`, including indefinite forms. The L1 statement concerns densities on the common quantile space; the probability-law statement is weak convergence. No claim of total-variation convergence of the finite atomic joint laws is made.

## Native closure

Five leaves compile with exit zero and empty logs: `HTGeometry.GaussianQuadraticTilt` (3 theorems), `HTGeometry.BoundedWeightedConvergence` (2 theorems), `RHTower.WeilLogShiftQuadraticTiltLaw` (3 definitions, 5 theorems), `RHTower.WeilLogShiftQuadraticTiltDensity` (2 definitions, 7 theorems), and `RHTower.WeilLogShiftQuadraticTiltLimit` (4 theorems). Each is imported once by its theorem-area umbrella; no umbrella build ran.

Final native `lake --old env lean /tmp/hgt-weil-quadratic-tilt-final-audit.lean` exits zero. All 26 declarations use only `propext`, `Classical.choice`, and `Quot.sound`; all 27 API probes pass, with no residual output. Metadata reports no issues across five leaves, 11 direct import edges, and nine incoming imports. Every edge was inspected. Refreshed corpus indexing finds all 26 declarations, including both pages of the 21 actual-law declarations and all five generic declarations, with no coverage markers or partial-results flag. Scoped `git diff --check` passes.

Authoritative global lint exits one with 367 warnings and eight unrelated errors: unreachable `RHTower.CCMPolarOddPrimeJumps`, `RHTower.PaperWoldNearEnvelope`, `RHTower.PaperWoldNearOperator`, `RHTower.PaperWoldNearSignedForm`, `RHTower.PaperWoldNearSpectrum`, `HTGeometry.CauchyTakagiApertureBoundary`, and `HTGeometry.QKrawtchoukCompanionTriangular`; plus `sorry` at `RHTower.CCMPolarOddPrimeJumps.lean:104` in `ccmPolarOddSource_eq_core_add_atoms`. No error or warning names a leaf in this increment. Unrelated files were not modified.

Artifacts: `/tmp/hgt-weil-quadratic-tilt-{metadata.json,incoming-imports.txt,final-audit.lean,final-audit.log,audit-summary.json,index-summary.json,lint.log}`. API notes: qualify `ProbabilityMeasure.map` explicitly when its argument is a subtype literal, since dot notation can select `Subtype.map`; rewrite the Gaussian exponential's scalar exponent explicitly to avoid unhelpful `ring` diagnostic output. No owned process remains running.

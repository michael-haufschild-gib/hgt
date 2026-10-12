# Sharp finite-Weil quadratic exponential threshold

Completed from local Lean corpus only; no web, external papers, numerical experiments, subagents, heartbeat increases, full/umbrella builds, commits, or pushes. User's mathematical source restriction persists.

Card: docs/drafts/pipeline/3-formalized/finite-weil-quadratic-exponential-threshold.md.

For every t : Nat → Nat, actual normalized projected index X_r at k_r=2*(r+1)^2+t r has linear MGF converging to exp(theta^2/8), all real theta. Its quadratic exponential moments converge to sqrt(2/(2-c)) for c<2 and to positive infinity for c≥2. BddAbove of their range iff c<2. Extended-integral limit for every real c is ofReal(sqrt(2/(2-c))) below 2 and top otherwise. Final actual roots have no analytic premises; branch subtypes only encode the sharp parameter ranges. Generic helpers retain ordinary reusable hypotheses, all discharged at actual roots.

Seven new leaves, wired once each into corresponding umbrella, all native terminal zero with empty logs:
- HTGeometry.WeakContinuousMomentTransfer (1 theorem): weak continuous-observable expectation transfer from uniform square bound via pushforward and existing scalar moment convergence.
- HTGeometry.GaussianQuadraticExponential (6): Gaussian density transfer, decaying quadratic envelope with absolute-linear factor, exact quadratic integrability iff c<1/(2v), exact Bochner formula, subcritical envelope integrability.
- HTGeometry.IntegralFatouDivergence (1): nonnegative AE convergence to a nonintegrable limit forces real integral divergence.
- RHTower.WeilLogShiftProjectedExponentialLimit (3): projected Gaussian exponential integrability/formula and actual index linear MGF convergence.
- RHTower.WeilLogShiftGaussianAveraging (3): exp(c x²)=Gaussian average of exp(sqrt(2c) z x), commutation with every actual finite observable law, actual index specialization.
- RHTower.WeilLogShiftQuadraticExponentialLimit (8): Gaussian threshold/value, common-quantile integral/integrability/AE convergence, subcritical DCT on nonnegative and nonpositive c branches.
- RHTower.WeilLogShiftQuadraticExponentialCriticality (3): actual real divergence for c≥2, unconditional extended-integral limit all c, exact boundedness iff c<2.

Mechanism: linear MGF limit plus uniform bound 4 exp(|a|+a²/8); Gaussian averaging gives envelope 4 exp(sqrt(2c)|z|+(c/4)z²), integrable under N(0,1) for c<2. Negative c uses quantile DCT bound 1. For critical/supercritical c, Fatou on common quantiles and Gaussian nonintegrability gives divergence. Beware Gaussian Bochner formula returns zero outside integrability; use actual real divergence and extended integral there.

Final native scratch audit: lake --old env lean /tmp/hgt-weil-quadratic-exponential-final-audit.lean exits0; validator checks all25 declarations and44 API haves; only propext, Classical.choice, Quot.sound, no residual output. Metadata issues[] across7 leaves,15 direct import edges,13 incoming imports. Refreshed scoped lexical index finds all11 declarations in quadratic Limit/Criticality leaves; markers[]. Scoped git diff --check passed before card finalization.

Global formal lint exits1, eight errors outside owned leaves: unreachable RHTower.CCMPolarOddPrimeJumps, PaperLiNegativeCutoffs, PaperLiNegativeOperator, PaperLiNegativeProfile, PaperLiNegativeSuppression, XiSliceOffCentreArcTail; HTGeometry.QKrawtchoukCompanionTriangular; sorry CCMPolarOddPrimeJumps.lean104 ccmPolarOddSource_eq_core_add_atoms. None of seven new leaves flagged. Do not alter foreign work.

Artifacts /tmp/hgt-weil-quadratic-exponential-{metadata.json,declarations.json,incoming-imports.txt,final-audit.lean,final-audit.log,audit-summary.json,lint.log,index.json}; leaflogs /tmp/hgt-<Leaf>.log. Native final session64367 and lint55031 both terminal; no owned native build live.

API lessons: rewrite pushed-forward power integrals before pow_one; Gaussian wrapper integrability needs simp, not simp only; NNReal nonzero variance via congrArg coercion on alleged zero equality. Fatou lemma lintegral_liminf_le' lives in MeasureTheory/Integral/Lebesgue/Add.lean. Use tendsto_of_le_liminf_of_limsup_le for ENNReal→top; Filter.liminf_eq_top needs CountableInterFilter and cannot apply to Nat.atTop. ENNReal.tendsto_ofReal_nhds_top converts back to real atTop. All used API names verified in native scratch.

Prior increments: `mem:research/finite-weil-joint-transport-exponent-boundary-2026-10-11`, `mem:research/finite-weil-joint-quantile-all-moments-2026-10-11`, `mem:research/finite-weil-uniform-exponential-scalar-moments-2026-10-11`.

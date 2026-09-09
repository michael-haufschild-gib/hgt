# Gomes arXiv corpus experiment — batch 29 complete; goal ACTIVE

User's unbounded /goal remains active. This is a batch checkpoint, not completion. Papers 2607.24901, 2509.25276, 2404.10461. Experimental scalar connection/tensor half-density applications; do NOT imply literal full gauge-category formalization. 2509.25276v7 withdrew v1-v6 equivalence; never revive it.

## Verified totals
Batch29: 44 theorems, 6 new modules, 5 definitions. Prior1310/139 => cumulative1354 theorems/145 modules.
Artifacts /tmp/hgt-gomes/twentyninth.
Six clean scratch checks; six exact-module foreground builds; all49 declarations #print axioms audited with only propext/Classical.choice/Quot.sound; all49 indexed. Global formal lint PASS.88 prior source hashes unchanged. No own Lean/Lake processes.
Six modules appended to GaloisForLFunctions/HTGeometry.lean, no umbrella build.
modules.json/counts.json/build-status.json/totals.json/axiom-audit.json/process-audit.json/prior-source-audit.json record evidence.

## Rules still binding
Work directly on Lean; no cards/docs. Search scripts/formal_tools.py research before new code. No computation tactics, no holes/added axioms. One foreground Lean per agent; LEAN_NUM_THREADS=1 lake env lean scratch, lake build exactmodule only for needed oleans/final audit. Wait terminal before next Lean. Never start devserver/fullbuild/commit. No subagents. Preserve unrelated changes/processes. Keep meaningful concise chat updates <=60sec. Scratch progress.json supports compaction. Do not mark goal complete at checkpoint.

## Six new modules (all namespace GaloisForLFunctions.HTGeometry)
1. GomesPolynomialExpDerivatives
- gomesPolynomialExpJet P n Q recursively Q then J' + P' J.
- gomesPolynomialExp_hasDerivAt P Q x exact derivative of Q.eval*x exp(P.eval).
- gomesPolynomialExp_iteratedDeriv P Q n: iteratedDeriv n (Qeval*expPeval) = jet.eval*expPeval.
- gomesPolynomialExp_contDiff P Q : ContDiff ℝ ⊤ ...
- jet_add, jet_scale Cc*Q, jet_constant P+Cc. Full recurrence independent of constant log-shifts.

2. GomesPolynomialExpRapidDecay
- gomesFinitePolynomialScale (a:Set.Ioi(0:ℝ)) (P:GomesFinitePolynomialProfile): finite subtype with val C a.val*P.val. Proved from two-tail decay.
- gomesFinitePolynomialReflect P: val P.val.comp(-X), finite by reflection.
- gomesPolynomialExp_negative_linear_tail Q: Q.evalx*exp(-x)→0 atTop (structural polynomial induction).
- gomesPolynomialExp_linear_tail Q a: Q.evalx*exp(-a.val*x)→0.
- gomesPolynomialExp_amplitude_atTop/atBot/cocompact P Q: |Q.evalx|*exp(P.val.evalx)→0.
- gomesPolynomialExp_amplitude_bounded P Q: ∃C ∀x |Qevalx|*expPevalx≤C.
- gomesPolynomialExp_weighted_bounded P Q k: ∃C ∀x ||x||^k*||Qevalx*expPevalx||≤C.
Global bound uses actual ZeroAtInftyContinuousMap and diameter bound + f0.

3. GomesPolynomialExponentialSchwartz
- gomesPolynomialAmplitudeSchwartz P Q : 𝓢(ℝ,ℝ), eval Qevalx*exp(P.val.evalx).
- _apply, _deriv (actual SchwartzMap.derivCLM ℝ ℝ maps to amplitude Q'+P'Q), _add,_scale.
- gomesPolynomialAmplitude_integrable / _abs_integrable P Q.
- gomesPolynomialExponential_schwartz_iff H:
 (∃f:𝓢(ℝ,ℝ),∀x,f x=exp(H.evalx)) ↔ IsFiniteMeasure(rawH).
- _schwartz_polynomial_iff: same ↔ 0<H.natDegree ∧ Even natDegree ∧ leadingCoeff<0.
No hypotheses in global classifications.

4. GomesPolynomialGroundState
- gomesPolynomialGroundState P : 𝓢(ℝ,ℂ) = complex postcomp of amplitude1 exponential for profile H/2.
- _apply = (exp(P.val.evalx/2):ℂ).
- _pointwise_ne_zero,_ne_zero,_undressed (=1),_supercharge (=0),_kernel (=0).
- _norm_sq = dilatonWeight P.val x.
- _kernel_normal_form P ψ: HamPψ=0 ↔ ψ=undressedPψ0 • groundP (handles H(0) nonzero).
- _kernel_span P ψ: HamPψ=0 ↔∃c:ℂ,ψ=c•groundP.

5. GomesPolynomialKernelClassification
- gomesPolynomialHamiltonian_nonzero_kernel_iff H:
 (∃ψ:𝓢(ℝ,ℂ),ψ≠0∧HamHψ=0) ↔ IsFiniteMeasure(rawH).
 Necessity: undressed kernel constant nonzero; existing weighted integrability divided by its nonzero squared norm.
- _nonzero_kernel_polynomial_iff: same ↔positiveevendegree+negativelead.
- _ker_bot_iff H: LinearMap.ker(HamH).toLinearMap=⊥ ↔ ¬finite rawH.
- _ker_eq_span P: actual ker=Submodule.span ℂ {groundP}.
- _finrank_one P: finrank complex ker=1.
- _finrank H: finrank ker=if finite rawH then1else0.
- _no_dual_ground_states H: H and -H cannot both have nonzero Schwartz kernels.

6. GomesPolynomialGroundTensorGeometry
- gomesPolynomialGroundState_tensor P Q:
 mulS(groundP)(groundQ)=ground(P+Q), actual pointwise tensor on same real base.
- _tensor_kernel.
- _injective : Function.Injective gomesPolynomialGroundState; canonical field retains all coefficients.
- _projective_constant_iff P Q:
 (∃c:ℂ,c≠0∧groundP=c•groundQ) ↔∃r:ℝ,P.val=Q.val+Cr.
- _projective_connection_iff: same projective condition iff superP=superQ.
- _projective_probability_iff: same iff massNormalizedP=massNormalizedQ.
- _measure: volume.withDensity(ofReal||groundP||²)=rawP.

## Proof/API traps learned
- Polynomial.contDiff DOES NOT EXIST. Polynomial.contDiff_aeval P ⊤ works; simpa using it, not restrictive simp-only. Schwartz smooth' = (ContDiff strongest).of_le le_top.
- For arbitrary exp derivatives, isolate algebraic derivative equality then rw and exact HasDerivAt.mul; broad convert created junk equality goals.
- simp-only under nested polynomial eval sometimes stopped after one layer; for rescaling use explicit function equality, funext x; rw[eval_comp,eval_mul,eval_C,eval_X]; simp only[←mul_assoc,inv_mul_cancel₀ ha,one_mul,neg_mul], then rw whole function in Tendsto.
- Integrable.congr lambda goals need explicit change before rw[hc x]; use pointwise equality mul_div_cancel_right₀ directly instead of simpa-only over integrable lambda.
- LinearMap.mem_ker can leave ↑CLM ψ syntactic coercion; use change (HamP ψ=0) ↔ψ∈span before kernel-span rewrite.
- open Classical at file level supplies decidability for if in theorem statement.
- finrank_span_singleton and finrank_bot are ROOT namespace; not Submodule.
- Complex.norm_real gives real norm; then Real.norm_eq_abs, exp positivity, pow_two, ←Real.exp_add.
- Avoid shell filename globs for guessed modules. rg --files first. Two unsuccessful guessed globs did no writes.
- CombinedApi.lean clean and records verified mathlib APIs.

## Next concrete application
Existing RHTower.EntireExponentialMomentPolynomialDensity is promising cross-corpus consumer: prove every finite polynomial density has an entire exponential-moment window via stability under arbitrary linear tilt C t*X, then consume existing L² polynomial-density/orthogonality theorems. Search before new code. Need build missing infrastructure, not pivot.
Already read ONLY lines24–95 of that existing file in batch29:
 namespace RHTower
 HasEntireExponentialMoments mu := integrableExpSet id mu = Set.univ.
 exp_mul_memLp_two_of_entireExponentialMoments {mu} hmu t : MemLp (exp(t*x))2mu.
 monomial_memLp_two_of_entireExponentialMoments {mu} hmu n : MemLp (x^n)2mu.
 realMonomialLp mu hmu n and _ae.
 positiveDensityMeasure / negativeDensityMeasure; their finite proofs need IsFiniteMeasure mu and Integrable g mu.
Need read later declarations for exact dense span theorem, not assume names.
Conjecture: finite polynomial log-profiles (positive even degree) stay finite under ANY lower-degree perturbation, notably linear tilt; hence all exponential moments and polynomial L² density. This is not started; only candidate.
Searches this batch: dilaton kernel dimension=0; ground projective22 hits reviewed bothpages, unrelated spectral projection machinery; dilaton moment8 quartic hits; polynomial density integrable26 hits reviewed bothpages. Broad polynomial moment finite185 query refined rather than treated as relevant.

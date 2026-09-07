# EDQ exact logarithmic cutoff average and adaptive current receiver — 2026-09-07

RH/EDQ goal remains ACTIVE and UNACHIEVED. Current chain Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH. This turn formalized a new exact source family and RH receiver; it did not prove its arithmetic upper bound. Preserve concurrent CCM-FU, CLG, HB, lag/Weil work. No subagents, commits, full/umbrella builds, or local numerical experiments.

## Closed Lean leaf — DO NOT REBUILD OR REAUDIT
`formal/GaloisForLFunctions/RHTower/EulerDeletionCutoffAverage.lean`, 330 lines, namespace `RHTower.DeletionCutoffAverage`, imports `EulerDeletionDilationPowerGrowth`. 17 public theorems, 7 definitions, 4 private helpers. Wired once into RHTower.lean.
Definitions logWeight(X,M,j)=(log(j+1)-log j)/(log M-log X), taper(X,M,d)=(log M-log(max X d))/(log M-log X), modular weighted average of full bdMobiusModularApproximant j; harmonic same average of deningerHarmonicPartial j; averagePrefix weighted full complex sourcePrefix j; averagedCoefficient(X,M,p)=taper(X,M,p+1)*DeletionMobiusCurrent.coefficient p; averagedCurrent full mixed quadraticCurrent(range M, averagedCoefficient).

Public theorem locations:
39 logWeight_sum: 1<=X<M implies sum over j in Ico X M weights=1.
44 logWeight_pos on retained cutoffs.
52 logWeight_suffix: X<=M,d<=M implies sum weights with d<=j equals taper.
63 taper_eq_one for d<=X; 68 taper_endpoint zero at M.
72 cutoff_sum_transfer: ANY real module E, finite average of sum_Icc(1,j) f equals sum_Icc(1,M) taper*f (smul). Exact finite reversal.
108 modular_eq_taper: full modular vector coordinates = negative sum taper*mu(d)*(n mod d)/d.
123 harmonic_eq_taper: same taper determines sum mu/d, no independently adjusted scalar.
130 error_eq_average at EVERY coordinate, full errors, not merely initial window.
136 error_initial: for 1<=n<=X, 1-modular=n*harmonic.
150 prefix_initial: for 1<=K<=X, averagePrefix=harmonic*S_s(K)-1.
176 exists_prefix_dilation_pair_lower: D>=2,K0>=1 independent of X,M, eventual pairs K,DK<=X have total squared defect >=1/8, uniform EVERY M>X.
187 exists_prefix_square_sum_linear_lower: eventually X, for ALL M>X, sum k<=X norm averagePrefix^2 >= X/(64D).
213 mixedPath_eq_average and 223 mixedEndpoint_eq_average: literal tapered deletion paths and endpoints exactly coincide with averaged original paths/prefix. All cross terms retained in averagedCurrent.
245 exists_averagedCurrent_rpow_lower: at every hypothetical right-half actual zero rho, exists C>0, eventually X, ALL M>X, C*X^(2 Re(rho)-1)<=Re averagedCurrent(X,M,rho). C=a/(128D). Uniformity in M is the advance.
287 riemannHypothesis_iff_averagedCurrent_cofinally_subpower:
RH iff forall actual zero rho, forall e>0, exists B, forall K, exists X M, K<=X and X<M and abs(Re averagedCurrent X M rho)<=B*X^e.
Outer M can depend on X,e,rho without growth restriction. Upper growth MUST be measured in INNER X, not uncontrolled larger M. Uses right-half exclusion and conjugatePartner for left half. No extra reflection-current lemma needed. NO producer of the upper bound and NO general norm-to-averaged-current transfer proved this turn.

Validation terminal:
- final scratch handle10127 exit0, /tmp/edq_average.check.log empty.
- final targeted `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionCutoffAverage` handle9577 exit0. ONLY new leaf built, 9.0 seconds; 13115 cached dependency graph jobs, replayed old warnings. Do NOT interpret replayed warnings as rebuilding dependencies.
- new-only axioms handle19442 exit0, all24 public declarations exactly propext, Classical.choice, Quot.sound. /tmp/edq_average.axioms.log.
- formal lint handle40279 exit0, passed, ordinary large-file warnings. /tmp/edq_average.lint.log.
- ONE search-index refresh:11 changed0removed,33174files404518declarations3954gapmarkers. /tmp/edq_average.index.log.
- scoped checks source=scratch,24axiom coverage/stdsets,no admission/unsafe/numericalcertificate, whitespace,uniqueumbrella,doclinks,stage passed.
- removed /tmp/edq_average.lean,/tmp/edq_average_api.lean,/tmp/edq_average_axioms.lean. Logs remain. All owned Lean handles terminal; don't kill concurrent jobs.

Proof pitfalls:
- `prefix` is Lean keyword; use averagePrefix.
- Force `(max X d : ℕ)` INSIDE Real.log, otherwise elaborator lifts max to reals, breaking natural max rewrites.
- Telescoping `Finset.sum_range_sub (fun j : ℕ => Real.log j) M` needs explicit function/length to match casts.
- endpoint lives in `RHTower.DeletionJointCirculation`, file EulerDeletionWeightedFifthCirculation. NOT DeletionReflectedCurrent.endpoint. Wrong name caused downstream `declaration uses sorry` warnings; corrected before successful scratch/audit. Never accept exit0 with that warning.
- Complex.real_smul exists and definitionally turns real smul into ofReal multiplication.
- sum_Icc_shift helper by induction converts Icc1M to rangeM f(p+1); sourcePath carries p-index coefficient. Generic cutoff transfer then handles arbitrary source coordinates.
- To rewrite a weighted sum using membership-dependent equality hp, prove sum equality by Finset.sum_congr; simp_rw[Finset.sum_congr rfl hp] makes no progress.

## Completed RunPod experiment — DO NOT REPEAT
Directory `docs/drafts/pipeline/2-fully-proven/computations/edq-cutoff-averaging-transfer-2026-09-07/` contains experiment.py, PROTOCOL.md(frozen), results.json, run.log, SHA256SUMS, REPORT.md. These are finite numerical observations, no Lean input.
Frozen seven scales X=2^k k10..16, widths M=2X,4X; T=256X. Compute raw X,2X,4X plus two log averages. Integer raw jump/floor cumsums; longdouble averaged jumps, compensation, weighted energies1/[n(n+1)]. Record head throughX plus eight dyadic blocks to256X. Primary ratio avgerror(M,T]/rawendpointF_Merror(M,T]. Strong if all14<=1/4, persistent if >=4width4ratios>=3/4, else mixed. Frozen BEFORE execution; one run, no failedvalidation/parameterrevision.

RESULT CLASSIFICATION MIXED. Ratios width2,width4:
k10 .475518655225661,.1523759716349865
k11 .3000041398695443,.2989570717917554
k12 .5320837493023617,.21828254370676942
k13 .4806236783469543,.2754910541517924
k14 .5011381898607342,.24107039006484093
k15 .4707298303948157,.39250981631002135
k16 .7009584822484299,.39013838578697974.
All14<1; none width4>=.75. Suppression measured beyond support, no monotonic scale law. Crucially omitted targettailupper=(1+l1coeff)^2/(T+1), rawtailupper=l1coeff²/(T+1), too loose for FULL-energy comparison. Example X65536,width4: measured post-supporterror .014006348264260459; omittederrorupper443.08483815817436.

Run ONLY authorized root@157.157.221.29 port27094 key~/.ssh/id_ed25519. ProcessPool7 workers, BLAS threads1, external timeout240sec kill-after5sec. Completed9.866871sec. Python3.8.10,NumPy1.24.4,longdoublemantissa63bits,nproc16,os.cpu_count32. Validatedµ against directfactorization fixedchecks; suffix weights/totalmass; raw and avg headfloor identities; independently summed fixed coordinates. Sieve square zeroing CORRECT mu[p*p::p*p]=0 (prior differentexperimentbug not repeated). Script sha fcb1d69a8646c99756d34798e050ba81f48aa778d62748c567ea355479aad4bc. Downloaded4records and verified all4SHA256 checks. Foreground run91543 terminalexit0; upload37850/download31664 terminal. Owned /tmp/edq-cutoff-averaging-transfer-20260907-root remote files+dir removed after verifieddownloads; pgrep found no Python experiment job. No remote work remains.

## Docs/current state
Moved source card from1-in-progress to3-formalized/edq-cutoff-averaging-transfer.md; contains exact derivation, adaptiveM criterion, finiteexperimentlimits, audits, remainingproducer.
Frontier new exactaveraging paragraph immediatelyafterDilationPowerGrowth andEDQrow currentaddition. STATUS new route-independent MUST-COMPARE-AT-THE-PRESERVED-SOURCE-SCALE (do not confuse an auxiliary support's growth with preserved defect scale). Bothcurrentnotdiary.

## Corpus reads this turn / remaining directions
MenonMobiusLargeValues ordinary dyadicµ windowmean-square eventually bound at all0<l<=A,K>=1; no square-root or EDQprimitiveupper. BarbanVehovWeight exact w_X(d)=mu(d)log(X/d); b_X(k)=sumdivisorw, equalsLambda(k)on1<k<=X, b_X(1)=logX. BarbanVehovSharpSummatory exact lcmquadratic and |sum_{k<=N}b_X(k)^2-N D_X| <=(XlogX)^2; weightedIoc error <=2(XlogX)^2/(L+1). Does not yet control complete compensated weighted primitive. BarbanVehovShortEnergyMain/Lcm are mollifiedcriticaldetectorenergy, not this fullsource. Raw criticaltailobstruction excludes convergence of raw error, not bounded/subpowerenergy or averages. Searches `mobius mean square` all33hits17modules, BarbanVehov first20of454, mobiusquadraticbound first20of32, mobiuscesaro first20of30; no cutoffaveragefound in limited earlier rg, do not claim exhaustive novelty.
Next mathematical task: derive actual averaged-current upper in innerX, possibly via a proved general fullprimitiveenergy transfer and arithmetic mean-square/cancellation estimates. WideningM is now allowed by receiver but a bound solely in M does not solve inner-scale target. No more numerical experiment without a new frozen genuinely uncertain discriminator; current fixedwidth ratios do not justify predictable repeats.

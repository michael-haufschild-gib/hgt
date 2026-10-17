# Signed prime–polar research lane

Independent BiScaleUncertainty research. User goal:100 significant theorem packages; **8/100 verified**, goal ACTIVE,92 outstanding. No RH work, hgtl7 skill, numerical experiments, grid blindness, inflated helper counts, commits, or umbrella builds. Main endpoints use actual C_c sources and numerical inputs without extra analytic hypotheses. One foreground Lean process per agent.

Authoritative README: `formal/GaloisForLFunctions/BiScaleUncertainty/README.md`, read fully, then complete update adding Section3.5 and Trap10 read. **READ-ONLY by explicit user instruction.** Section3.3 directs this lane; Trap9 preserves actual prime weights and arbitrary signed correlations. Trap10 now prioritizes explicit unconditional producers: no further receiver-only reformulations and no pre-floor linear counterterm subtraction. Do not edit old/new README.
Canonical ledger: `docs/reports/BiScaleUncertainty/SignedPrimePolarTransport-FACTS.md`.
Parent card: `docs/drafts/pipeline/1-in-progress/signed-prime-polar-transport-2026-10-17.md`.
Read attachment each new turn: `/Users/michael/.codex/attachments/e9ef520a-4498-4562-99e8-1c42812df597/pasted-text-1.txt`.

## Verified packages

1. `AnnularCorrelationTransport.lean` + `SignedPrimePolarCoupling.lean`: construct C1 collar correlation H for arbitrary compact continuous f. Actual weights Λ(n)/sqrt(n), polar density2cosh(x/2), L=log(N+2). Exact work H0+exp(-L/2)H(L)E(L)-integral exp(-x/2)(V-H/2)E-integral exp(-x/2)H, E=ψ(exp x)-exp x. Uniform Krein mass cost and annular Levy/reciprocal bound. Paper `SignedPrimePolarTransport.md`.

2. `SignedPrimePolarPacket.lean` + `SignedPrimePolarGramTransport.lean`: actual compact atomicSource, polarSource, signedSource P_N. Q_N=integral P_N² is full iterated signed pairing of h(s-t), retaining both negative prime–polar terms. Actual source support proves Fubini. Q_N<=M_N²R; signed increment²<=2Q_N(R-h(y)); signed annular transport replaces mass with Q_N. Paper `SignedPrimePolarPacketGram.md`.

3. `SignedPrimePolarHalfLineDomain.lean` + `SignedPrimePolarHalfLineTransport.lean`: source cutoff N0 kills h and all positive right-annular H,V tails. Literal n>=2 sum finitely supported/absolutely summable; polar/work kernels integrable. Upper endpoint vanishes; fullPairing H=fullChebyshevWork. Every N=N0+K gives global scalar transport retaining finite Q_N. Paper `SignedPrimePolarHalfLine.md`.

4. `AnnularCorrelationSource.lean` + `SignedPrimePolarCoherentSchur.lean`: actual backward collar g(u)=d^-1 integral_I f(u-y), I=[exp a,exp a+d], d=exp b. With C=H0, B=integral g², R=h0, D=pairing h, W=work, Q=packetEnergy, mixed covariance integral g(u)f(u+t)=H(t); B=d^-2 double integral_I h(z-y),0<=B<=R, integral gP=W. Nonnegative actual residual norms B-C²/R,Q-D²/R. (W-CD/R)²<=(B-C²/R)(Q-D²/R); (D-W)²<=Qδ where δ=R+B-2C; D²/R+(W-CD/R)²/(B-C²/R)<=Q. Global at N0+K, including zero-source cases. Paper `SignedPrimePolarCoherentSchur.md`.

5. `AnnularSourceRegularity.lean` + `SignedPrimePolarRoughGauge.lean`: g is C1 with s=(f(u-A)-f(u-A-d))/d. k=s-g/2 actual compact gauge source; G=integral|k| admitted. Exact remainder ||f-g||²=δ. Weighted upper Q_N(f)<=3(1+eta)(10+eL²)B+3(1+eta)G² integral e²+(1+1/eta)M²δ, eta=exp c, e=exp(-x/2)E. eta1 gives roughGaugeBound coefficients6,6,2. Global coherent/Levy transport with independent smoothing/transport collars. Reuses compiled, exact-axiom-audited `ChebyshevGauge.packetEnergy_le_chebyshev_mean_square` on constructed g; no derivative of original f. Paper `SignedPrimePolarRoughGauge.md`.

6. `AnnularGaugeEnergy.lean` + `SignedPrimePolarCorrelationBudget.lean`: integral s²=2(R-h(d))/d²; integral sg=0; integral k²=E_g=2(R-h(d))/d²+B/4. Changing A translates g; B,E_g independent of A. k vanishes outside[A-T,A+d+T], T=actual multiplierSourceRadius f, so G²<=(2T+d)E_g=collarGaugeBudget. Substitute into rough bound for correlationGaugeBound and global Levy transport. T derived from f, not assumed or necessarily minimal. Paper `SignedPrimePolarGaugeCorrelation.md`.

7. `SignedPrimePolarScaledCollar.lean` + `SignedPrimePolarOptimalCollar.lean`: actual signed scalar compensation f=tg+(f-tg), all real t. Exact residual R-2tC+t²B. Define U=3(10+eL²)B+3collarGaugeBudget*integral e²>=30B. Q_N(f)<=F(t)=(1+eta)t²U+(1+1/eta)M²(R-2tC+t²B). D=(1+eta)U+(1+1/eta)M²B, E=(1+1/eta)M²C, t*=E/D, V=(1+1/eta)M²R-E²/D. Exact F(t)-V=D(t-t*)² including D0: D>=U>=30B forces B0 then C=E0 by actual Gram inequality. Every minimizer classified: F(t)=V iff D0 or t=t*. Z=optimizedPacketBound=min(M²R,V) gives Q<=Z<=M²R. At eta1 F(1)=correlationGaugeBound, hence Z<=old bound; exact uncapped gain D(1-t*)². Strict gain threshold: Z<M²R iff M²R/eta<E²/D. Global coherent and Levy transport take original source plus numeric parameters only. All optimization/degeneracy/comparison/transport counts once. Paper `SignedPrimePolarOptimalCollar.md`; card `3-formalized/signed-prime-polar-optimal-collar-2026-10-17.md`.

8. `SignedPrimePolarHarmonicCorrection.lean` + `SignedPrimePolarFactorialLift.lean` + `SignedPrimePolarFactorialProducer.lean`: explicit compact measurable R_K(x)=exp(x/2) sum_{j=1}^K indicator_[0,log(K/j)](x), REAL K/j. Actual atomic sum is T(K); full polar integral is K H_K-K+K log K-T(K). Hence nu(R_K)=2T(K)-K log K-K H_K+K. For W_N=(R_4N-4R_2N+4R_N)/sqrt(N), nu(W_N)=(2 B_N-C_N)/sqrt(N), C_N=4N(H_4N-2H_2N+H_N) in [0,1] by adjacent reciprocal pairing. Reuse existing abs_chebyshevBiNullProducer_le to obtain |nu(W_N)|<=(10 log(4N+1)+3)/sqrt(N). Literal atoms finite/absolutely summable and polar term integrable, all constructed. Public factorialBiNull_producer(n:Nat) bundles admission+bound at N=n+1, no analytic/arithmetic premise or free weights. W_N(0)=0, W_N(log4N)=2; factorialBiNull_ne_autocorr proves no compact continuous real source has this autocorrelation. It is a discontinuous scalar producer, not a uniform packet or positivity result. Counts once; original numerical B_N theorem is reused, not counted again. Paper `SignedPrimePolarFactorialProducer.md`; card `3-formalized/signed-prime-polar-factorial-producer-2026-10-17.md`.

## Verification

All eight packages have direct leaf passes and standard axiom audits. Package8 three final leaves exit0 with empty logs /tmp/spp8-harmonic.log, /tmp/spp8-lift.log, /tmp/spp8-producer.log. Scratch /tmp/spp8_final_axioms.lean passes twelve reports, only propext,Classical.choice,Quot.sound; main signature has only n:Nat (/tmp/spp8-final-axioms.log). Imports wired, index exits0 (/tmp/spp8-index.log), scoped whitespace passes. Latest recorded global lint exits1 solely for eleven unrelated concurrent unwired modules; exact list in lane FACTS ledger and /tmp/spp8-lint.log. No task-local error. Do not edit other lanes.

Shared .olean files disappeared during checking; direct restores of unchanged Coupling and GramTransport passed. A temporary snapshot of field artifacts provided LEAN_PATH fallback for later direct checks. All actual dependencies were present in shared tree before the overlay and obsolete spp8 API probes were removed. No owned Lean/search/lint/index process remains active. Final axiom scratch/logs and research search evidence retained. No source edits to restored dependencies. Do not launch full builds to fix isolated missing artifacts.

## Boundaries and next target

Scalar support stabilization does NOT imply Q_N stabilization: distant translates retain energy. No infinite packet or cutoff-uniform Q bound. H is mixed correlation, not assumed autocorrelation. H0 and negative-exponential polar shadow cannot be dropped; E0=-1 fixes boundary sign. Schur gives joint lower control; rough upper bounds retain actual source residuals. Gauge budget position invariant but δ depends on A via H0. New explicit gauge budget is an upper bound on G², not claimed smaller than G².

Package7 optimizes only the scalar trial family at fixed smoothing and eta. It removes coefficient-one loss, not the residual. No joint width optimization. At eta1 capped bound no worse than mass and contribution6; other eta compare with their own trial family. Smoothness alone does not imply strict gain.

Package8 is verified and counted. It avoids pre-floor divisor contamination by real-ratio continuum cutoffs, but does not discharge arbitrary-correlation packet control. Its discontinuous test is not an autocorrelation, as formally certified.

Next producer candidate: `0-backlog/signed-prime-polar-grid-preserving-smoothing-2026-10-17.md`. Average a tiny common dilation lambda∈[1,1+1/(4N)] to obtain a concrete C_c test while preserving every prime-grid value. Expected exact pairing [2B_N-(1+1/(8N))C_N]/sqrt(N), with nonvanishing and bounded L2 norm to audit. This is unproved/unformalized and uncounted. Keep the package8 discontinuous test distinct from an autocorrelation: its origin is 0 but top value is 2.

Multiple-collar compensation is parked: `0-backlog/signed-prime-polar-multiple-collars-2026-10-17.md`. Preserve cross-correlations if revisited, but follow Trap10 producer priority first.
Secondary uncounted width candidate: B(d)=2d^-2 integral_0^d(d-t)h(t)dt, reconstruct from d²B(d). A classical rearrangement alone does NOT count; pursue only if it closes a distinct width/transport question.

## Search evidence

Package8 /tmp/spp8-producer-search.json and /tmp/spp8-lift-search.json: partial=false, full file inventory, candidate lemmas and source arguments inspected. Compiler metadata mostly pending/source-only and semantic coverage unmeasured. Follow-up /tmp/spp8-next-search.json: partial=false/errors=[], retrieves smooth logarithmic-grid sources, finite-grid interpolation and current producer source; source retrieval is not certification. No retrieved statement supplies the real-ratio lift plus harmonic correction. No external novelty claim.

Package7 `/tmp/spp7-search.json`, `/tmp/spp7-opt-search.json`: partial=false/errors=[], candidates/source arguments inspected. Retrieved finite-partition Gram optimization and smooth-gauge bounds are distinct. Snapshot compiler coverage includes many pending/stale entries. No external novelty claim.
Followup `/tmp/spp7-next-search.json`: partial=false/errors=[], includes own source-only declarations before compilation; do not treat search as kernel certification. Field rg found no mixed-collar gauge kernel endpoint.
Prior width semantic search `/tmp/spp6-next-search.json` disconnected, partial=true; lexical fallback `/tmp/spp6-next-lexical.json` returned52 declarations, existing double average/unrelated triangular matrix and pair-count results.

## Lean/workflow details

- Infinite-sum linearity is Summable.tsum_add/sub (not root tsum_add/sub); tsum_mul_left and tsum_div_const exist. Probe new APIs in /tmp before use.
- Use open _root_.RHTower for floorSummatory; unqualified RHTower can resolve a different namespace inside GaloisForLFunctions.
- A reverse Nat.cast_mul rewrite need not match literal real 4*N. Supply an explicit cast equality proved by push_cast.
- Package8 harmonic correction uses lightweight Mathlib.NumberTheory.Harmonic.Bounds; it does not need the heavy factorial producer import.

- update_plan unavailable; cards carry executable plans. Serena active project Python cannot extract Lean symbols; use precise patches. Preserve concurrent edits.
- Whole C_c coercion matters: write `autocorr ((f-t • g : C_c(ℝ,ℝ)) : ℝ → ℝ)` to avoid elaboration as a difference of coerced functions. Typed literal-lambda integrability facts avoid Pi.sub/Pi.mul rewrite mismatches; in particular give hsub/htm/htg explicit types before integral_add/sub.
- Explicit named Fubini integrands avoid coercion/heartbeat loops. No heartbeat increases.
- `autocorr_source_const_mul` reused from FiniteSourceEnergyScalarization. C_c smul API `CompactlySupportedContinuousMap.smul_apply`; packetEnergy_smul and signedSource_smul_apply now public.
- `continuous_parametric_integral_of_continuous` root; `integral_integral_swap_of_hasCompactSupport` MeasureTheory.
- Generic API probes need explicit universe levels, e.g. HTGeometry.sq_integral_mul_le.{0}, integral_const_mul.{0,0}, Finset.mul_sum.{0,0}.
- `Finset.sum_div`, not sum_div_distrib. `summable_of_ne_finset_zero` exists; Function.HasFiniteSupport.summable does not.
- HasCompactSupport.div_const nonexistent: use mul_right reciprocal. Derivative products: HasDerivAt.mul then congr_deriv.
- Compact IBP helper `HTGeometry.integral_deriv_eq_zero_of_hasCompactSupport` takes pointwise HasDerivAt, Continuous derivative, HasCompactSupport function.
- Source radius in HyperbolicJumpEnergyTransfer: multiplierSourceRadius,pos,abs_le_multiplierSourceRadius. Restricted Cauchy via HTGeometry.sq_integral_mul_le; setIntegral_eq_integral_of_forall_compl_eq_zero uses pointwise off-set vanishing.
- RealEvenPolarTestFn tactics need explicit `linarith only`/`nlinarith only` facts per README. General transport endpoints retain arbitrary C_c sources; the explicit package8 producer has only its numerical index and is a compact measurable test, not a C_c source or autocorrelation.

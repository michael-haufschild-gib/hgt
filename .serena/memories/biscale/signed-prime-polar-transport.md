# Signed prime–polar research lane

Independent BiScaleUncertainty research. User goal:100 significant theorem packages; **7/100 verified**, goal ACTIVE,93 outstanding. No RH work, hgtl7 skill, numerical experiments, grid blindness, inflated helper counts, commits, or umbrella builds. Main endpoints use actual C_c sources and numerical inputs without extra analytic hypotheses. One foreground Lean process per agent.

Authoritative README: `formal/GaloisForLFunctions/BiScaleUncertainty/README.md`, all242lines read. **READ-ONLY by explicit user instruction.** Section3.3 directs this lane; trap9 preserves actual prime weights and arbitrary signed correlations. Do not edit old/new README.
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

## Verification

All seven packages have direct leaf passes and standard axiom audits. Latest leaves exit0 with empty logs `/tmp/spp7-scaled-build.log`, `/tmp/spp7-optimal-build.log`. Scratch `/tmp/spp7_final_axioms.lean` exits0; twelve endpoints only propext,Classical.choice,Quot.sound; printed main signatures contain no extra premises (`/tmp/spp7-final-axioms.log`). Imports wired, index exits0 (`/tmp/spp7-index.log`), scoped whitespace passes. Global lint exits1 solely for six unrelated concurrent unwired modules: CausalExponentialResponseAndLaplaceEnergy, ExplicitNyquistPolarAndChebyshevFactorialProducer, FiniteGridRunLength, FoldFreeKernelGramAndFranelGcdCancellation, RealizedCoherentCancellation, SuccessorSequenceHilbert. Evidence `/tmp/spp7-lint.log`; no task-local errors. Do not edit other lanes. No owned Lean/search/lint/index process remains running. Obsolete spp7_api probe/log removed; final audit/evidence retained.

## Boundaries and next target

Scalar support stabilization does NOT imply Q_N stabilization: distant translates retain energy. No infinite packet or cutoff-uniform Q bound. H is mixed correlation, not assumed autocorrelation. H0 and negative-exponential polar shadow cannot be dropped; E0=-1 fixes boundary sign. Schur gives joint lower control; rough upper bounds retain actual source residuals. Gauge budget position invariant but δ depends on A via H0. New explicit gauge budget is an upper bound on G², not claimed smaller than G².

Package7 optimizes only the scalar trial family at fixed smoothing and eta. It removes coefficient-one loss, not the residual. No joint width optimization. At eta1 capped bound no worse than mass and contribution6; other eta compare with their own trial family. Smoothness alone does not imply strict gain.

Next uncounted card: `0-backlog/signed-prime-polar-multiple-collars-2026-10-17.md`. Candidate exact mixed gauge Gram G_ij=S_ij+B_ij/4 from integral(g_i g_j)'=0; S_ij four endpoint autocorrelations, B_ij double collar Gram. Seek full coherent mixture source/transport certificate and comparison with scalar trials, not merely polarization. Singular coefficient directions must be discharged by actual source geometry; no assumed invertibility. No code for this target yet.
Secondary uncounted width candidate: B(d)=2d^-2 integral_0^d(d-t)h(t)dt, reconstruct from d²B(d). A classical rearrangement alone does NOT count; pursue only if it closes a distinct width/transport question.

## Search evidence

Package7 `/tmp/spp7-search.json`, `/tmp/spp7-opt-search.json`: partial=false/errors=[], candidates/source arguments inspected. Retrieved finite-partition Gram optimization and smooth-gauge bounds are distinct. Snapshot compiler coverage includes many pending/stale entries. No external novelty claim.
Followup `/tmp/spp7-next-search.json`: partial=false/errors=[], includes own source-only declarations before compilation; do not treat search as kernel certification. Field rg found no mixed-collar gauge kernel endpoint.
Prior width semantic search `/tmp/spp6-next-search.json` disconnected, partial=true; lexical fallback `/tmp/spp6-next-lexical.json` returned52 declarations, existing double average/unrelated triangular matrix and pair-count results.

## Lean/workflow details

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
- RealEvenPolarTestFn tactics need explicit `linarith only`/`nlinarith only` facts per README. Lane main sources remain C_c.

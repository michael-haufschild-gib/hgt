# Actual Xi full finite Hankel coercivity and explicit degree/time bound

Active user goal remains unconditional Lean RH proof or refutation; NOT complete. Work is in /Users/michael/Documents/code/hgt/formal. No commits/push were requested/performed by this agent.

## Verified new increment
Five leaves, 32 unconditional theorems,12 definitions. All foreground final lake --old env lean <leaf> -o <olean> audits passed warning-free, one Lean process at a time, no full or umbrella builds. All32 #print axioms audited: only propext, Classical.choice, Quot.sound; missing=[], unexpected_axioms={}, diagnostics=[]. All five wired exactly once in RHTower.lean. No sorry/admit/added axiom/opaque/unsafe/norm_num/decide/native_decide/#eval/#reduce/heartbeat changes. Last axiom audit session4562 exit0. Final scope checks show matching oleans newer than sources.

1. RHTower/XiHeatFiniteDecomposition.lean: scaled coefficients, polynomial and actual finite amplitude. Exact xiHeatHankelForm_scaled_eq_energy_sub_debt; all mixed terms and multiplicities retained, all needed summability proved. Lower bound K - ||a||² E_N <= H_N.
2. RHTower/XiHeatFiniteSamplingBands.lean: eventually_forall_exists_xiHeat_finite_separated_nodes and eventually_forall_exists_xiHeat_sampling_determinant have ONE small-time cutoff for ALL finite N. Use actual RVM zeros in (4^i T,3*4^i T], T=exp(-tau/2). Scaled squared node gaps >=1, norm <= R_N=(3*4^N)^2+1, determinant norm>=1. N0 vacuous.
3. RHTower/XiHeatFiniteUniformPositivity.lean: explicit xiHeatSamplingEnergyFloor N, =1 forN0, otherwise exp(-R_N)/(N³ C_N²), C_N=N!*((1+N R_N)^(N-1))^N. xiHeatFiniteNormEnergy_eventually_uniform_floor shares ONE cutoff across all orders/coefficient vectors. xiHeatHankelForm_eventually_scaled_coercive, ...weighted_coercive and ...eventually_nonneg prove each fixed finite order positive at all sufficiently small positive times, uniformly all coefficient vectors. Literal weighted margin eta *sum_j (c_j/t^j)^2 <=H_N(c,t).
4. RHTower/XiHeatQuarterPowerDebt.lean: actual three-halves reciprocal mass S=sum_q1/(|alpha_q|sqrt|alpha_q|), finite by existing XiThreeHalvesSummability. F_k=(4k+3)!+1. xiHeatNormMoment_scaled_le_quarter proves t^(k+1)L_k <=F_k S exp(tau/4) for ALL tau. Pointwise quartic-power proof and factorial Gaussian bound, no numerical computation. b0=F1,b_j=4j²F_(2j-1)+F_(2j+1) forj>=1. A_N=S*sum_{j<N}b_j. xiHeatFinitePhaseDebt_le_quarter: D_N(a,t)<=||a||² A_N t^(1/4), all cross terms retained by exact amplitude/Cauchy-Schwarz.
5. RHTower/XiHeatJointDegreeTimeBound.lean: xiHeatHankelForm_eventually_joint_lower_bound proves (eta_N-A_N exp(tau/4))*||a||²<=H_N(scaled a,t), common sampling cutoff. xiHeatHankelForm_joint_degree_time_coercive: exists tau0, forallN tau<=min tau0 (4log(eta_N/(2(1+A_N)))), floor eta_N/2 for every coefficient vector.

## RH endpoint still OPEN
Authoritative XiGaussianHeatHankelLadder.riemannHypothesis_iff_forall_xiHeatHankelForm_nonneg requires ALL N,a and ALL positive t. Common ENERGY sampling cutoff must not be conflated with all-order POSITIVITY cutoff. Degree-dependent constants leave all-order/fixed-positive-time and all-time endpoint unresolved. No exact negative witness for actual Xi proved. Do not mark goal complete. Existing XiGaussianHeatTraceCriterion off-line separator uses a finite polynomial and selected large heat time, not covered here.

## Next corpus-grounded conjecture
Search found XiLogDerivLineOneWindowLower.exists_xiZeroCount_window_ge_log:
exists h>0,T1>=4, forall T>=T1, log T <=N(T+h)-N(T-h).
Direct Lean read verified; its proof uses XiZeroCountRVMRemainder's O(logT) remainder. Can improve exponential sampling radius to QUADRATIC:
choose windows centered at (i+1)T with T>=4h and aboveT1. Scaled squared nodes lie between (i+3/4)^2-1/4 and (i+5/4)^2, adjacent real gaps>=1. Norm cap <=(N+1)^2+1. Need actual-copy extraction from positive window count, then adapt sampling proof/energy floor. Not yet implemented. Corpus search 'xiSpectralPoint window' found no direct bounded-window sample producer. This improves degree dependence but alone does not close RH time range.

## Audits/artifacts
Projectless working log: /Users/michael/Documents/Codex/2026-09-26/new-chat-3/work/xi-curvature-rh-loop.md.
work/xi-finite-manifest.json; xi-finite-axioms.lean/.log; xi-finite-scope-audit.json; xi-finite-audit-summary.json.
User report outputs/xi-full-hankel-energy-bound.md; preceding third-form report linked to it.
Index refreshed after lint. Repository lint --check-generated exit1: unrelated concurrent unwired modules (Eta reflection/prefactor, HorizontalIsolationBlockPacket, MollifiedMeanSquareGaussianPrimeFloor, ThetaNoetherExchangeSign, ThetaPrimeScalingRigidity, WindowTransformSamplingParseval, ZetaGaussianTwistedMoment, HT conjugate-reflection/Cotangent/ExteriorEuler, HilbertMetric.HorizontalLamzouriUnnormalized) and stale LEAN_API. None of ownfive unwired. Do not claim global lint passed or fix others' ongoing work.
Owned /tmp/xi-finite-api.lean and temporary process profile removed; audit evidence retained.

## Process/tool lessons
One previous interrupted handle missing+no process+noolean justified restart. Later intentionally cancelled superseded check10478 (exit143) to strengthen common cutoff; not timeout-based restart. A sample of slow lean proved it was loading imports, not a tactic loop. Cache warmed and later checks completed fast. Final no owned Lean process remains after axiom check.
Lean rewrites: explicit rw [Fin.sum_univ_eq_sum_range (fun j => ...) N] at h works where simp fails. Determinant proof use apply h.trans; rw [<-Complex.sub_re]; exact Complex.re_le_norm _. Specify mul_pow C (exp...)4 so rw does not hit first unrelated power. Explicit calc avoids fragile convert/ring goals.
Serena symbol operations previously triggered hidden Lake builds, so avoid them under user foreground/no-full-build rules; use corpus formal_tools.py research and direct Lean. Memories are safe. Check current project before writing memory because shared activation changes.

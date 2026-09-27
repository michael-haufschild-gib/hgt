# Whole-clique repair and arbitrarily large actual prime families

Active goal RH proof via arithmetic conservation and Noether; RH unproved/unfalsified. Previous goal turn universal finite triangle correction was progress. Current turn verified failure of triangle sufficiency, constructed stronger clique method, and is building actual prime cliques and finite Noether dynamics.

Repo /Users/michael/Documents/code/hgt/formal. Foreground one own Lean at a time; --old; no full builds; no numerical experiments or heartbeat hacks; no agents/commit/push. Other chats edit/build/commit concurrently; preserve. Prior tracked scratch deletion TriangleAxiomAudit.lean is intentional own cleanup.

## Current proof/build state
New files:
1 FiniteTriangleRankOneLoss.lean — PASSED clean final leaf with fresh .olean.
2 FiniteCliqueCollectiveGap.lean — PASSED clean final leaf with fresh .olean.
3 CCMFiniteCliqueBound.lean — PASSED clean final leaf with fresh .olean.
4 ThetaFinitePrimeCliques.lean — PASSED first attempt clean, fresh .olean.
5 CCMFinitePrimeCliques.lean — initial errors only missing import CCMPrimeFrustratedTriangle for compact-real polar bridge; import added; final leaf audit PASSED clean with fresh .olean.
6 CCMFinitePhaseNoether.lean — final audit currently running exec session59723. Includes finite phase energy/torque/variation/Lagrangian/conserved momentum, explicit uniform rotation and clique phase bound. Last poll live/no output. DO NOT start another own Lean until terminal.
First FIVE modules wired after CCMPrimeTriangleExtension in umbrella. Need wire last module when passed, final axiom audit/scratch cleanup/index/lint. Optional planned addition after current audit: identify Noether charge explicitly by derivative of L(theta,v+t*ones) at0=Σv; then explicit uniform-rotation charge formulas if useful. No full umbrella build. Scan no sorry/admit/newaxiom/heartbeat/#eval/native_decide; diff --check clean.

## Verified negative result (not RH counterexample)
Constant real matrix Mij=p>=0 has Q=p(Σxi)^2. For n>=3:
Lseparate=(2-n)pΣxi²;
triangle correction=((n-1)/2)pΣxi²;
combined triangle bound=((3-n)/2)pΣxi².
So for n>3 this estimate is negative even for a known PSD form. Proof SYMBOLIC finite sums, no enumeration/numerical experiment. Main `finiteSignedTriangle_lower_constant_exact`.
Actual endpoint `exists_ccmPositive_source_triangle_loss_repaired` (CCMFiniteCliqueBound:32) constructs an actual positive smooth source from exists_ccmArithmetic_positive_baseline_phase_potential; repeats it four times; proves entire real span nonnegative, triangle estimate at coefficients1 negative, and whole-clique estimate exact for every coefficient vector. Thus triangle sufficiency fails, larger group accounting repairs actual known-positive test.

## Whole-clique bound
Identity Σordered i≠j (xi+xj)^2 =2(n-2)Σxi²+2(Σxi)^2.
finiteSignedCliqueGain M = inf' over univ.offDiag of max(Mij,0), or0 if offDiag empty. Nonnegative always, positive if nonempty and every offdiag entry strictly positive. Let g=this gain.
finiteSignedCliqueCorrection M x = g*((n-2)Σxi²+(Σxi)^2), nonnegative even for n<=1 via exact square identity.
For every real symmetric M: Lseparate+Cclique<=Q. Also Lseparate+max(Ctriangle,Cclique)<=Q. Constant M=p with nonempty offdiag has g=p and L+Cclique=Q exactly.
Actual universal result `ccmRestrictedWeilSourceQuadratic_finite_collective_lower` transports this to every finite family of literal full CCM form-domain sources, all real coefficients, no geometric/sign/positivity premises.

## Actual prime cliques
ThetaFinitePrimeCliques.lean:
- spacedPrimeChoice N from Nat.exists_infinite_primes, ge and prime proofs.
- spacedPrimeSequence N recursive next choice above2previous+1; prime, strictMono, allterms>=N, 2p_i<p_j for i<j.
- exists_pos_le_finite_family e he via univ.inf' when nonempty; radius1 on empty type.
- exists_cofinal_thetaFinitePrime_clique (N n): actual p:Fin n→Nat allprime>=N, geometric separation; common r>0; canonical translated bump ground profiles at0 and logpi; all hub polar entries negative, all ordered leaf entries positive. Finite eps choices from previous prime-negative-radius and atom-free-positive-radius, combined on Fin n⊕(Fin n×Fin n). Every pair difference logpj-logpi is beyond kernel threshold and avoids integer logs by distinct primality.
CCMFinitePrimeCliques.lean:
- ccmWeilRealPolar_neg_left from add/zero polar laws.
- ccmWeilPrimeCliqueFamily u v : Optionι→domain, none=-u, somei=v_i.
- exists_cofinal_ccmFinitePrime_clique (N k): k+2 leaves plus signed hub, k+3 total. Common aperture from finite compact union. Actual smooth u,vi exact supports ball0r/balllogpi r, r,m>0, allprime>=N and geometric sequence; every offdiag polar of f strictlypositive; for all real x,
Lseparate(M,x)+m*((card-2)Σxi²+(Σxi)^2)<=Q(Σxi fi).
All arithmetic signs and positive min constructed internally. This does NOT prove total Q>=0; diagonal deficit still may need control. Radius/min can shrink with dimension; no uniform global claim.

## Pending finite Noether module
CCMFinitePhaseNoether.lean imports CCMFinitePrimeCliques and existing CCMWeilTriangleNoether.
Definitions V(theta)=Q(Σcosθi ui)+Q(Σsinθi ui), torque_i=2Σj Pij sin(θi-θj), L=Σvi²/2-V. V is TWO-channel actual Q sum, not silently single complex phase Q.
Theorems intended:
- V=ΣijPij cos(θi-θj); common shift invariance.
- actual interaction skewness and Σtorque=0.
- HasDerivAt t↦V(θ+t v) at0 with derivative -Σ torque_i v_i (connect force to potential, not merely naming it).
- total momentum Σ deriv(q_i) constant on classical Newton trajectories hacc (honest intermediate equation hypotheses).
- explicit existing scalar ccmWeilTriangleUniformPhase cω(t)=c+ωt repeated at every node satisfies Newton with acceleration0 as CONCLUSION.
- finiteSignedSeparateLower_cos_sin = lower atones.
- phaseFloor=Lseparate(M,ones).
- universal clique phase bound V>=phaseFloor+g*(n(n-2)+(Σcosθ)^2+(Σsinθ)^2).
FINAL AUDIT PASSED: CCMFinitePhaseNoether.lean session39776 exit0, clean, fresh .olean, wired in RHTower.lean immediately after CCMFinitePrimeCliques. First-variation fix was simp only [A, Pi.sub_apply, id_eq, zero_mul, add_zero, one_mul]; ring after convert! to (hi.sub hj).cos.const_mul. Private phase_interaction_skew omits Fintype. Added verified hasDerivAt_ccmWeilFinitePhaseLagrangian_velocity_shift identifying charge Σvi and ccmWeilFinitePhase_uniform_rotation_charges giving momentum card*omega and energy card*omega²/2+V(constc). All six leaves PASSED individually using lake --old env lean <file> -o <olean>. Combined NoetherCliqueAxiomAudit.lean audit13 endpoints PASSED exit0 session82621, dependencies only propext/Classical.choice/Quot.sound, scratch deleted. Theta endpoint namespace is ROOT RHTower, not RHTower.ThetaSourceWard. No new axioms, sorry, computations, heartbeat overrides. Index refresh passed (4 changed,0 removed). Global lint exit1 only unrelated in-progress umbrella gaps (CausalMobiusThetaTail, CausalThetaHalfLaplace, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, PolynomialWeilTests, SubNyquistInterpolationTest, XiGaussianDerivativePhase, ZetaZeroDensityPowerSaving, HTGeometry/LagrangeRectangleContour) and concurrent-edit staleness LEAN_API/LEAN_OVERVIEW. Final index refresh PASSED exit0 (1 changed,0 removed), regenerating API/GAPS/OVERVIEW. Do not repeat global lint amid ongoing concurrent edits or modify other chats' unfinished modules. All own processes finished; no active Lean process. Own six modules each wired exactly once; targeted diff --check clean; scratch audit absent. Earlier tracked TriangleAxiomAudit.lean deletion is own intentional cleanup and must remain. RH still neither proved nor falsified; selected family gain can shrink and arbitrary-source diagonal deficit remains.

## Lean lessons current turn
- Unused summation indices need explicit types in calc expressions: Σ(i:ι)Σ(j:ι)xi². Otherwise Lean creates unresolved type metavariables and displays synthetic sorry goals (no sorry in source).
- Product of sums: `rw [pow_two, Finset.sum_mul_sum]` preserves desired order. `simp [sum_mul,mul_sum]` can transpose order.
- In symbolic inclusion-exclusion sum proof, sum_add_distrib also expanded full-weight sum; simplify hfull with same rule before rw.
- Reverse mul_sum under nested binders: `simp only [←Finset.mul_sum]` works; repeated `rw` did not.
- Finset.lt_inf'_iff takes ONE explicit argument H; le_inf'_iff takes H and f. Finset.inf'_le _ hmem works.
- signedTriangleGain_off_constant doesn't need Fintype (omit); finiteSignedQuadratic_constant doesn't need DecidableEq (omit). finiteSignedCliqueGain nonneg/le/pos/constant don't need DecidableEq (omit).
- Proving nonzero card-2 needs explicit hd:0<(card:ℝ)-2 from hn>=3 before mul_ne_zero; positivity alone didn't use the subtraction inequality.
- No extra `ring` after simp when simp already closes repeated-index branches.

Prior continuity: `mem:research/noether_global_finite_triangle_correction_2026_09_27`, `mem:research/noether_actual_prime_frustrated_triangles_2026_09_27`.

# C11 fully formalized: no positive geometric reserve on any theta tail

Persistent goal: unconditional Lean proof/falsification of RH. Still NOT achieved; unsubtracted actual K sign remains open. No git; no numerical mathematical experiments; no heartbeat/recursion increases; one owned foreground Lean process; scratch first and named leaf builds only. User scientific/stroke-of-genius methods and corpus-led conjecture loops remain binding.

## Closed result
C11 is proved unchanged: for every real a and epsilon>0, there are n, real nodes t_i>max(a,0), real b_i with sum_ij b_i*b_j*(K(t_i,t_j)-epsilon*G(t_i,t_j))<0. K is full theta tail first-moment kernel; G its integrated sqrt((x+s)(y+s))Phi(x+s)Phi(y+s) kernel. The theorem is `RHTower.ThetaGeometricBoundaryAudit.exists_finite_negative_geometric_tail`, ThetaTailGeometricCoercivityObstruction.lean:54. This is NOT a negative packet for K, and NOT an RH decision.

Own closed card: docs/drafts/pipeline/5-failed/rh-geometric-tail-reserve-root-2026-09-26.md. Strict-reserve strategy retired; C11 obstruction true. Card contains complete paper proof and positive survivors. Original in-progress card was moved, not left stale. Own fact log: docs/drafts/pipeline/1-in-progress/rh-reflection-source-sign-2026-09-26-facts.md through F92.

## Eight formalized leaves
All named builds pass, each wired once. First five audited previous continuation (51 public theorems); final three audited this continuation (19), total70. All #print axioms reports are standard propext/Classical.choice/Quot.sound, none missing. No forbidden declarations/options.
1 HTGeometry/MellinBoundaryFinitePart: exact logarithmic subtraction, divided-difference finite part and ratio limit.
2 HTGeometry/SecantEnergyBoundary: Fatou converts nonintegrable tangent square into arbitrarily large finite positive secants.
3 HTGeometry/SchwartzSecantEnergy: strong Schwartz translation -> half-line squared-secant convergence.
4 RHTower/ThetaGeometricBoundaryEnergy: actual tangent, exact energy decomposition, explicit finite part and coefficient Phi(0)^2/4>0; nonintegrable tangent; large secants.
5 RHTower/ThetaTailGeometricReserveObstruction: K channel secants bounded, G secants unbounded, common-translation moving-cut continuity, positive-node Fin2 negative comparison packet.
6 HTGeometry/ComplexSquareRootEnvelope: sqrt_norm_sq; sqrt_norm_le_add_one for Re z>=0.
7 RHTower/ThetaTailGeometricAnalyticLocality: geometric analytic L2 feature on right half-strip, bounded Hermitian augmented realization, actual real kernel identity 2(K-epsilonG), geometricTailAccumulationSet, geometric_negative_dimensions_tail_iff (line227).
8 RHTower/ThetaTailGeometricCoercivityObstruction: negative_geometric_tail_packet; exists_finite_negative_geometric_tail.

## Dependency-closed mechanism
v(t)=sqrt(t)Phi(t). Integral v'^2 = inverse-distance Phi² tail/4 -Phi(x)^2/2 + integral t Phi'^2. Subtract Phi(0)^2 log(1/x)/4; explicit finite part is proved. Fatou yields unbounded v secants. A_c(t)=(t+c)Phi(t) is Schwartz; c=+1,-1 squared secants converge. K secant is half their difference, G secant is v energy. K-epsilonG has a negative h,0 packet; moving both nodes is just a lower integration cut, so continuity moves them strictly positive.
On geometricStrip=thetaCuspStrip intersect {Re z>0}, sqrt(z+s)Phi(z+s) has the existing c=1 polynomial channel envelope since norm(sqrt z)<=norm(z+1). Adjoin the geometric Family to SourceDouble using WithLp2 product and form (differenceForm,-2epsilon id). Compressed closed-span realization has kernel 2(K-epsilonG) on positive real nodes. Analytic totality transports a negative vector to finite sections on every accumulating real tail. Real/imaginary energy splitting gives real coefficients; S.equivFin.symm reindexes support to Fin n.

Positive survivors: exact actual tangent finite part and sharp positive logarithmic coefficient (ThetaGeometricBoundaryEnergy lines146,164), plus retention of EVERY finite negative dimension on each positive tail, not just one negative vector. Whole-route meaning: only sharp boundary D>=-2G remains potentially useful. Do not continue manufacturing strict-reserve no-gos as substitute for source sign.

## Final verification evidence
/tmp/rh-c11-final-axioms.lean and .log, expected names /tmp/rh-c11-final-axiom-names.txt: 19 reports validated by /tmp/rh-c11-check-final-axioms.py. Prior51: /tmp/rh-c11-boundary-axioms.log. Latest named build /tmp/rh-c11-final-leaf-build.log exit0. Index /tmp/rh-c11-index-alltail.log exit0. Lint /tmp/rh-c11-lint-alltail.log exit1 on ONLY two unrelated unwired modules: RHTower.ShiftedDirichletPolynomialUniqueness and RHTower.ShiftedDirichletTarget. No own-leaf or stale-generated-file error. Global lint not green; don't edit others' files/logs to hide it. All owned handles terminal (including final axiom session63639); process scan follows before final.

## Corpus/frontier reassessment
Read literal RH receivers in ThetaTailFirstMomentDoubleLaplace.lean:817 riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian;846 two-Volterra Krein difference;887 doubleLaplace. They require all finite complex nodes in Re w>1/2. These are receivers, not source sign producers.
Read frontier TH section: fixed-node eventual PD and corrected-Cauchy model positivity do not provide uniform-rank full-source sign. C8-C10 strict Cauchy/boundary comparisons are excluded; C11 now also excludes strict geometric reserve. Avoid confusing positive source entries with PSD. ThetaTailPositiveConeExtensionNoGo is only a continuous countermodel; actual analytic totality has stronger transport.
Latest deep search /tmp/rh-c12-sharp-sign-search.json partial (text_retrieval interrupted), /tmp/rh-c12-quadratic-sign-search.json partial=false. Complete inventories; compiler mostly source_only, semantic coverage unmeasured. Candidate lemmas/source_arguments methods/proof_ideas/ingredient_sets inspected. Generated ingredients concerning entrywise positivity, angular kernels or nonnegative coefficients do NOT establish signed quadratic PSD and were not used. No new primary C12 is frozen. Next work must attack exact full-source sign, not package another receiver.

## Resolved Lean pitfalls
- sqrt measurable composition needs explicit f:=fun t:Real=>z+(t:Complex); otherwise wrong complex-domain translation inferred.
- shifted strip holomorphic simplification needs id_eq.
- min-radius inclusion use Metric.ball_subset_ball, not hw.trans_le.
- Hermitian scalar proof needs simp [map_ofNat] after inner_smul rules; simp alone leaves conjugate(2)=2.
- Type analytic hp on geometricStrip before mono inter_subset_left to avoid intersection metas.
- Complex.sqrt_of_nonneg uses scoped ComplexOrder; real kernel G proof uses indicator integrals and Real.sqrt_mul.
- K secant norm proof uses RCLike.re and RCLike.ofReal_pow, not only Complex casts.
- Typed IntegrableOn lambdas avoid Pi.sub elaboration mismatch.

Previous optimization COMPLETE: mem:rh/root-lean-proof-optimization-2026-09-26 and own card docs/drafts/pipeline/1-in-progress/lean-proof-optimization-root-2026-09-26.md. 46 proof bodies raw heartbeats125,582,673 ->86,464,486 (31.15% less); comparison-rate proof95.52% less. All3named builds and33axiom audits pass, statements unchanged, no limit hacks. No optimization work pending. Prior C10: mem:rh/root-charged-cusp-energy-collapse-2026-09-26.
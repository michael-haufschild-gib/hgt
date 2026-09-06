# EDQ holomorphic unit-phase classification and no-go (2026-09-06)

RH goal remains ACTIVE and UNPROVED. Full chain: literal Euler deletion -> retained chronological remainder or joint signature -> independent orientation INCLUDING EXCEPTIONAL HEAD -> exclusion of every off-line zero -> RH. This session closed a bounded head-factorization audit, not the RH producer. Do not repeat U1/U2 as open conjectures.

## New leaves
- formal/GaloisForLFunctions/RHTower/ArithmeticUnitPhaseRigidity.lean (347 lines, 25 public defs/theorems), namespace RHTower.DeletionMixedRefinement.
- formal/GaloisForLFunctions/RHTower/ArithmeticUnitPhaseNoGo.lean (70 lines, 3 public theorems), same namespace.
Both wired in RHTower.lean after ArithmeticRemainderPhaseCutoff.

Source: B(s)=-(s(1-s))^-1/2, G(s)=B(s)-zeta(s)/(s(s+1)); actual normalizedWeightedRemainder(s,1)=star(G(s)) on minimumStrip. UnitPhaseIdentity U H is the pointwise equality Im(g_s(1))=Im(zeta(s)H(s)) throughout U. UnitPhaseGerm rho says exists H analytic at rho and this identity eventually throughout a neighborhood.

## Exact audited results
1. On connected open U in strip and analytic H, UnitPhaseIdentity iff exists real c, G+zeta H=c throughout U. Open mapping, full conjugation sign checked.
2. unitPhaseBoundary_eq_iff: B(s)=B(t) iff s=t OR s+t=1, for ALL complex parameters. Hence every phase chart contains at most one positive-height zero.
3. On zero-free strip domains every real c supplies analytic H=(c-G)/zeta; on connected open domains these exhaust multipliers.
4. unitPhaseGerm_tangent: at strip zero rho admitting analytic H germ, zeta'(rho)*(H(rho)-1/(rho(rho+1)))=-(1-2rho)/(2(rho(1-rho))^2).
5. unitPhaseGerm_iff_simple_critical_zero (line340): at every positive-height strip zero, germ exists IFF Re rho=1/2 AND deriv zeta rho!=0. Necessity from real B plus nonzero derivative at positive height. Sufficiency constructs H=dslope(c-G,rho)/dslope(zeta,rho), whose denominator is nonzero near rho; identity holds at rho too. Does NOT prove all zeros simple or on wall.
6. exists_unitPhase_positive_zero_above from corpus HardyTheorem.exists_Xi_zero_gt and ZetaCarrier arch-factor nonvanishing, no computational zero data.
7. not_finite_unitPhaseIdentity_cover n: no Fin n family of open preconnected strip domains with analytic multipliers and identities covers all positive-height strip zeros. IsPreconnected explicitly permits empty domains, handled separately. Finite union of <=1-zero chart sets has bounded imaginary image; Hardy contradicts bound.
8. not_unitPhaseIdentity_strip: no global holomorphic H on whole strip with the identity (one-chart corollary).

## Cards/ledgers
Old docs/drafts/pipeline/1-in-progress/arithmetic-unit-phase-factorization.md MOVED/replaced by docs/drafts/pipeline/5-failed/arithmetic-unit-phase-factorization.md, preserving frozen U1/U2 and positive S1/S2 with dependency-closed paper proof. Canonical certificate: docs/drafts/pipeline/3-formalized/arithmetic-unit-phase-classification.md.
Current-only frontier updated EDQ paragraph line56, route row, terminal row, summary. STATUS new route-independent rule: audit extra properties imposed by certificates, e.g. simplicity beyond location. Existing edq-quartic-remainder-phase-cutoff.md remains in progress with active RH producer unchecked.

## Verification
Combined scratch /tmp/edq_unit_all.lean passes; published rigidity lake env lean clean; no-go source and strengthened empty-domain scratch /tmp/edq_unit_nogo_empty.lean clean, latter byte-identical to published final. Serial LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticUnitPhaseRigidity (9.9s) and ...ArithmeticUnitPhaseNoGo (42s) pass, only those leaves rebuilt; cached dependencies replay existing diagnostics. No full/umbrella builds.
All28 public declarations #print axioms via /tmp/edq_unit_final_axioms.lean and /tmp/edq_unit_axioms.log: ONLY propext, Classical.choice, Quot.sound. All entries parsed/checked, no sampling. No added axiom, placeholder, or computational cert.
Index refreshed, research retrieves capstone. lint --check-generated STILL fails only two unrelated pre-existing missing imports: RHTower.ThetaCuspModularCompactTube, HTGeometry.PolynomialODEJetRankThreeCompactExpansion. Log /tmp/edq_unit_lint.log; global lint not passing. Scoped whitespace/card-link checks pass. All owned Lean sessions completed. No commits by this task; other work in repo may commit concurrently, preserve it.

## Next work
Independent exceptional-head orientation still missing. The holomorphic factorization is terminal globally/finite-cover, and even an infinite local-germ cover would require simplicity as well as RH. Do not equate this scoped no-go with failure of EDQ or all analytic head identities. Existing uniform quartic tail n^2>=t^3 is valid but leaves unit head; frozen linear cutoff t<2pi n, complete-prefix B2, undamped clock C remain separately open and unchanged. Continue corpus-driven search for actual cumulative/head source law or joint-signature orientation rather than rebuilding receiver labels.

Tools: Serena Lean symbol APIs explicitly ignore Lean path; use rg/read fallback. One foreground Lean process per agent, cwd formal, lake env lean scratch, targeted leaf final audit only. No subagents authorized. update_plan unavailable; pipeline card used for tracking. Skills l7 read/announced. Local analytic helper RHTower.analyticAt_dslope_of_analyticAt in AnalyticDividedDifference; Metric.isConnected_ball is namespaced. HasDerivAt.fun_mul/fun_div and convert! avoid complex instance mismatches. ContinuousAt.eventually_ne supports local quotient denominator.
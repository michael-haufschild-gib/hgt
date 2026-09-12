# HB: actual left-QNM metric equation and complete correction exchange

Goal remains ACTIVE; fixed-clock extinction and RH NOT proved. Do not mark blocked for mathematical difficulty. Work in /Users/michael/Documents/code/hgt. Own fact/no-go log now has 34 entries: docs/drafts/pipeline/1-in-progress/hb-extinction-own-research-log.md. Own paper card: hb-radiative-source-period-attack.md. Foreign frontier/STATUS/physical-mode-action cards remain read-only for this work. No subagents were spawned.

## Closed this turn

1. formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLeftQNMMetricEquation.lean, 526 lines; namespace RHTower.D4BMLeftModeRadialEquation. SHA256 6b1f301768d6cdc239699c1811570a7e18bb31702c08cb29cade70bae2c785fe. Scratch /tmp/hb-left-mode-radial-equation.lean passed. Isolated cached exact-leaf lake build passed 133s, 2 jobs; helper /tmp/hb-left-qnm-metric-audit.py and log /tmp/hb-left-qnm-metric-audit.log. Published five olean/ilean/trace artifacts, source hash guarded. Wired once after BMMixedCorrectionBoundary.
- profile_derivatives and profile_smooth: original continued tortoise modes for BOTH prescribed fundamental QNM frequencies (side Bool) AND BOTH original radial normalizations (outer Bool). Y'=Y1, Y1'=(w^2-lambda*horizonCoordinate)Y. Smoothness follows current corpus TwistedRadial.contDiffOn_of_linear_ode, source checked, not supplied.
- profileSecond_hasDerivAt differentiates the actual smooth potential; radius_derivatives closes the third lift derivative. radiusLiftThird df ddf dddf r = [r*dddf(tortoise r)-3*(r^2+1)*ddf(tortoise r)+8*r*df(tortoise r)]/(r^2-1)^3.
- radius_master_defect: original VectorStream.master and masterFirst at -w reduce to c*(D-lambda*A), c1*(D-lambda*A).
- metricField (line266): actual mixed metric reconstructed from original radial mode, exp(-w*tau), literal coexact angular vector. fullMetricJet line274; metricField_jet line367 proves actual ordered full metric two-jet at original modePoint (time zero).
- angular_equation line401 uses literal reader eigen-equation. metricField_einstein line413 gives zero original cosmological Einstein linearization in ALL16 components at that ORIGINAL TIME-ZERO ACTION SLICE. Do not claim this statement is global in time or a boundary theorem.
- metricField_is_original_stream line505 identifies the field with reconstruction from actual physicalLeftModeStream temporal/radial derivatives on ENTIRE exterior, any time. Original clock/frequencies unchanged.

2. formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLeftQNMCorrectionExchange.lean, 95 lines; namespace RHTower.D4BMLeftQNMCorrectionExchange. SHA256 67e4964565ef0ffbf97ecadbbe856b92b5d2598fbf5b6508832dc01389c56ca5. Scratch /tmp/hb-left-qnm-correction-exchange.lean passed after one symmetry helper repair; log /tmp/hb-left-qnm-correction-exchange-check.log empty. Isolated cached exact-leaf audit passed 290s, 2 jobs; helper /tmp/hb-left-qnm-correction-exchange-audit.py, log matching -audit.log. Published artifacts/hash guarded. Wired once after new metric leaf.
- leftJet actual ofMetricField at original modePoint.
- leftJet_symmetric proves all actual metric derivative slots symmetric, no assigned slots.
- testResidualWork_zero uses actualJet_eq and new source-derived Einstein equation.
- complete_mixed_exchange WBCQ:
Delta C = W0(M)*L B_ppm + W0(A_pm)*E2(P,M) + W0(A_pp)*E2(Q,M) + boundaryDefect(P,A_pm,M)+boundaryDefect(Q,A_pp,M).
Both test residuals in previous WBC removed, source-proved. All original mixed coefficient/correction slots, independent source copies and scalar/vector amplitudes, changing volume/inverse weights retained through WBT. No correction equation supplied. This is a LOCAL discrepancy identity, not integrated source extinction or a zero value of original action.

Both new leaves only set autoImplicit false. No heartbeat/depth/transparency hacks, no computations/axiom printing. One owned foreground Lean process at all times. All own Lean/scratch/audit processes terminal. Index ran once after final declarations: scripts/formal_tools.py index succeeded (3 changed). scripts/formal_tools.py lint --check-generated passed with existing large-file warnings. No full or umbrella build. Shared foreign edits preserved; no commit/push.

## Source-level comparison / positive no-go salvage, PAPER ONLY
Own card top XP/XF/XFU; own log34. For X=[(dS tensor dT+dT tensor dS)/2]^TF:
div X=(lambdaS+lambdaT)d(ST)/4+(lambdaS-lambdaT)(S dT-T dS)/4.
Derivation by covariant product rule, mixed Hessians cancel trace derivative; actual scalar equations supply eigenvalues. Source/marked reader same-copy lambdaS=rho(rho-1), lambdaT=rho(rho-2)/4; difference rho(3rho-2)/4 nonzero at Xi occurrences. Does NOT prove current nonzero or HB impossible. If a mixed shift-two inverse (2-Delta)U=ST were admitted, its Hessian cancels only d(ST) piece; no mixed inverse constructed here.
Positive second pass: J=S dT-T dS, original bilinear coexact convention (T_y,-T_x), gives <J,*dT>=-div(ST *dT); density -T(S_x*T_y-S_y*T_x) dxdy=-d(ST dT). Upper horizontal outward flux of ST*dT is -ST*T_x dx. With a different scalar response U, <J,*dU>=-div(ST *dU)+2S<dT,*dU>. Mismatch coefficient alone does not obstruct integrated cancellation. These are PAPER calculations, not new Lean results or full E2 identification. No route retired.
Actual-channel check: original D4BMQuadraticMixedSource.tensor squareCovector=*d(S^2/2), gradientCovector=*d(y^2*(Sx^2+Sy^2)/2). Pairing with *dT is ordinary gradient product: <*dF,*dT>=div(F*dT)-lambdaT F T. XF does NOT erase that scalar/vector overlap. This recovers own log15; do not rediscover as a new extinction mechanism.
Horizontal evenness search hit BMEisensteinActualSignedFourierUniqueness (read82–135): actual raw/completed Poincare functions even in absolute-convergence parameter domain. Not yet transported here to every continued literal/correction/boundary. Do not assume every complete channel odd.

## Search record
Six files in formal/.lake/hb-extinction-scratch:
left-full-equation-source-deep.json: partialtrue57366files, semantic Qdrant budget timeout;
left-metric-derivative-methods.json and complete-work-translation-variational-deep.json: partialfalse57366;
tensor-principal-source-cancellation-deep.json and cross-reader-tensor-current-methods.json: partialfalse57370;
cross-reader-coexact-parity-methods.json: partialfalse57373. All latterfive noerrors. Candidate/method/ingredient views inspected; most compiler metadata pending. Adopted smooth-ODE lemma kernel checked. Recent broad reciprocity/virial/rigidity search read https://arxiv.org/html/2609.04169v1 (Vu etal Sep3, sections2,3.2–3.3). Finite-network transpose reciprocity versus PSD distinction; no Einstein/positivity theorem imported.

## Next actual hard attack; avoid circles
Do NOT redo left residual verification or claim another local equation selects Xi zeros. Substitute actual translated causal quadratic/cubic correction fields into WBCQ, identify E2(P,M) and E2(Q,M) for ORIGINAL distinct source/reader frequencies and angular parameters, and derive integrated cancellation with every face/contact retained. XP is only a tensor-component lead. Own log15/26 already retain scalar overlap and finite-translation onset defect/past cap; neither is zero.
Read current foreign updates before new work. Most recent source inspections: BMVectorVectorQuadraticSource full1–155 (closed same-mode tensor); BMScalarScalarQuadraticSource1–150; BMQuadraticMixedSource1–160 (same-mode scalar/vector source plus correction). These same-mode formulas cannot be polarized into the distinct reader without verifying incidence. Foreign BMAngularTwoTensor/PrincipalTensor cancel original same-scalar principal tensor; cusp-growth work ongoing. Do not edit foreign files.

Lean implementation lessons: Matrix/projection rewrite diamonds repaired by a scalar average helper and exact application, not transparency settings. In general use typed local functions, convert!/using! for local definitional diamonds. ActualJet_eq is public; don't unfold huge actualJet. Do not edit live scratch files or start dependent Lean before terminal process. Final leafaudit took290s with no errors; do not infer hang from silence. All owned handles11448/12363/71645/56177/57949 terminal, yielded functions cell1659 complete.

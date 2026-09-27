# Exterior moment cancellation: support, exact Gamma rate, shrinking frequency profile

## Status
Active goal remains a formal RH proof. RH and uniform square-root control of the original signed remainder are UNPROVED. This turn made verified progress; do not mark goal complete or blocked. Repo /Users/michael/Documents/code/hgt/formal. No own build process remains live. No subagents, commits, pushes, full builds, umbrella builds, numerical experiments, new axioms, sorry, or heartbeat increases.

## Finished leaves: 43 public theorems
All under GaloisForLFunctions/RHTower; all audited with `lake --old env lean FILE -o .lake/build/lib/lean/...olean`; each wired exactly once at RHTower.lean around lines1466–1471. Final object timestamps all newer than sources. Final axiom audit imports last leaf and prints all43 theorems: only [propext, Classical.choice, Quot.sound]. Audit scratch /Users/michael/Documents/Codex/2026-09-26/new-chat-2/work/CCMExteriorMomentAxiomAudit-b3wi293e.lean removed. No own pending source repair.

1. CCMCoherentExteriorSupportGauge.lean (9 public)
Imports prior CCMCoherentMidpointMomentAction. Defines s_n=ccmMidpointExteriorShiftAt a r n=2a+|r|+1+n, exterior E_n=half(U_-s_n f-U_(r+s_n)f).
- Physical increment support projection P kills E_n exactly.
- Full COMPLEX inner <delta,E_n>=0, hence action invariant under any complex multiple, extending old real symmetry.
- P(momentCancelledField)=P(original odd field), so this exterior correction cannot reduce supported odd cost.
- Exact norm split of corrected field into supported original odd field plus invisible residual.
- ||E_n||<=||f|| for arbitrary SoninL2; ||E_n||²=||f||²/2 for aperture sources.
Key names: ccmIncrementSupportProjection_exteriorOddAt_zero, inner_increment_exteriorOddAt_zero, ccmGammaIncrementAction_exteriorOddAt_complex_invariant, ccmIncrementSupportProjection_momentCancelledField, norm_sq_momentCancelledField_support_split, norm_sq_ccmMidpointExteriorOddFieldAt.

2. CCMCoherentExteriorMomentTradeoff.lean (10 public)
Imports1. beta_n=ccmMidpointExteriorFrequencyAt a r n=2pi(s_n+r/2)=beta0+2pi*n >0 and tends to infinity.
M(r)=ccmActualHeadMidpointSignedMoment (2a) N r, B3(r)=ccmActualHeadMidpointCubicMoment (2a) N r.
Correction C_n=(M/beta_n)E_n; O_n=O-C_n; S_n=S-(M/beta_n)sin(beta_n*xi); B_n=B3+|M|beta_n².
- P C_n=0, action unchanged.
- C_n->0 in ordinary L²; O_n->O.
- ||C_n||²=(M/beta_n)²||f||²/2.
- EXACT INVARIANT line115 `ccmActualHeadMomentCorrectionAt_energy_budget_product`:
  ||C_n||² (B_n-B3)=|M|³||f||²/2.
Useful names tendsto_ccmActualHeadMomentCorrectionAt_zero, tendsto_ccmActualHeadMomentCancelledFieldAt, norm_sq_ccmActualHeadMomentCorrectionAt.

3. CCMCoherentExteriorMomentSpectrum.lean (8 public)
Imports2. Exact Fourier AE formulas for E_n and O_n; norm²O_n=integral S_n² |Ff|². B_n>=0, |S_n(xi)|<=|xi|³ B_n/6.
J_n=-2 sin(pi*r*xi)S_n, |J_n|<=(|pi*r|/3 B_n)xi⁴.
Current against delta preserved, exact spectral current integral equals original complete prime-plus-terminal field current. No Fubini exchange.
Key names abs_ccmActualHeadMomentCancelledSineAt_le, abs_ccmActualHeadMomentCancelledCurrentAt_le, re_inner_increment_momentCancelledFieldAt, re_inner_increment_completed_eq_momentCancelledAt_spectral.

4. CCMCoherentExteriorMomentGammaLimit.lean (8 public)
Imports3. kappa(h)=ccmGammaHigherBinetDualDensity h=exp(h/2)(exp(2h)-1), nonnegative for h>=0.
Proves M*sqrt(kappa(|r|)) in MemLp2, directly from every actual prime quantile cell and oriented terminal cell as compactly supported continuous indicators. No form-domain premise: arbitrary aperture L² source.
E_M(T,N)=ccmActualHeadSignedMomentGammaEnergy T N=integral M(T,N,r)² kappa(|r|), integrable and nonnegative.
Uniform-in-r beta_n>=2pi(n+1).
C_Gamma(n)=ccmActualHeadMomentCorrectionGammaCost a N f n=integral ||C_n(r)||² kappa(|r|), integrable, >=0.
Bound line132: C_Gamma(n)<=((||f||²/2)/(2pi(n+1))²) E_M(2a,N).
Limit line149: C_Gamma(n)->0 for FIXED aperture and cutoff. Main names integrable_ccmActualHeadSignedMomentGammaDensity, ccmMidpointExteriorFrequencyAt_lower, ccmActualHeadMomentCorrectionGammaCost_le, tendsto_ccmActualHeadMomentCorrectionGammaCost_zero.

5. CCMCoherentExteriorMomentGammaRate.lean (3 public)
Imports4. Fraction q_n=2pi(n+1)/beta_n belongs [0,1] and tends to1 for eachr.
Exact rate theorem line55 `tendsto_ccmActualHeadMomentCorrectionGammaCost_scaled`:
  (2pi(n+1))² C_Gamma(n) -> (||f||²/2) E_M(2a,N).
Proof normalizes the density as (||f||²/2)q_n² M²kappa and applies dominated convergence with bound M²kappa. FIXED a,N; no uniform arithmetic cutoff bound claimed.

6. CCMCoherentExteriorMomentBoundaryLayer.lean (5 public)
Imports5.
- Global frequency bounds: |S_n-S|<=|M|/beta_n; |J_n-J|<=2|M|/beta_n. Thus corrected symbols converge uniformly back to originals as exterior shift grows.
- Exact profile error: |beta_n S_n(y/beta_n)-M(y-sin y)| <= (|y|³ B3/6)/beta_n².
- `tendsto_ccmActualHeadMomentCancelledSineAt_boundary` aroundline85: beta_n S_n(y/beta_n)->M(y-sin y).
- `tendsto_ccmActualHeadMomentCancelledCurrentAt_boundary` aroundline112: beta_n² J_n(y/beta_n)->-2(pi*r*y) M(y-sin y).
This locates the cancellation in a shrinking frequency window; original arithmetic signed factor survives. It does NOT provide uniform control of the actual signed remainder.

## Mathematical significance / remaining task
An exact action symmetry can cancel first frequency moment with correction cost tending to zero even in full Gamma-weighted norm. The price is growing cubic budget, with exact field-cost/budget invariant. The shrinking frequency profile exhibits the surviving signed arithmetic moment. These results do not control M as aperture/cutoff grows, do not reduce physically supported cost, and do not prove RH.
Keep pursuing original signed-current bound; don't present the correction bound as a remainder bound.

## Searches / existing infrastructure found (avoid duplicating)
Use corpus tool `python3 ../scripts/formal_tools.py research ... --mode lexical --no-refresh --budget-seconds 45 --per-module 0 --limit ...`, then direct Lean, no cards.
- CCMCoherentPhaseCostReduction already removes real reflected component after support projection, exact Gamma savings; no need rebuild that 2x2 projection.
- Quantile boundaries b_N=2log(1+P_N/2), P_N=sum criticalMellinAtomWeight belowN. Cell mass integral exp(h/2) = Lambda(n)/sqrt(n).
- Tentative displacement-moment telescoping is ALREADY present in CCMActualHeadOutgoingQuantileCosinePhaseNormalForm: `ccmActualHeadOutgoingQuantileMomentError_eq_displacementMoment`, `ccmActualHeadOutgoingQuantileCosinePhaseProfile_secondDeriv_zero_eq_displacementMoment` line740.
- CCMActualHeadOutgoingQuantileCompletedCharacteristicSeam.lean line740 `ccmActualHeadOutgoingQuantileCompletedCosinePhaseSymbol_secondDeriv_zero` proves completed curvature =4pi²[sum w_n log²n +(2exp(T/2)-(2+P_N))*T² - integral0T exp(h/2)h²]. Terminal orientation retained, including overshoot. Symbol definitions at539–548. Read excerpts only; files >500lines.
- Possible next bridge (NOT proved this turn): relate new integrated r*M directly to existing completed curvature: expected Phi''(0)=-4pi integral r*M. Then Cauchy with E_M and integral r²/kappa may quantify conserved curvature charge. Need prove all integrability/normalization; no guessed claim of new mathematical theorem.
- Another possible investigation: minimum Gamma cost over exact-current fibres, beyond existing phase-only projection. Searches `current minimum` and `current projection` did not return a CCM minimizer, but have not exhaustively established absence. Search direct Lean before building.
- Existing exterior cosine superoscillation and Jordan-mass wall modules already show approximation/mass tradeoffs; don't duplicate or infer global positivity from compact approximation.

## Lean API lessons
MemLp has no `.congr`. Use `.ae_eq` (declaration `MemLp.ae_eq hfg hf`) or memLp_congr_ae. Integrable.congr does exist.
MemLp.integrable_norm_pow converts p2 to integralnorm²; in Integrable.congr sometimes `dsimp only` needed before rw Real.norm_eq_abs, but in DCT filter_upwards it made no progress and was removed.
`memLp_finsetSum` current camelCase; HasCompactSupport.memLp_of_bound and compact Icc continuous bound suffice for cell integrability.
For q in[0,1], use `pow_le_pow_left₀ hq.1 hq.2 2` then one_pow, not nonlinear tactic guesses.
Positivity cannot infer sign of opaque beta_n: supply `(ccmMidpointExteriorFrequencyAt_pos a r n).le` explicitly.
field_simp often closes simple normalized identities completely; remove following ring. Boundary file now has no warnings.
Use `squeeze_zero_norm`, then add_const target, for scalar rate limits. `mul_div_cancel₀ a hb` is b*(a/b)=a. `mul_div_assoc` rewrites a*b/c to a*(b/c).

## Operational verification
Shared compiled dependencies repeatedly disappeared during other work. Restored only required missing dependency leaves, foreground, one own Lean process at a time; source of those leaves unchanged. Eventually all six own leaves passed; all43 axioms passed together. No ongoing own process. A dependency emitted a tactic info suggestion despite exit0; no warning from final own leaves.
Index refreshed successfully: LEAN_API.md, LEAN_GAPS.md, LEAN_OVERVIEW.md and search DB. Final `git diff --check` passed. Global lint --check-generated failed ONLY on28 unrelated unwired concurrent modules, no stale-generated errors and none of our six flagged. Do not wire unfinished other work.
Unwired RHTower: CCMPositiveFrequencyGramSaving, CCMPositiveFrequencyMeasure, MobiusMomentMatchedAssembly, MobiusMomentMatchedFamily, MobiusMomentMatchedPacket, MobiusMomentSimplexSelector, MobiusThreeWindowExtraction, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, TiltedRiemannKernel, ZetaZeroDensityPowerSaving.
Unwired HTGeometry: AlgebraicGroupDerivationCoordinates, AlgebraicGroupGenericPoint, AlgebraicGroupInvariantDerivations, AlgebraicGroupIsogenyTail, AlgebraicGroupRationalPointEvaluation, AlgebraicGroupTangentMap, FixedAdjoinIndependentDescent, FunctionFieldJetBasis, FunctionFieldJetExtension, FunctionFieldJetField, IsogenyFunctionFieldLevel, MaurerCartanFixedFields, MaurerCartanJetCoordinates, SchemeStalkPoints, SchurKernelOperator, SquareZeroPointLifts.

# EDQ joint first-jet exclusion — 2026-09-07

RH goal remains ACTIVE and unproved/unfalsified. Full chain Euler deletion -> exact complex zero balance -> signed arithmetic separation -> exclude every off-line zero -> RH. Current and previous turns made authoritative Lean progress. Do not count local radii/cofinal witnesses as RH; do not mark blocked for mathematical difficulty.

CRITICAL CORPUS CORRECTION: actual unconditional simple-critical density IS AVAILABLE, contrary to earlier EDQ notes/search conclusions. Read current formal/GaloisForLFunctions/RHTower/Zeta23SimpleCriticalDensity.lean. Imports Zeta23.FinalMult; manifest pins https://github.com/anthropics/formal-math.git revision cac1c55684ee31ed76a4c0573e974c01794851c5. Cached olean exists. Public theorem eventually_superlinear_xiSimpleCriticalZeroCount gives 1/(72*pi)*T*log T <= xiSimpleCriticalZeroCount T eventually. Also two_thirds_simpleCritical_epsilon, two_thirds_le_liminf_xiSimpleCriticalRatio, exists_pos_le_liminf_xiSimpleCriticalRatio. New-only axiom audit of THIS turn's actual-witness assembly confirms all inherited dependencies, including provider, only propext/Classical.choice/Quot.sound. No old explicit axiom recheck. Do NOT repeat obsolete claim that corpus lacks actual cofinal simple critical zeta zeros. XiSimpleCriticalSuperlinearConsumer.not_linear_bound_of_superlinear makes finite-count extraction straightforward.

NEW CLOSED LEAF: formal/GaloisForLFunctions/RHTower/ArithmeticJointJetExclusion.lean,253 lines,10 theorems+2 defs, namespace RHTower.DeletionMixedRefinement. Imports ArithmeticEvenReflectionExclusion and Zeta23SimpleCriticalDensity (cached; only new leaf built).

Quantitative source bounds:
- norm_reflectionTargetQuadraticCorrection_le_four hs ht: full odd R(s) norm<=4 for open strip and |t|>=1. First rational numerator controlled by3u^3, both normSq factors >=u^4, hence first term<=3; full mean term<=1/12 using all four height factors. Rounded total<=4.
- abs_hardyResponseNormalizationRate_im_le_two ht: |Im(k)|<=2 for |t|>=1 (each reciprocal critical denominator norm<=1).
- hardy_first_jet_at_offline_zero_le line108: actual off-line strip zero, |t|>=1, delta=s.re-.5, H=hardyZ t, then |H|+|H'|<=48*t^2*delta^2. OFF-LINE premise required; do NOT apply at a critical zero. Odd disk yields norm(Z')<=49delta^2/12, hence corrected Hardy slope |J|<=49t^2 delta^2/2; even theorem |H|<=7t^2delta^2; |Im(k)|<=2 gives combined bound (actual sum constant45.5, rounded48).

Defs hardyFirstJetSize t=|H|+|H'|, hardyFirstJetRadius t=sqrt(hardyFirstJetSize t/(96*t^2)).
hardyFirstJetRadius_pos: t!=0 and jet size>0 -> positive radius.
zero_in_hardyFirstJetRadius_is_critical: open strip, |t|>=1, actual first-jet size>0, |delta|<=radius, zeta(s)=0 -> s.re=.5. Factor-two reserve forces jet<=jet/2 if off-line. Keeps critical zero itself; NOT a zero-free-segment claim.

Actual provider:
exists_high_simple_critical_xi T: exists t>T, t>0, xi(c)=0, (analyticOrderAt xi c).toNat=1. If none, every cumulative simple-critical finset is subset of the fixed finset at T; count constant bound contradicts existing superlinear provider. No density or RH premise.
hardy_derivative_ne_zero_of_simple_critical_xi: actual order-one Xi zero at c gives H=0,H'!=0. Uses xi_analyticOrderAt_eq_riemannZeta_of_mem_strip, ENat.toNat_eq_iff_eq_coe, analyticOrderAt_deriv_of_pos, and existing zeta/Hardy derivative interface.
hardyFirstJetSize_pos_of_simple_critical_xi: hence actual jet size positive.
critical_response_ne_zero_of_simple_critical_xi line219: L_full(t)+V(c)!=0 there. Exact Hardy norm identity with H=0 forces H'=0 if response vanishes, contradiction.
exists_high_critical_zero_with_jet_exclusion line232: above EVERY T actual t>=1 with zeta(c)=0, H'!=0, critical arithmetic response!=0, positive literal radius, and ALL strip zeros at same height inside radius are critical. This handles actual critical-zero heights where prior amplitude floor fails.

Limits: first jet can vanish at a multiple critical zero. Requiring first-jet positivity everywhere would add simplicity; actual Mathlib RH definition (RiemannZeta.lean185) only locates zeros, no multiplicity condition. Positive density of simple critical zeros does NOT cover remaining zeros, and a positive radius need not reach strip edges. Need nonlocal arithmetic orientation/coverage, not just more local-radius wrappers. Exact even and odd source constraints remain; global RH missing.

Docs: card docs/drafts/pipeline/3-formalized/edq-joint-jet-exclusion.md. Frontier current paragraph+EDQrow updated to actual provider, joint radius, cofinal nonzero critical response. STATUS derivative-vanishing rule strengthened with actual noncancellation witnesses; new route-independent multiplicity/coverage rule. Umbrella import appended only.

Verification: final scratch47992 exit0/no diagnostics; leaf build99241 exit0 ONLY new leaf6.3sec, dependencies cached10982jobs. Axioms4957 exit0 all12 new declarations std3 only, includes full inherited Zeta23 provider closure. Lint5608 exit1 ONLY5 unrelated unreachable: RHTower.ThetaCuspFactoredReflectionBound, ThetaCuspFactoredReflectionError, ThetaCuspSharpFiniteCooling; HTGeometry.FirstAtomOddScaleSevenBounds, LogarithmicLaplaceScoreBounds. Don't report older0 or7error status as current. Index47143 exit0 1changed0removed. All owned processes terminal; no owned joint-jet Lean/lake process remains. /tmp/edq_joint_jet.lean and /tmp/edq_joint_jet_axioms.lean removed. Logs /tmp/edq_joint_jet.{check,build,axioms,lint,index}.log retained. No full/umbrella build, no old axiom recheck. Don't rebuild/re-audit finished leaf.

Lean details:
- Generic first-jet order proof: analyticOrderAt_deriv_of_pos ha (n:=0) (by simpa using orderOne) yields derivative order0. (analyticOrderAt_eq_zero.mp h).resolve_left (not_not.mpr ha.deriv) gives derivative!=0.
- ENat.toNat_eq_iff_eq_coe _ 1 converts toNat1 to order1.
- Avoid broad simp of normSq critical denominator with local C0 let: simpa only [show c.im=s.im by simp[c,criticalResponsePoint]] using reflection_target_normSq_lower c.
- convert of u^8<=C*C0 into (u^4*u^4)<=C*C0 generated spurious normalization issue; explicit calc u^8=u^4*u^4:=by ring; _<=...:=mul_le_mul... worked.
- hder from abs_sub (J) (bH), unfold J and use add_sub_cancel_RIGHT. Re-fold |J| via change before combining upper bounds.
- Norm identity at H=0,response0 simplifies to 0=(H')^2; use nlinarith to get derivative zero, not Eq.symm directly.

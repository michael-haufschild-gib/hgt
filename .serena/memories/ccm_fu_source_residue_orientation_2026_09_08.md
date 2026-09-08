# CCM-FU: source scalar and actual physical residue orientation CLOSED

Active unbudgeted RH proof/falsification goal remains UNFINISHED, not blocked. Previous goal turn classification: PROGRESS, nine new checked/audited public theorems establish the exact source sign and eventual actual head-average orientation. No update_goal called. Full chain: actual divisor source -> renewable signed reserve -> exhaustive selection -> uniform signed Abel bound -> RH.

Explicit user override persists: frontier map docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md is READ ONLY even when replayed goal text says update. It was read, NEVER edited this turn. STATUS read; no edits (new parity fact is route-specific). No subagents authorized/spawned. No commits/pushes. No numerical experiments. One owned foreground Lean process at a time; no full/umbrella/large builds. Exact new leaves wired into RHTower. Known lake build packaging audit still pending due broad stale dependency rebuild; don't rerun huge preflight/build. User permits needed oleans only. One small missing prerequisite FinitenessTransition.olean was rebuilt exactly using lake env lean; no old theorem axiom audits.

## Nine new public theorems in three leaves
All path prefix formal/GaloisForLFunctions/RHTower/.
1. ZetaThreeHalvesLogMoment.lean (~113 lines)
 - eulerLogMass_three_halves_gt : (64/17:ℝ) < eulerLogMass (3/2).
 - Private f(x)=log x*x^(-(3/2)), primitive=-(2logx+4)*x^(-(1/2)).
 - Proves derivative of f, antitonicity on Ici2 via log2>2/3, primitive derivative and zero limit, integral2∞ f=(2log2+4)/sqrt2.
 - Real log-series summability from existing ZetaFisherVariance; AntitoneOn.integral_le_tsum_comp_add 2 and zero first two terms identify full eulerLogMass. sqrt2<17/12 yields >64/17.
 - Final scratch67145 exit0. Exact emission22831 exit0.

2. DivisorSourceNegativeHalfReflection.lean (~118 lines)
 - zetaChi_negative_half : zetaChi (-(1/2))=-1/(4*(Real.pi:ℂ)).
 - logDeriv_zetaChi_negative_half : logDerivχ(-.5)=cast(log(8π)+γ-2-π/2).
 - divisorSourceEntire_negative_half_eq : B(-.5)=cast((D+cZ-Z²/(4π))/(4π)), with D=eulerLogMass(1.5), Z=eulerMass(1.5), c=log(8π)-γ-2-π/2.
 - Exact Gamma_R recurrence and off-pole condition give χ value; quarter digamma/reflection/recurrence give derivative. Differentiate actual FE on neighborhood Re(s)<0. Existing real zeta and derivative series identify D/Z.
 - Final scratch80339 exit0 (mathematical header added while run in progress, no proof change; subsequent exact-file check includes it and passed).
 - Exact emission91197 exit0.

3. DivisorSourceResidueOrientation.lean (~114 lines)
 - divisorSourceEntire_negative_half_lower : 1/(272π)<(B(-.5)).re.
 - divisorSourceEntire_negative_half_pos : 0<(B(-.5)).re.
 - divisorSourceEntire_negative_half_im : (B(-.5)).im=0.
 - divisorCoreMellinPairResidue_oriented_pos P hNonempty hPrime : 0<(-1:ℝ)^(P.card+1)*(divisorCoreMellinPairResidue P).re.
 - eventually_mobiusDivisorDilationMean_oriented_pos P hNonempty hPrime : ∀ᶠY:ℝ in atTop,0<(-1:ℝ)^(P.card+1)*mobiusDivisorDilationMean P Y.
 - c>-1 uses log24=3log2+log3, π>3,π<3.15,γ<29/50 and existing exact log bounds. 0<Z<=3 from absolute source zeta bound. D>64/17. Bracket>64/17-3-3/4=1/68; divide4π.
 - Product(1-sqrtp)=(-1)^card product(sqrtp-1), latter positive. Residue=-B(-.5)*product*J with existing J>0. Physical limit gives strict eventual orientation.
 - Actual W_P is eventually POSITIVE for ODD nonempty cores, NEGATIVE for EVEN nonempty cores. No uniform threshold or discrete release sign yet.
 - Final scratch43895 exit0; exact emission78445 exit0.

All nine audited ONCE in external scratch84676 exit0: [propext, Classical.choice, Quot.sound] only. No public defs in these leaves; private helper proofs included in closure audits. No sorry/native_decide/added axiom. Final global formal lint38151 passed, only unrelated pre-existing large-file warnings. Index25955 passed (4 changed files). Scoped git diff --check passed. All three new imports follow MobiusDivisorDilationMean in RHTower.lean. New sources remain untracked intentionally (no commit requested).

## Cleanup COMPLETE
All owned temp files removed:
 /tmp/ccm_residue_sign_api.lean
 /tmp/ccm_negative_half_reflection.lean
 /tmp/ccm_log_moment_lower.lean
 /tmp/ccm_residue_orientation.lean
 /tmp/ccm_residue_orientation_audit.lean
 /tmp/ccm_residue_orientation_lint.log
 /tmp/ccm_residue_orientation_index.log
Final ps scan shows NO live lake env lean, /lean, or lake build process (exit1 no matches). No owned tool session remains live. Keep needed new oleans and small FinitenessTransition cache.

## Documentation current state
- MOVED docs/drafts/pipeline/2-fully-proven/ccm-fu-divisor-source-residue-sign.md to 3-formalized/ccm-fu-divisor-source-residue-sign.md. Stage2 source was untracked from preceding turn; no stub retained. One incoming stage1 link was updated.
- Stage3 sign card has complete paper proof, all nine exact names, validation and remaining arithmetic obligations.
- Updated stage1 ccm-fu-fixed-core-correlation-contour.md and ccm-fu-fixed-core-signed-head-moment.md: source scalar and actual W eventual parity CLOSED; discrete integral and changing-core renewal OPEN.
- Updated stage3 ccm-fu-fixed-core-correlation-contour.md and ccm-fu-fixed-core-physical-dilation-mean.md with companion sign links; removed stale open scalar-sign claims.
- Updated stage1 ccm-fu-fixed-core-prime-correlation.md: exact next source identity and detailed block-integral proof target.
- No frontier or STATUS edit.

## NEXT direct source task: discrete prime-correlation integral
Already existing exact series theorem:
 MobiusDivisorFixedCorePrimeCorrelationLimit.lean: hasSum_mobiusDivisorPrimeCorrelationMass P hP hp hpP gives sum of signed masses = κP-κ(insert p P).
 Mass n is ρ(insert p P)*(Phi_n(1/n)-Phi_n(1/(n+1))) for n>0, and0 at n0.
 rho(insert p P)=Sieve.squarefreeDensity*product(q/(q+1)).
 Phi_n=mobiusDivisorPrimeCorrelationPrimitive P p n, definition at line77:
 2*[a_n*a_(n/p)*t +(2/3)*(a_n*sqrtp*b_(n/p)+b_n*a_(n/p))*t*sqrtt
       +b_n*sqrtp*b_(n/p)*t²/2].
 a,b=mobiusDivisorHeadBlockSlope, mobiusDivisorHeadBlockIntercept.
 Existing exact rational-sample affine theorem is mobiusDivisorInterpolatedHead_eq_block_affine; called in line97 of correlation limit.
 G_P(M/r) equals actual clipped rational head (MobiusDivisorContinuousHeadMoment.mobiusDivisorContinuousHead_div).

Target exact new theorem, p prime outside finite prime P:
 κP-κ(P+p)=2ρ(P+p)p^(-3/2)*W_P(p).

Concrete paper bridge (NOT YET Lean):
 1. For real u in (n,n+1), prove G_P(u)=a_n sqrtu+b_n and G_P(u/p)=a_(n/p) sqrt(u/p)+b_(n/p).
    Actual finite Mobius dilation, unit head square-root interpolation, floor division by positive Nat. Include n/p=0 inactive blocks.
 2. Differentiate -Phi_n(1/u):
      d/du[-Phi_n(1/u)] =2sqrtp G_P(u)G_P(u/p)/u³.
    The three terms are u^-2,u^-5/2,u^-3. Exact endpoints give Phi_n(1/n)-Phi_n(1/(n+1)).
 3. Sum unit intervals n>=1 using absolute integrability. Existing real-ray |G_P(x)|<=C_P sqrtx bounds the kernel by a multiple of1/u², all tails included. Thus existing mass series equals2sqrtpρ*integral_(u>1)G_P(u)G_P(u/p)/u³ du.
 4. Substitute u=p*x. G_P(x)=0 at x<=1 removes lower segment. Factor sqrtp*p/p³=p^-3/2. This proves desired physical identity.
 Once exact bridge closes, eventual W parity can orient κP-κPp for distant primes. Uniform renewable reserve still requires quantitative changing-core and every-cutoff control; fixed-core signs do NOT close RH.

Inspected useful source files:
- MobiusDivisorFixedCorePrimeCorrelationLimit.lean first110 lines and symbol inventory: definitions above, summable_abs_mobiusDivisorPrimeCorrelationMass at293, abs_mobiusDivisorPrimeReleaseCoefficient_sub_prefix_le at304, hasSum... at322.
- DivisorContinuousUnitMoment.lean first85: divisorContinuousUnitHead_between {k}(hk:1<=k){x}(k<=x)(x<=k+1) gives K_k+(sqrtx-sqrtk)*primeFreeDivisorDefect k; unit head zero x<=1; complex primitive equals actual integral.
- MobiusDivisorContinuousHeadMoment.lean finite dilation definition at46; real rational identity at104; J positivity at260; zero<=1 at267.
- DivisorContinuousHeadRegularity.lean contains floor formula measurability proof and real-ray bound, but does NOT assert G_P continuous or its unit-block affine formula.
Prefer direct block integration over introducing a generic weighted Riemann-sum theorem unless corpus already supplies a better exact bridge. Search whole corpus and current source before writing new Lean.

## Important local Lean/API lessons
- Lean toolchain4.32.2 typeclass diamonds: use convert! rather than convert when converting HasDerivAt or ordered real statements. Plain convert generated fake goals Real.instAddCommGroup=Real.normedCommRing.toAddCommGroup or Real.instLT=...!
- Negative rationals under functions: -(1/2) and -1/2 produce syntactically distinct subterms after norm_num; use canonical -(1/2) consistently and simp only[neg_div] when connecting old statements. Same -(1/4).
- Nat.cast_nonneg argument is (α:=ℝ), NOT (R:=ℝ).
- Complex.Gammaℝ_eq_zero_iff does not rw directly under ≠: intro h; obtain⟨n,hn⟩:=iff.mp h.
- To cancel Γ_R in χ value, establish hg' as Γ_R(3/2)=Γ_R(-.5)*(-1/(4π)), then rw[mul_comm,mul_div_assoc,div_self hne,mul_one]. field_simp/ring alone normalized gamma arguments inconsistently.
- Complex.natCast_log has implicit {n}; use (n:=2), not positional2. Cast numeral rewrite requires simpa only[Nat.cast_ofNat].
- HasDerivAt.mul for FE generates Pi/function compositions. simp only[Pi.mul_def,Function.comp_def,id_eq,affine_point_identity,mul_neg_one,mul_neg,mul_one,←sub_eq_add_neg] matches explicit derivative.
- isLittleO_log_rpow_atTop and tendsto_rpow_neg_atTop are GLOBAL, not Real.namespace.
- (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero gives logx/x^r ->0. Then rpow_neg yields logx*x^-r.
- integral_Ioi_of_hasDerivAt_of_nonneg' has derivative on Ici a, positivity on Ioi a, limit atTop. Automatically discharges integrability, no assumed domain.
- Set membership isn't normalized by linarith: give show (2:ℝ)<=x from hx or show2<x from hx.
- Integral comparison coerces Nat2 as ↑2: norm_num only[Nat.cast_ofNat] at hbound before rw exact integral.
- sum_add_tsum_nat_add2 norm_num unfolds private f and cast(n+2); simp only[f,Nat.cast_add,Nat.cast_ofNat] on target before rw shifted equality.
- Finset.prod_mul_distrib and Finset.prod_const prove neg-product factor; no prod_neg_distrib name in this mathlib.
- (-1)^card square=1: rw[←pow_mul,mul_comm P.card 2,pow_mul];norm_num.
- No extra scratch axioms check old library needed.

Prior complete proof state in mem:ccm_fu_physical_dilation_mean_limit_2026_09_08 and mem:ccm_fu_literal_mellin_contour_limit_2026_09_08. Do NOT re-audit or rebuild these completed leaves unless genuinely needed cache missing.

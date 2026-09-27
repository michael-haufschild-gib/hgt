# Full complex coercivity for far integer-log gaps; positive arithmetic Noether potential

## Status and verification
RH remains unproved/unfalsified. Goal ACTIVE; completion requires a formal RH proof. This was a progress turn with nine verified new modules, including genuine sign theorems for an explicitly constructed class. No new blocker, axioms, sorry, numeric experiments, heartbeat changes, subagents, commits, push, full or umbrella builds.
Repo /Users/michael/Documents/code/hgt/formal. Every new leaf below passed `lake --old env lean GaloisForLFunctions/RHTower/Leaf.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/Leaf.olean` individually, final versions without warnings. Twelve endpoint #print axioms checks returned only propext, Classical.choice, Quot.sound. Audit scratch work/noether_far_gap_coercivity_audit.lean deleted. Wired all nine into RHTower.lean lines19736–19744 at time; MainTheorems line28 already imports RHTower. Index refreshed, final lint --check-generated has NO stale generated files and NO own unreachable modules. It exits1 for five other-work unwired modules: MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, XiCriticalResidualPhaseGap, ZetaZeroDensityPowerSaving. Preserve others' work. Initial final lint caught concurrent stale LEAN_GAPS/LEAN_OVERVIEW; re-index + lint fixed staleness. All own processes terminal.

Predecessor details: `mem:research/noether_integer_log_gap_decay_prime_sensitive_polarization_2026_09_27`.

## Mathematical progression
Previous exact bound: for two radius-r balls centered c1<c2, l=c2-c1-2r>=threshold and entire Ioo(l,c2-c1+2r) avoiding ALL log n,n>=2:
4r<=exp(-l), |C|<=exp(1/2)/4 exp(-l/2)*(M1+M2), and |Q(phi+psi)-Q(phi-psi)|<=exp(1/2)exp(-l/2)*(M1+M2).
This turn proves local diagonal coercivity independently of centers, combines it with that decay to prove full positivity for both signs, extends to all complex phases, constructs nonzero families at arbitrary separation, and shows positive coupling/modulus increase coexisting with strictly positive full energy. Finally constructs actual positive-baseline arithmetic phase potential and conserved Noether flow.
IMPORTANT: These far-gap results require the WHOLE supporting-ball difference interval to avoid every integer logarithm. They are NOT general prime-power-gap results or positivity for all sources. Mere sparse support avoidance does not imply that containing interval is free. No RH implication beyond a new verified positivity region.

## Nine new leaves under GaloisForLFunctions/RHTower
### 1. CCMSmoothSourceRecentering
Namespace RHTower.
- ccmTranslatedSmoothSource_physical_coeFn: form translation h has physical representative u(x+h).
- ccmSmoothSourceQuadratic_eq_of_translate: any two smooth sources u:a,v:b with v(x)=u(x+h) have identical FULL Q, even unrelated apertures. Embed both translated vectors into common A=a+b+|h|, compare actual physical functions by Lp.ext + embedding injectivity, apply existing full translation invariance.
- ccmSmoothSourcePhysicalMass_eq_of_translate: same exact physical L2 mass via translation of integral.
- CCMComplexSmoothInteriorSource.recenter u b c hs: source v(x)=u(x+c), hs:tsupport u subset Ioo(c-b,c+b). Smoothness, compact support via comp_homeomorph, support via tsupport_comp_subset_preimage.
- exists_ccmSmoothSource_center_independent_gap (line92): ∃delta,C>0, forall apertures a and actual smooth complex u, any center c, tsupport u subset ball c delta => C*physicalMass(u)<=Q_a(u). Uses existing small-aperture positive ground energy at d/2. Constants independent of center and ambient aperture.

### 2. ThetaRealTranslatedCoercivity
- ccmSmoothSourceFormVector_eq_add_smul u v w s hw: pointwise w=u+s*v implies exact form-vector relation; reuses existing combo construction.
- ccmCompactRealProfileEnergy_eq: Q_a(source(k*phi))=thetaRealArithmeticQuadratic phi.
- thetaRealArithmeticQuadratic_compact_parallelogram: Q(phi+psi)+Q(phi-psi)=2Qphi+2Qpsi for compact real Schwartz profiles, transported from existing actual form parallelogram.
- thetaGroundNormSq_nonneg (namespace RHTower, not ThetaSourceWard).
- exists_thetaReal_center_independent_gap: same delta,C uniform local gap for compact real Schwartz phi in physical theta ground mass Mphi=thetaGroundNormSq(thetaComplexify phi).

### 3. ThetaFarIntegerLogGapCoercivity
- exists_thetaReal_farIntegerLogGap_coercivity:
∃R,kappa>0, forall compact real Schwartz phi,psi in equal-radius balls (r>=0), if R<=l and whole difference interval excludes ALL log n,n>=2, then BOTH
kappa*(Mphi+Mpsi)<=Q(phi+psi),
kappa*(Mphi+Mpsi)<=Q(phi-psi).
Proof chooses local delta,C then R=max(threshold+1, max(-log(4delta)+1, 1-2log C)), kappa=C/2. Width bound forces r<delta; closure support lies in closedBall r subset ball delta. Cross coefficient <=C. Parallelogram + |Qplus-Qminus|<=C totalMass gives both lower bounds. No assumed positive diagonal or spectral bound; local gap is proved internally.

### 4. ThetaComplexGroundComponents
Namespace RHTower.ThetaSourceWard.
- thetaRealComponent chi=chi.postcompCLM Complex.reCLM; thetaImagComponent similarly.
- apply/add/sub simp laws; support subsets; compactness transfer.
- thetaGroundNormDensity_realImag and thetaGroundNormSq_realImag: exact physical mass splitting.
- thetaGammaPolarQuadraticDensity_realImag; thetaPrimeScalingCrossDensity_realImag and integrated cross splitting.
- thetaFullArithmeticQuadratic_realImag: Q_full(chi)=Q_real(Re chi)+Q_real(Im chi), all Schwartz chi, all Gamma/prime/pole terms retained. Uses integrable densities and direct complex algebra.

### 5. CCMFarIntegerLogGapCoercivity
- exists_thetaComplex_farIntegerLogGap_coercivity: same uniform R,kappa gap for arbitrary compact COMPLEX chi,eta, both sum and difference. Real+imag decompositions preserve supporting balls and add exactly.
- support_ccmThetaGroundProfile: support(u/k)=support u (strict positivity of k).
- hasCompactSupport_ccmThetaGroundProfile.
- ccmThetaGroundProfile_combo_add/sub: profile of actual combo u+v / u-v equals profileu +/- profilev.
- exists_ccm_farIntegerLogGap_coercivity (line77): actual full source statement for all a,u,v supported in such balls; kappa*(norm embedding u squared + norm embedding v squared)<=Q_a((u.combo v u 1 0).vector), and same with -1 for difference. Arbitrary complex phases/amplitudes allowed; supports and arithmetic gap are exact domain conditions.

### 6. ThetaFarPositiveBumpPairs
- thetaGroundNormSq_pos_of_ne_zero: any Schwartz chi nonzero at a point has strictly positive ground mass. Integrable continuous nonnegative density with positive theta weight; integral_pos_of_integrable_nonneg_nonzero.
- exists_farIntegerLogFree_bump_pair(T): genuine nonnegative real compact Schwartz phi,psi with supports EXACTLY ball0r, ballcr, r>0, T<=c-2r, phi0>0, psi c>0, full difference interval all-integer-log-free. Uses exists_atomFree_mem_Ioo between maxT0+1 and maxT0+2, atom-free eps neighborhood, r=min(eps/8,1/8), actual ContDiffBump inner r/2 outer r converted to Schwartz. No computations/sampling.
- exists_arbitrarily_far_positive_thetaPair(T): same actual family plus Q(phi+psi)>0 and Q(phi-psi)>0. Applies coercivity at max T R and nonzero mass. Proves positivity class nonvacuous at arbitrary separation.

### 7. CCMFarGapPhaseCoercivity
- support_ccmCosLocalizedSource_subset / sin analogue.
- ccmCosLocalizedSource_combo / sin analogue: localization commutes with arbitrary complex source combinations.
- exists_ccmFarGap_phaseEnergy_gap (line54): same uniform R,kappa family, for EVERY Schwartz angle theta and phase t,
kappa*(Mu+Mv)<=ccmPhaseLocalizationEnergy(u+v,theta,t).
No binary-angle assumption, no sign assumption on either localization error. Applies complex source coercivity independently to cosine and sine components and uses exact physical mass conservation for each original source. This is positive actual energy along all local phase rotations in the far complete-integer-gap class.

### 8. ThetaFarPositiveInterference
- thetaGammaPolarGroundCrossPairing_pos_of_balls: nonnegative phi,psi whose supports equal ball0r,ballcr, r>0 and c-2r>threshold have strictly positive actual continuous cross pairing C. Proof on compact closed-ball rectangle: continuous kernel beyond threshold, integrable, nonnegative, positive on open product rectangle of positive volume, zero outside closed rectangle. No arithmetic exclusion needed for this cross-only statement.
- exists_arbitrarily_far_positive_modulus_increase(T) (line90): genuine compact profiles phi,psi in arbitrarily far equal balls with (phi+psi)(x)=|(phi-psi)(x)|, equal ground mass for plus/minus, C>0, and
0<Q(phi-psi)<Q(phi+psi).
Derived from previous actual positive family + exact all-channel polarization. This shows modulus increase can persist even where full energies have been proved strictly positive. Do not call it a negative Q example. Endpoint retains supports, gap and modulus/mass facts, but does NOT retain the prime-exclusion statement (available in proof/previous family if needed).

### 9. CCMPositiveNoetherPhaseWitness
- exists_ccmArithmetic_positive_baseline_phase_potential:
∃actual a,u,compact theta,B with Q_a(u)>0 and B>0;
E(q)=ccmPhaseLocalizationEnergy u theta q = Q_a(u)+B(1-cos q),
HasDerivAt E (B sin q) all q, and E(q)>0 all q.
Construction: far positive modulus witness, compact separating theta=0/pi on the two tsupports; u=k(phi-psi), v=k(phi+psi). cosLocalized u=v and sinLocalized u=0. General binary-angle phase identity plus E(pi)=Qv>Qu yields B=(ErrPrime-ErrContinuous)/2>0. No unproved prime or energy assumption. This endpoint does not state prime localization error zero; do not infer it from signature alone.
- exists_ccmArithmetic_positive_noether_flow (line111): same Q(u)>0,B>0 and compact theta; E=Qu+arithmeticPhasePotential B; E(q)>0; exact conserved
(deriv(flow B q) t)^2/2 + E(flow B q t)=Qu+2B+1;
trajectory Newton law q''=-E'(q).
Reuses established time-translation invariant action, inverse travel-time trajectory, Noether charge. IMPORTANT flow is selected positive-speed energy curve (energy 2|B|+1 relative to baseline), not arbitrary initial velocity; kinetic term was chosen in inverse-Noether construction, not canonical arithmetic dynamics. Current result adds a proved positive actual baseline.

## Lean tactics / repairs
- Common aperture positivity needs explicit linarith [a.2,b.2,abs_nonneg h], not bare positivity.
- ccmArchimedeanFormEmbedding norm is definitionally same as restricted aperture norm. `change ... at hf` useful.
- To combine localized energy lower bounds, first rewrite original masses using `rw [←hmu,←hmv]`, then nlinarith only [hc.1,hs.1]. Passing mass equalities into nlinarith directly failed because multiplying equalities by kappa introduces higher-degree monomials.
- IsCompact closed-ball product needs explicit args: `(isCompact_closedBall c r).prod (isCompact_closedBall (0:ℝ) r)`.
- Rewriting support equalities directly via `hps.symm ▸ hx` fails if target written as phi x ≠0; state membership `x ∈ Function.support phi`, rw hps, then use its definitional nonzero meaning.

## Remaining RH gap and possible next work (UNPROVED PLANS)
No all-source domination, negative full source, or RH proof. The far complete-integer-log-free class is now controlled, including complex phases. Move to genuine prime-power interactions rather than re-proving this case.
Useful next direction: center-independent local gap plus previous actual prime-gap comparison. For source difference interval inside consecutive-prime log cell [log p,log q], continuous cross <=(q-p)/(2sqrt p)*totalMass. Exact full polarization retains prime correction. Need bound active higher-prime-power translations inside that cell, not erase them.
Potential elementary program, not yet formalized:
1. Infinitely often (q-p)/sqrt p is arbitrarily small. Corpus query 'prime gap sqrt small' found no matches, but search more before implementing. Contradict eventual lower bound eps sqrt p using Bertrand sqrt q<=2sqrt p: sqrt q-sqrt p>=eps/3. Then p_n grows at least quadratically, forcing sum1/p_n summable, contradict existing not_summable_nthPrime_reciprocal. Uses no PNT or conjectural gap theorem.
2. For a prime gap q-p<sqrt p, at most one k-th power per exponent k>=2 can lie in (p,q). Consecutive k-th powers differ by at least sqrt of the upper power. Exponents bounded by log_2 q. Thus total von Mangoldt/sqrt weight of proper powers in the cell should have a vanishing bound of order (log q)^2/sqrt p. This still needs full rigorous Lean infrastructure and exact constants; do not claim it proved.
3. Combine that actual prime-correction bound with continuous cross and local diagonal gap to prove positive full source planes in infinitely many genuine prime-log cells, without all-integer exclusion. Larger gaps/general sources remain real RH barrier. Alternatively pursue exact cancellation/weighted operator control directly. Keep full goal intact and active.

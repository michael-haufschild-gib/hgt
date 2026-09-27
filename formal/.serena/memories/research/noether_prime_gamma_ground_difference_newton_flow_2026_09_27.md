# Noether arithmetic current, continuous Gamma energy, CCM domain bridge

## Goal and scope
User changed active goal on 2026-09-27: develop arithmetic conservation into an actual formal RH proof; apply Noether in both directions. Goal is complete ONLY when RH is proved. No RH proof obtained. Do NOT mark complete for finishing this batch. Open-ended conjecture/proof/fail/learn/pivot continues. No extra axioms, no sorry, no numerical experiments, no heartbeat changes; one foreground Lean build at a time; final leaf audits lake --old env lean; no umbrella/full builds. No commit/push by this agent.

Repo /Users/michael/Documents/code/hgt/formal. Other chats concurrently edit/build/commit. Preserve their work. No subagents authorized. Prior batch: mem:research/noether_full_action_exchange_sign_scaling_rigidity_2026_09_26.

## Verified batch (seven leaves)
All below passed final lake --old env lean FILE -o .lake/build/lib/lean/...olean, and all seven are imported in GaloisForLFunctions/RHTower.lean. MainTheorems already imports that umbrella. Do not build umbrellas.

1. ThetaPrimeGammaScalingEnergy (namespace RHTower.ThetaSourceWard)
- Bounded complex profile squared norm lift; absolute integrability and exact source/target marginals, cross pairing.
- thetaPrimeScalingEnergy_eq_diagonal_sub_cross: E_prime = D - 2 C.
- completeTheta_primeShift_symmetric_balance: P(x)+P(-x)=A(x)+A(-x)-2 archConstant*k(x), using actual complete theta source equations at both points. A=Gamma+two polar sources.
- thetaPrimeGammaScalingDiagonal = integral |chi|² Re[k(A+A_reflected-2 archConstant*k)].
- thetaPrimeGammaScaling_identity: D_Gamma - 2 C_prime = E_prime.
- equality iff bounded continuous chi is constant; strict inequality iff nonconstant.
- This diagonal Gamma weight is NOT the full nonlocal Gamma operator.

2. ThetaNoetherHamiltonJacobi
Actual j(x)=Re fullPrimeShiftNoetherCurrent theta theta x, F(x)=Re thetaNoetherExchange x, V(x)=j(0)-j(x), v(x)=sqrt(2*j(x)).
- j>0, j<=j0, j'=-F; V'=F, V>=0, V>0 iff x!=0, V<j0.
- v>0, v²=2j, v<=v0, v'=-F/v.
- S(x)=integral_0^x v; H(x,S')=j0.
- L(x,v)=v²/2-V(x); H=v²/2+V(x); v*dL/dv-L=H.
- Mechanical action integral L(q,q') exactly invariant under simultaneous time translation of q and interval.
- Constructed actual model; not an RH argument.

3. ThetaNoetherNewtonFlow
- Travel coordinate tau(x)=integral_0^x 1/v is continuous strictly increasing and onto R: derivative >=1/v0>0.
- Explicit order isomorphism thetaNoetherTravelIso; q(t)=its inverse, q(0)=0, q'=v(q), q''=-F(q).
- Actual Euler-Lagrange equation and conserved energy j0, without assuming ODE hypotheses.
- Flow(x,t)=q(t+tau(x)); identity and composition law; energy constant. This is a global flow on the one positive-velocity energy curve, not all phase space.
- Final audit green after using convert! to resolve real module instance diamonds and unfolding thetaNoetherFlow in derivative conversion.

4. ThetaGammaPolarScalingKernel
Imports minimal ThetaCuspGammaSourceAction + ThetaCuspPolarSourceAction.
mu(u)=2 cosh(u/2)-exp(-u/2)/(1-exp(-2u)).
- Exact combined Gamma/pole source integrand = a(u)k(x)+mu(u)k(x+u), a=exp(-2u)/(1-exp(-2u)).
- mu=exp(-u/2)*(exp(u)+1-1/(1-exp(-2u))).
- mu(log(5/4))<0 and mu(log 2)>0, both positive shifts.
- All exact symbolic proofs; no numerical approximations.
- Blocks uniform positive-jump interpretation of full Gamma/pole operator; not an RH counterexample.

5. ThetaGammaPolarScalingEnergy
thetaContinuousLinkMeasure=(volume restricted to u>0).prod volume.
Density for S:ThetaSource and chi:Schwartz R C:
mu(u)*S.k(x)*S.k(x+u)*norm(chi(x+u)-chi(x))².
- Absolute integrability on entire ray and line; iterated-integral/Fubini identity.
- Key private bounds:
  |mu(u)| exp(-2u) u² <= (2u²+u/2) exp(-u/2), u>0.
  S.k(x)S.k(x+u) <= C² exp(-2|x|) exp(-2u), u>=0, from S.decay 4.
  Schwartz increment <= seminorm R 0 1 chi * |u|.
- Separable polynomial-exponential integrable majorant. No cutoff or convergence premises.
- Constants use existing HTGeometry.integrable_abs_pow_mul_exp_neg_abs.

6. ThetaGammaPolarGroundDifference
Let a=exp(-2u)/(1-exp(-2u)), b=mu(u), k0=S.k x, k1=S.k(x+u), chi0,chi1.
Diagonal density = k0*(a*k0+b*k1)*|chi0|² + k1*(a*k1+b*k0)*|chi1|².
Quadratic density = a*(k0²|chi0|²+k1²|chi1|²)+2b*k0*k1*Re(chi1*conj chi0).
- thetaGammaPolarDiagonalDensity_actual identifies those coefficients with literal source integrands at x and -x-u (theta evenness), no invented operator.
- Quadratic - diagonal = -continuous jump density pointwise.
- Compensated difference absolutely integrable, integral=-E_cont. No subtraction of divergent integrals.
- thetaPrimeGammaPolarRelativeForm = D_Gamma - 2 C_prime + integral(compensated difference).
- thetaPrimeGammaPolarRelativeForm_eq: Q_relative = E_prime - E_cont.
- Does NOT yet identify Q_relative with full CCM/restricted Weil form or establish positivity.

7. CCMThetaGroundProfile (namespace RHTower)
Imports prior GroundDifference + SuzukiCCMMixedSmoothCore.
For every CCMComplexSmoothInteriorSource a, chi=u/k is a Schwartz profile, built from smooth nonzero theta denominator and compact support.
- ccmThetaGroundProfile_reconstruct: k(x)*chi(x)=u(x), pointwise.
- ccmSmoothCore_exists_convergent_thetaGroundProfile: every actual smooth CCM core test has such a profile and both energies integrable.
- This proves coverage of the whole smooth core, not equality/positivity of quadratic forms.

## Audits and cleanup
A scratch audit imported all seven leaves plus existing CCMRestrictedWeilPoleCompressionRHCriterion. 21 #print axioms checks all returned only propext, Classical.choice, Quot.sound. Included main new identities, flow Newton/Euler-Lagrange/energy, continuum convergence, compensated identity, domain coverage, existing riemannHypothesis_iff_parityPole_nonneg and riemannHypothesis_iff_primeGammaPoleInequality.
Owned scratch noether_quadratic_api.lean and noether_completed_axioms.lean deleted from chat work directory.
No sorry/admit/axiom/native_decide/#eval/heartbeat declarations found in seven new leaves.
Index refreshed. Initial lint --check-generated exited1 only for concurrent unrelated unwired modules MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, ZetaZeroDensityPowerSaving, plus API/OVERVIEW staleness caused by concurrent changes after refresh. Second refresh succeeded (3 changed sources). Second lint still saw those unrelated unwired modules plus newly created XiRealAxisGaussianSampling and XiRealAxisSchwartzEnergy, and API/OVERVIEW staleness from concurrent edits. Final refresh after that check succeeded (1 changed source); API/GAPS/OVERVIEW and search DB regenerated. No own build or audit process remains running. No errors concerned the seven new leaves. Do not wire other chats' unfinished leaves or repeatedly chase index churn.

## Existing exact RH endpoint inspected and axiom-audited
CCMRestrictedWeilPoleCompressionRHCriterion:
- riemannHypothesis_iff_parityPole_nonneg: RH iff both ccmPolarParityFormVector a (+1/-1) full-source energies >=0 for every positive aperture.
- riemannHypothesis_iff_weilPoleCompression_nonneg: RH iff |ccmWeilPoleCross a|<=ccmWeilPoleDiagonal a for every aperture.
- riemannHypothesis_iff_primeGammaPoleInequality: expanded literal prime/Gamma/pole arithmetic entries.
- riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound: RH iff integral_0^T(exp(t)-psi(exp t)) dt has uniform O(exp(T/2)) bound.
These are equivalences, NOT unconditional proofs of the needed inequality.
SuzukiPolarTranslateMultiplier:303 identifies source quadratic on smooth CCM test with Suzuki screw form of its derivative; do not lose derivative normalization.
SuzukiCCMMixedSmoothCore contains actual C_c^infty source, toSchwartz, toCCMFormVector and physical a.e. representative theorem.
CCMActualHeadCompletedAutocorrelationProducer: source quadratic = phase constant*norm² + positive Gamma translation energy + actual completed-error autocorrelation current, alternatively higher-Gamma energy + outgoing polar-prime current.
CCMActualHeadGammaAutocorrelationEnergy: ccmGammaTranslationDensity(u)=exp(-u/2)/(1-exp(-2u)), literally the Gamma coefficient above.
CCMRestrictedWeilGammaMixedJump gives convergent mixed Gamma energy on complete form domain.

## Next obligations: full form identification
Need prove Q_relative(chi=u/k) equals actual restricted Weil source quadratic (with exact factors/constants/boundaries).
Pointwise raw quadratic decomposes into:
gamma(u)*|f(x+u)-f(x)|²
+ (a(u)-gamma(u))*(|f(x)|²+|f(x+u)|²)
+ 2*(2cosh(u/2))*Re(f(x+u)conj f(x)).
Here f=k chi; integrate over u>0,x. Gamma term matches existing CCM translation energy. Universal (a-gamma) integral together with -2 archConstant gives actual gammaHardyPhaseRate normalization; retain this constant exactly. Polar cross term matches two exponential pole pairings; prime term is -2 C_prime.
Alternative analytic proof: establish absolute integrability of forward source-density k(x)|chi(x)|²*(GammaTerm+PolarTerms), then reflected/sheared version via measure-preserving (u,x)->(u,-x-u). Its integral is D_Gamma+2 archConstant*norm(f)² by actual source equation. Existing gammaSourceBound integrable and S.decay bounds suffice; no new deep analytic obstruction. Mathlib MeasurePreserving.skew_product can prove shear/reflection measure preservation. Avoid separating singular a and gamma integrals before cancellation.
Then positivity is the real RH obligation; do not rename it an assumption or claim a route complete.

## New conjecture for immediate proof loop (NOT proved yet)
Literal continuous Noether crossing current:
C(x)=integral_{u>0} mu(u) * integral_{y=x}^{x+u} k(y)k(y-u) dy du.
Let j_p(x)=Re fullPrimeShiftNoetherCurrent theta theta x.
Conjecture exact full cut energy:
j_p(x)-C(x)=integral_{t>x} 2*t*k(t)^2 dt, for all real x.
Expected derivation:
C'(x)=Re[k(x)*(A(x)-A(-x))], diagonal a cancels inside integrand.
Existing prime current derivative = this - 2*x*k(x)^2.
Both currents tend to zero at +infinity -> FTC tail identity.
Tail is even and strictly positive (k even, positive); yields unconditional positivity of full arithmetic form on each single-cut theta test. This does NOT prove PSD for combinations: mixed two-cut kernels/cross terms remain the RH difficulty.
Corpus research 'Gamma Noether current' found only old ThetaPrimeShiftNoetherConservation, which integrates the Gamma exchange as an abstract primitive; it does not build literal continuous crossing current. Search 'theta cut energy tail' found only unrelated HedenmalmThetaMovingHorizonBoundary.
Infrastructure:
- Need first-power sibling of current bound: |mu(u)| exp(-2u)*u <= (2u+1/2) exp(-u/2), u>0. Existing proof's hden=2u exp(-2u)<=1-exp(-2u) handles it.
- S.decay4 gives uniform current majorant C²*u*exp(-2u); integrable against |mu|.
- Differentiate interval current via FTC, then use actual gammaSourceTerm and pole bounds to dominate derivative on x-neighborhoods (keep Gamma subtraction intact).
- DCT x->+infty: fixed-u source pair tends0, uniform above ray majorant.
- Mathlib MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' is available, IntegralEqImproper.lean:813, for tail identity.
Do not assert this conjecture already proven.

## Lean API repairs to reuse
- open scoped SchwartzMap for 𝓢 notation.
- norm_sub_le gives |a-b|<=|a|+|b| after Real.norm_eq_abs; abs_sub_le takes THREE arguments and is triangle through middle point.
- Explicitly specify Real.exp_pos (-2*u) in an untyped have; placeholder argument cannot be inferred from later use.
- Seminorm nonneg is apply_nonneg p x (NOT p.nonneg).
- Product AE theorem is Measure.ae_prod_iff_ae_ae.
- simp only [Pi.add_apply] before ring when Integrable.add leaves function addition.
- For abs of norm-square, provide explicit norm-square expression; wildcard sq_nonneg may try to match signed kernel.
- Convert! resolves pervasive real/complex module instance diamonds; often closes goal automatically, so do not append ext/rfl unless needed.
- ContDiff.div uses scalar field as target; for real-smooth complex quotients use ContDiff.mul with ContDiff.inv and convert!, not .div.
- Complex.normSq_sub uses (starRingEnd C), so match that in density cross term.
- Integrable.neg function-instance diamond handled with convert! and pointwise difference theorem.
- No heartbeats raised.

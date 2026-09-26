# Full prime action, sign law, scaling rigidity — completed batch

Active open-ended Noether/arithmetic-conservation goal remains ACTIVE. This batch is progress, not overall completion. No RH proof/disproof or literature novelty claim. Repo /Users/michael/Documents/code/hgt/formal. No subagents or commits/pushes by this agent. Other agents concurrently edit/build/commit shared repo.

Rules: unconditional final results, no custom axioms/sorry/numerical experiments/native_decide; one own foreground Lean process at a time; final leaf audits lake --old env lean; no full/umbrella builds; wire completed modules; no heartbeat increases. Direct Lean corpus search ../scripts/formal_tools.py research ... --mode lexical --no-refresh; no cards.
Prior memories: noether_adjoint_domain_arithmetic_boundary_2026_09_26, noether_arithmetic_prime_shift_current_2026_09_26.

## Seven modules DONE
All under GaloisForLFunctions/RHTower, final leaf audits GREEN with .olean emitted, wired in RHTower.lean. MainTheorems imports RHTower and root imports MainTheorems. Namespace RHTower.ThetaSourceWard except Dilation/Separation in RHTower.

1 ThetaPrimeShiftNoetherVariation
Joint measure count.prod volume on Nat x Real; rho_ST(n,x)=Lambda(n)/sqrt(n)*T.k(x)*S.k(x+log n), stored complex.
Joint continuity/integrability, bounded-profile source/target marginals and transposition.
thetaPrimeLocalResponse = integral Delta chi*rho.
thetaPrimeLocalResponse_eq = integral chi*(-fullPrimeShiftWardDivergence).
thetaPrimeLocalResponse_actual = integral chi*thetaNoetherExchange.

2 ThetaPrimeShiftNoetherAction
A_chi(e)=integral exp(e*Delta chi)*rho, e complex.
Integrability every e; exact density from reciprocal fields p=exp(-e chi)T.k, q=exp(e chi)S.k.
hasDerivAt_thetaPrimeLocalAction at every e, dominated differentiation.
At zero derivative=localResponse; actual derivative=integral chi*W.
thetaPrimeLocalAction_add_const: exact global reciprocal scaling symmetry.

3 ThetaPrimeShiftNoetherArctan
rho real nonnegative, prime2 density strictly positive.
thetaPrimeArctanProfile r(x)=arctan(x-r), bounded continuous.
thetaPrimeLocalResponse_arctan_re_pos S T r, for every pair and center.
Actual specializations integral_arctan_thetaNoetherExchange_re_pos and deriv_thetaPrimeLocalAction_arctan_re_pos.
Strict continuous-integral proof at (2,0), no numeric experiment.

4 ThetaSourceDilation
k_r(x)=exp(-r)*k(exp(-r)x), ThetaSource admission, zero/add action laws.
X_r(w)=X(exp(r)w), conserved total mass X_r(0)=X(0), derivative scaling.
sourceBezoutian_thetaSourceDilation: B_r(w,v)=exp(r)^2*B(exp(r)w,exp(r)v).
Does NOT assert actual fixed-prime/Gamma source equation dilation invariance.

5 ThetaNoetherEulerFluxSeparation
Existing modulated Gaussian negative B witness a+i16/3 (0<a<2pi/3).
Dilation r=log a moves negative witness to Re w=1.
exists_thetaSource_positive_noether_negative_euler_flux:
source with all self-prime currents positive and all arctan responses positive, yet B_S(w,w).re<0 at Re w=1.
exists_thetaSource_no_positive_current_representation:
negative B cannot equal any integral f(x)^2*J_SS(x).re.
Unconditional existence. NOT RH counterexample: this source is not actual theta, no actual Gamma/pole equation asserted.
Positive survivors: action, exact dilation law, actual-source orientation, sharp energy nullspace.

6 ThetaNoetherExchangeSign
Uses existing strictAntiOn_thetaCuspFullSource_mul_reflect at u=0 from HedenmalmCenterMixedThreePoint.
Strict radial theta decrease + |x-log n|<=x+log n: all prime terms nonnegative at x>0, prime2 strict.
thetaNoetherExchange_re_prime_sum: Re W(x)=k(x)*sum_n Re(primeSourceTerm n(-x)-primeSourceTerm n x).
Proved:
thetaNoetherExchange_neg; thetaNoetherExchange_zero;
thetaNoetherExchange_re_pos_iff (0<Re W iff 0<x);
thetaNoetherExchange_re_neg_iff;
thetaNoetherExchange_eq_zero_iff;
strictAntiOn_thetaNoetherCurrent_re on Ici0;
fullPrimeShiftNoetherCurrent_self_neg S x (self-current even for EVERY source);
thetaNoetherCurrent_re_lt_center_iff (actual J(x).re<J(0).re iff x!=0);
integral_thetaNoetherExchange_finite_re_pos_iff (Re integral_0^x W>0 iff x!=0, including negative x).
With prior upper bound, V(x)=J(0).re-J(x).re=Re integral_0^x W obeys 0<V(x)<J(0).re off zero. J'+W=0, J+V=J0. Current positive/even, unique peak at zero, tends0 at +infinity (prior Boundary).
No physical trajectory constructed yet.

7 ThetaPrimeScalingRigidity
E(chi)=integral norm(Delta chi)^2*rho.re.
Continuous/nonnegative density, integrability from bound (2 norm chi)^2, constant-addition invariance.
thetaPrimeScalingEnergy_eq_zero_iff S T chi:
E=0 iff chi=BCF.const R (chi0).
thetaPrimeScalingEnergy_pos_iff: E>0 iff chi nonconstant.
Zero integral -> continuous density identically zero (count.prod volume open-positive).
Positive prime2/prime3 densities give periods log2/log3.
REUSES eq_of_two_dilation_invariance from TwoDilationDivisorMetric, with 2^m!=3^n via prime divisibility.
No duplicate density infrastructure; no Gelfond-Schneider dependency.

## Audit/cleanup
All seven final leaf commands:
lake --old env lean GaloisForLFunctions/RHTower/<leaf>.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<leaf>.olean
GREEN with no final warnings.
20 #print axioms key results: ONLY propext, Classical.choice, Quot.sound.
API scratch passed, axiom scratch passed, both deleted from /Users/michael/Documents/Codex/2026-09-26/new-chat-2/work.
All own build processes finished. No full builds. Own git diff --check passed.
Generated indexes refreshed with guarded formal_tools.py index.
Global lint --check-generated exit1 only for five concurrently-created unrelated unwired modules:
RHTower.AnharmonicCubicCriticalLineOrder, HorizontalIsolationBlockPacket, WindowTransformSamplingParseval, XiHeatSamplingEnergyBound; HilbertMetric.HorizontalLamzouriUnnormalized.
No stale-generated errors at this lint. Pre-existing large-file warnings. Do not wire others' unfinished modules or claim global lint green.

## Useful API lessons
Real->complex current composed with real negation uses HasDerivAt.scomp, NOT .comp.
Typed intermediate derivatives + convert! fix scalar-instance diamonds.
Complex.reCLM.hasFDerivAt.comp_hasDerivAt: convert! h using1; simp [thetaNoetherExchange_eq].
refine hs.tsum_pos ?_ 2 ?_ preserves subgoal order.
BCF scope required. Local count IsOpenPosMeasure via Measure.count_ne_zero; product instance resolves.
integral_re is root. Continuous.ae_eq_iff_eq measure continuous_zero validated.
Narrow Complex.ofReal_mul rewrite avoids push_cast changing real exp into complex exp.
Measure.integral_comp_mul_left may require explicit g.

## Next conjectures to BUILD, not yet formalized
1. Direct arithmetic quadratic identity: expand E into source/target marginals and prime cross term. Sum actual equations at x and -x:
P k(x)+P k(-x)=A(x)+A(-x)-2 archConstant*k(x),
A=gammaSource+two polar sources; multiplication x cancels.
Expected:
E(chi)=integral norm(chi x)^2*k(x)*(A(x)+A(-x)-2 archConstant*k(x)).re
 -2 Re integral conj(chi(source))*chi(target)*rho.
Then nonnegative with equality iff chi constant. Build bounded-profile mixed marginals and integrability. Variation + Rigidity are infrastructure.
Related SuzukiRestrictedWeilForm.weilPrimeBlock_eq_jumpForms is finite/unweighted; do not duplicate it.
CRITICAL: diagonal potential A(k)/k is NOT full nonlocal Gamma operator on arbitrary tests. Do not identify with RH operator without proof.
2. Inverse-Noether physics: j=Re J, F=Re W, V=j0-j; v=sqrt(2j)>0.
Hamilton-Jacobi S(x)=integral_0^x v: S'=v, (S')^2/2+V=j0, v*v'=-F.
Then construct actual global trajectory WITHOUT ODE hypotheses using tau(x)=integral_0^x 1/v.
Since j<=j0, tau'>=1/sqrt(2j0), strictly increasing onto R. Inverse q should obey q'=v(q), q''=-F(q), conserved energy j0.
3. RH gap: generic positive Noether data insufficient by explicit counterexample.
Need express actual RH-equivalent sourceBezoutian packet form (ThetaCuspTiltFluxSourceWeld) through E plus proved nonnegative terms using Gamma/pole structure. No such identity established.
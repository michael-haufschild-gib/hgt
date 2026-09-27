# Active goal and user steering
Unbounded active goal remains proving RH through arithmetic conservation / Noether. RH NOT proved or falsified. Latest user specifically demands control of the full signed remainder at square-root scale, forbids abandoning an unresolved mathematical problem, and explicitly authorizes sustained conjecture/proof/fail/learn loops and building missing mathematics. Do not mark goal complete, blocked merely because RH is hard, or replace the full target by a weaker bound. No subagents/commits/pushes. Continue direct Lean research, not cards. One own foreground Lean process; leaf audits `lake --old env lean file`, no umbrella/full builds, no numerical experiments, no new axioms/sorry/heartbeat increases. Repo /Users/michael/Documents/code/hgt/formal.

## Full target
D(T)=ccmLogChebyshevDeficitPrimitive T = integral_0^T (exp t - Chebyshev.psi(exp t)). Required actual bound |D(T)| <= C exp(T/2), T>=0. Existing CCMRestrictedWeilPoleCompressionRHCriterion proves this equivalent to RH. No such bound constructed. PNT gives only D=o(exp T).

## Completed latest four modules, 26 public theorems
All four leaf audits PASSED and fresh .oleans produced. All 26 #print axioms audits returned only [propext, Classical.choice, Quot.sound]. All four imports wired into RHTower.lean around lines19835-19838. Audit scratch CCMCriticalRemainderAxiomAudit.lean deleted. Older scratch CCMPrimeDeficitAxiomAudit.lean also deleted after its successful31theorem audit. No own Lean process remains after audit49537 completed. Search index final refresh76837 completed exit0 after cleanup (3 changed,0removed); LEAN_API/GAPS/OVERVIEW regenerated. All four .olean mtimes confirmed fresh; both scratch audits confirmed removed. No own process remains. Global lint failed on six unrelated concurrent unwired modules plus metadata races: MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, XiGaussianSampledPerturbation, ZetaZeroDensityPowerSaving, HTGeometry.ComplexSquareEnergyPerturbation. Do not wire other chats' unfinished leaves. Own imports checked; no sorry/axiom/native_decide/#eval/heartbeat hacks; git diff --check umbrella passed.

### CCMPrimePowerSquareRootControl.lean (6 theorems)
Defines P(T)=ccmProperPrimePowerPrimitive=integral(psi(exp t)-theta(exp t)); Dtheta(T)=ccmLogThetaDeficitPrimitive=integral(exp t-theta(exp t)).
- ccmLogChebyshevDeficitPrimitive_eq_theta_sub_proper: D=Dtheta-P, exact signed.
- P>=0 on nonnegative ray.
- exists_ccmProperPrimePowerPrimitive_squareRoot_bound: actual unconditional existsB>=0, P(T)<=B(exp(T/2)-1). Uses mathlib Costa--Pereira psi-theta<=C sqrt x; no log loss.
- ccmProperPrimePowerSource_sub_half_bounds: 0<=psi(exp t)-theta(exp t)-psi(exp(t/2)) <= (log4+4)(exp(t/3)+exp(t/5)), all real t.
- tendsto_ccmProperPrimePowerSource_scaled_one: exp(-t/2)(psi(exp t)-theta(exp t))->1.
- tendsto_ccmProperPrimePowerPrimitive_scaled_two: exp(-T/2)P(T)->2.
Thus proper powers give a known nonzero square-root bias; true prime fluctuations remain unresolved. Final audit exit0 emits a harmless ring tactic informational suggestion, no errors/admissions; all axiom prints clean. Avoid claiming literature novelty.

### CCMPrimeDeficitCriticalEnergy.lean (11 theorems)
E(t)=ccmPrimeDeficitCriticalEnergy=exp(-t)D(t)^2.
W(t)=ccmPrimeDeficitSignedWorkDensity=exp(-t)D(t)(exp t-psi(exp t)).
- ae_hasDerivAt_ccmLogChebyshevDeficitPrimitive; E>=0; E(0)=0; E continuous; W interval-integrable.
- ae_hasDerivAt_ccmPrimeDeficitCriticalEnergy: E'=2W-E a.e.
- ccmPrimeDeficitCriticalEnergy_balance: E(b)-E(a)+integral_a^b E=2 integral_a^b W, all a,b. Absolute continuity handles all prime entries.
- ccmPrimeDeficitSignedWork_nonneg: integral_0^T W>=0 forT>=0.
- ccmLogChebyshevDeficitPrimitive_before_first_prime: D(t)=exp t-1 for0<=t<log2.
- E(t)>0 for0<t<log2.
- not_antitoneOn_ccmPrimeDeficitCriticalEnergy: actual E is not nonincreasing on [0,infinity); fails already before first prime. This refutes only global dissipation from zero, NOT eventual dissipation or boundedness.
This identity holds for any analogous forcing; by itself it provides no special arithmetic upper estimate. Do not treat conserved momentum as a bound on E.

### CCMPrimeDeficitPrimeWork.lean (5 theorems)
- integral_mul_psi_exp_eq_prime_entry_tails: for continuous g, T>=0,
 integral_0^T g(t)psi(exp t) = sum_(1<=n<=floor(exp T)) Lambda(n) integral_log(n)^T g(t).
- ccmLogChebyshevDeficitPrimitive_eq_prime_log_tents: D(T)=exp T-1-sum Lambda(n)(T-log n).
- ccmPrimeDeficitSignedWork_eq_prime_entry_tails:
 integral_0^T W = integral_0^T D - sum Lambda(n) integral_log(n)^T exp(-t)D(t).
- ccmPrimeDeficit_prime_entry_work_le_background: the finite signed prime work is <= integral D (unconditional, although individual tails may be negative).
- ccmPrimeDeficitCriticalEnergy_prime_work_balance: E(T)+integral_0^T E = twice the preceding background-minus-prime-work gap.
This proves the gap nonnegative; the upper bound needed for critical control remains OPEN. Do not take absolute values of individual prime tails or assume their sign.

### CCMPrimeDeficitScaleDescent.lean (4 theorems)
R(T)=ccmPrimePowerDescentRemainder=integral_0^T [psi(exp t)-theta(exp t)-psi(exp(t/2))].
- ccmPrimePowerDescentRemainder_bounds: 0<=R(T)<= (log4+4)[3(exp(T/3)-1)+5(exp(T/5)-1)], T>=0.
- ccmProperPrimePowerPrimitive_eq_half_deficit: P(T)=2(exp(T/2)-1-D(T/2))+R(T), all T.
- ccmLogChebyshevDeficitPrimitive_scale_descent: D(T)=Dtheta(T)-2(exp(T/2)-1)+2D(T/2)-R(T), all T.
- ccmPrimePowerDescentRemainder_critical_bound: |exp(-T/2)R(T)| <= (log4+4)[3exp(-T/6)+5exp(-3T/10)].
This preserves the smaller-scale unknown with an explicitly subcritical error. It does NOT yet bound the same-scale Dtheta term.

## Earlier in this same long turn: 7 modules /31 public theorems, all verified/wired/axiom-audited
These had not previously been put in memory; now record:
1. ExponentialPrimitiveCancellation: locally integrable f with exp(-t)f(t)->0 implies exp(-T)integral_0^T f->0 (one theorem, symbolic epsilon split).
2. CCMPoleLeadingCancellation: D, literal integrated deficit, pole cross, diagonal, and both actual parity energies vanish after exp(-2a) normalization (5 thms). Full pole energy o(exp2a), no sign/critical bound.
3. CCMOddPrimeContinuousCancellation: explicit normalized Codd identity, boundary limits, continuous odd balance/prime operator both tend -2 after exp(-2a), and recent-minus-old prime budget tends2 (6 thms). Their leading negatives cancel in full Q, not an RH counterexample.
4. CCMSmoothPrimeContinuousCancellation: every epsilon>0 actual compact smooth sources with positive physical mass, negative continuous C, and |Q|<epsilon*(-C), at all sufficiently large apertures (2thms).
5. CCMPolePlaneCancellation: |Q(c*p+ +d*p-)| <= (|diagonal|+|cross|)(||c||^2+||d||^2), and uniform o(exp2a) for arbitrary complex coefficients (2thms).
6. CCMPrimeDeficitNoetherAction (11thms): L(t,q,v)=v^2/2-D(t)v; exact position translations; actual q=q0+p*t+integral_0^t D; canonical momentum p; global momentum EL; V(t,q)=-q(exp t-psi(exp t)); Newton a.e.; exp(-t)(q'-p)->0. Time-dependent potential, not conserved mechanical energy.
7. CCMPrimeDeficitForceAction (4thms): ordinary kinetic-minus-potential action differs from invariant action by q(T)D(T); force action under position translation changes by cD(T); constructed trajectory C1; actual endpoint includes boundary symmetry, conserved shifted momentum, Newton a.e.
ThreeWayCancellation.lean documentation corrected (proofs unchanged, leaf audited): its actual proofs are finite substitutions and scalar cancellation under a decomposition premise, NOT full source identification, uniform tail bounds or bounded prime error. Per-mode bounds alone are not summable.
Total current completed batch =11new modules,57 public theorems, all standard axioms. Earlier five-module/19theorem batch recorded in research/noether_finite_prime_stabilization_negative_continuous_invariant_2026_09_27 remains valid.

## Direct-source research for next hard step (not implemented yet)
- CCMFUSuzukiSelbergSquareRootAbelAction: exact weighted signed curvature = terminal normalized Chebyshev error + interior half-order Selberg Abel action + arch remainder. Boundary and interior have opposite signs. This is not a bound.
- CCMFUSuzukiMobiusDivisorDilationChannels.lean:638 mobiusDivisorSquareRootAbelMoment_eq_divisorDefect_kernel collapses to prime-free divisor defect paired with a signed clipped Mobius kernel. Individual dilation estimates lose joint cancellation.
- LocalizedHalfDensityGerm.lean:562 halfDensityInteriorFibre_second_derivative realizes centered ratio-localized Lambda*Lambda pair sum; :596 localizedVonMangoldtPair_eq_integral gives finite product-fibre/Fourier identity with genuine kernel representation hypotheses. Source read; no new coupling to current energy proved.
- PsiRemainderRecursion.lean:34 abs_psiRemainder_recursion bounds |R(N)log N + sum Lambda(k)R(floor N/k)| by400N. SelbergSecondInequality takes absolute values and loses desired sign. To get new gain, retain signed correlation and improve actual remainder, do not assume it.
Possible next route: expand finite prime work into a two-prime overlap kernel and regroup by product with ratio retained, then apply actual divisor/Selberg identities to the UPPER signed-work gap. Algebra suggests infinite critical causal-tent overlap (2+|a-b|)exp(-|a-b|/2); equivalently unnormalized pair kernel (2+|log n-log m|)/max(n,m). This is only a proposed derivation, not yet a proved bridge or bound. Need special arithmetic cancellation beyond the generic energy identity.

## Lean lessons
- Chebyshev.psi_eq_sum_Icc uses Icc0 floor, not1. For Icc1 use definition psi and reverse Finset.Icc_add_one_left_eq_Ioc.
- Annotate `(fun n : Nat => Real.log n <=t)` in filter, otherwise coercion can turn finset into real mapped finset.
- Dot field access on a new line after `(term)` may parse as an argument. Bind a typed local first; then hi.absolutelyContinuousOnInterval_intervalIntegral etc.
- LocallyIntegrable a.e derivative lemma is _root_.LocallyIntegrable.ae_hasDerivAt_integral; use explicit interval integrability proof when field lookup fails.
- AC addition uses .fun_add with constant ContDiff-derived AC, not .const_add (which may resolve to Tendsto).
- Real.lt_log_iff_exp_lt, not Real.exp_lt_iff_lt_log.
- Need simp [Pi.neg_apply,Pi.pow_apply,id_eq] on derivatives of function powers/negation.
- nlinarith cannot infer multiplying exp(-t)*exp(t)=1 by D(t). Factor with ring then rewrite cancellation.
- Several `rw` applications affect one integral at a time. After variable-change on two integrals, `simp only [zero_div,smul_eq_mul,integral_exp,Real.exp_zero]` normalizes both.

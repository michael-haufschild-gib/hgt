# Euler completion, positive renewal, and critical-mass obstruction (2026-09-27)

Active goal remains proving RH through arithmetic conservation/action identities. RH UNPROVED. No global square-root bound obtained. Previous goal turn was progress (global residual reflection); this turn also changes authoritative Lean state with four new leaves / 31 public theorems.

Repo /Users/michael/Documents/code/hgt/formal. User rules: no sorry/custom axioms/computational experiments/heartbeat overrides; one own foreground Lean process; lake --old env lean FILE -o matching .olean; no full or umbrella builds, subagents, commits or pushes; preserve concurrent changes. Four modules wired into RHTower umbrella once. Final validation appended later.

## Mathematics

Use D(T)=ccmLogChebyshevDeficitPrimitive T and Z_a=logarithmicWeightedDilation a. Existing source G=Z_1 D, H=Z_1 Z_1 D. All arithmetic products below are Dirichlet convolution, except explicit pointwise weight masks.

a_P(n)=mu(n) if n divides P, else0: ccmEulerMobius P : ArithmeticFunction Real.
q_P(n)=1 if n>1 and Coprime(n,P), else0: ccmEulerRough P.
w_P=mu-a_P: ccmEulerMobiusTail P.
For positive P this completes a finite Euler product. P=0 is also admitted algebraically (a_0=mu, q_0=0); unboundedness results deliberately use P+1.

Exact identities, all P:
a_P*zeta=1+q_P.
w_P*zeta=-q_P.
DivisorTransform w_P=-q_P.
LogDivisorTransform w_P=-(q_P*Lambda).
q_P in [0,1], q_P*Lambda>=0. Thus both residual transforms are nonpositive.

Factorial completion:
For n<=m, a_(m!)(n)=mu(n) and q_(m!)(n)=0. No factorial computation.
For m=floor(exp(T/2)), T>=0, the existing affine head symmetry gives A_(m!)(T)=D(T), where
A_P=ccmPrimeDeficitEulerAction P=the actual existing ccmPrimeDeficitCoefficientAction at a_P.

## Exact positive recurrence

A generic new identity transfers the full source back to D:
Z_w Z_w H = Z_(DivisorTransform w) Z_(DivisorTransform w) D, every real T.
For Euler completion and T>=0:
D(T)-A_P(T)=Z_qP Z_qP D(T).
This is positive in its coefficient kernel, NOT an assertion D or remainder has positive sign.
The actual signed earlier deficit values remain inside the operator.

Also:
D-A_P=E_P-L_P,
E_P=Z_qP Z_qP Kexp>=0,
L_P=Z_(qP*Lambda) Z_qP Klin>=0,
Kexp=max(exp t-1,0), Klin=max(t,0).
Neither E nor L is assumed bounded, and no cancellation estimate follows from their nonnegativity.

## Exact finite inverse

b_P=q_P^2=ccmEulerRenewalKernel P.
c_(P,k)=sum_{j<k} b_P^j=ccmEulerResolvent P k.
Both b and c have nonnegative coefficients.
q vanishes below2; b^k vanishes below4^k.
For T>=0:
Z_c A_P(T)=D(T)-Z_(b^k)D(T).
If floor(expT)<4^k, the final term vanishes exactly:
D(T)=Z_c A_P(T).
Explicit depth k=Nat.log 4 floor(expT)+1 always suffices.
No infinite sum, convergence, tail estimate, or contraction premise.
The existing arithmetic finite support machinery from Sieve.HeathBrownIdentity is reused.
This is a finite reconstruction identity, not a bound.

## Verified failure of a tempting next conjecture

Critical mass:
M(P,U)=sum_{1<=n<=U} q_P(n)/sqrt(n)
  = ccmEulerCriticalMass P U.
For every natural P,B:
B+1 <= M(P+1, ((P+2)(B+1))^2).
Witness arithmetic progression n=(P+1)j+1, j=1..K,
K=(P+2)(B+1)^2. All terms are coprime to P+1 and >1. Each denominator <=(P+2)(B+1).
Consequently M(P+1,U) is unbounded in U for EVERY fixed positive modulus.

Quadratic kernel mass:
N(P,U)=sum_{1<=n<=U} b_P(n)/sqrt(n)
  = ccmEulerRenewalCriticalMass P U.
M(P,U)^2 <= N(P,U^2).
Proof rewrites the Dirichlet convolution using existing Sieve.sum_Icc_divisorsAntidiagonal_swap and retains the complete product square inside its hyperbola; all omitted terms nonnegative.
Thus N(P+1,U) is unbounded for every fixed positive modulus too.
This formally rejects a uniform positive critical contraction for fixed Euler completion. It does NOT refute RH or bound the signed actual D. A scale-dependent modulus or cancellation inside E-L remains necessary.

## Files / public theorem counts
CCMPrimeDeficitEulerResidual.lean: 11.
CCMPrimeDeficitEulerRenewal.lean: 7.
CCMPrimeDeficitEulerResolvent.lean: 9.
CCMPrimeDeficitEulerCriticalMass.lean: 4.

Corpus search before implementation found existing public mobiusCommonDivisorKernel_eq_coprimeIndicator in MobiusCoprimeIncidence.lean; reused it.
A coprime squarefree sqrt-mass bound exists in Sieve.CoprimeSquarefreeHarmonic but has restrictions on prime-reciprocal sums and even modulus; new elementary progression proof applies to EVERY positive modulus, with no squarefree restriction. No duplicate direct Euler renewal theorem found.
Research search for 'vonMangoldt coprime convolution' and 'arithmetic log convolution derivation' returned none (not proof of universal absence).

## Next mathematical idea, not yet formalized
Retain arithmetic prime forcing explicitly rather than replacing the recurrence by its positive norm.
For rho_P=1+q_P and Lambda_P(n)=Lambda(n) if Coprime(n,P), else0, expect:
rho_P*Lambda_P = pointwise(log * rho_P).
Then q_P*Lambda_P = log*rho_P - Lambda_P.
In particular for n>1 coprime to P:
(q_P*Lambda)(n)=log(n)-Lambda(n).
The full Lambda splits into surviving and deleted prime parts. The latter must not be discarded.
At P=m!, surviving-prime force starts above m, so the b_P*Lambda_P component starts above (m+1)^3; deleted-prime forcing can already enter at 2(m+1)^2.
Potential route: compare the two complete signed work terms using this literal logarithmic-derivative law; positive absolute bounds provably fail at fixed P.
Another option is scale-dependent Euler completion and its exact prime-update action law, but search existing EulerDeletion modules before implementing.

## Lean details
- ArithmeticFunction does NOT have sub_apply or sum_apply in this mathlib. Use sub_eq_add_neg + add_apply + neg_apply; prove sum evaluation/nonneg by range induction when needed.
- For neg_mul under arithmetic-function coercion, rw failed; use congrArg (fun f : ArithmeticFunction Real => f n) (_root_.neg_mul ...).
- q*q is not definitionally q^2; simp only [ccmEulerRenewalKernel,pow_two].
- Nat positivity tactic did not handle 1<=K directly; use Nat.one_le_iff_ne_zero.mpr and positivity.
- Finset.sum_image and sum_Icc_divisorsAntidiagonal_swap need explicit coefficient functions here.
- Nat.cast_nonneg parameter is alpha (Lean alpha symbol), not R.
- field_simp closes the arithmetic progression normalization; no trailing ring.


## Final verification
All FOUR final leaf audits passed sequentially in foreground using lake --old env lean FILE -o matching .olean. Final CriticalMass audit has no warnings (removed unreachable trailing ring). Combined 31-public-theorem #print axioms audit exited0; every theorem uses only [propext, Classical.choice, Quot.sound].
Four objects fresh, exactly one umbrella import per leaf, no forbidden constructs/trailing whitespace. git diff --check umbrella passed.
Temporary /Users/michael/Documents/Codex/2026-09-26/new-chat-2/work/EulerRenewalAxiomAudit-lrjnhfs1.lean removed.
Index first attempt exited1 from InterruptedError in filesystem traversal; second attempt succeeded and wrote API/GAPS/OVERVIEW metadata, search index refreshed.
Final global lint exited1 for 13 unrelated unreachable modules and stale LEAN_GAPS.md / LEAN_OVERVIEW.md during concurrent work. No own module errors. Do not claim global lint clean or repeat these gates without new cause.
Unreachable modules at final lint: RHTower.ClusterNodeFrame, CompositeResolventDivision, MobiusDiscretePacketGeneralOrder, MobiusDiscretePacketHorizon, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, RiemannKernelCuspSeries, XiGaussianHeatChannelTransfer, XiWindowQuotient, ZetaZeroDensityPowerSaving; HTGeometry.ExponentialLagrangeContour, PolynomialExtrapolationRemez.
Last scoped git status: four new leaves untracked, umbrella modified. Concurrent work preserved. No commits/pushes. All own process handles terminal; no own live build, index or lint process.
Goal remains ACTIVE; RH remains unproved. The positive fixed-modulus contraction conjecture is disproved, while the original signed prime-force cancellation problem remains open.

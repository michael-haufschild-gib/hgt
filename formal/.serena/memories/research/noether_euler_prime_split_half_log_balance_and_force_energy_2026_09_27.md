# Euler prime split, half-log balance, and complete-force coefficient energy (2026-09-27)

Active goal remains proving RH via arithmetic conservation/action identities. RH UNPROVED; no global square-root bound for the signed time-domain deficit. Previous turn was progress (Euler completion + positive recurrence + fixed-modulus critical-mass obstruction). This turn adds six leaves / 45 public theorems; validation appended after completion.

Repo /Users/michael/Documents/code/hgt/formal. Scratch /Users/michael/Documents/Codex/2026-09-26/new-chat-2/work.
No full/umbrella builds, subagents, commits, pushes, custom axioms, sorry, computational experiments or heartbeat overrides. One own foreground Lean process; final leaf checks lake --old env lean FILE -o matching .olean.

## Reused infrastructure
Search found RHTower.logDerivation and logDerivation_mul in LocalizedHalfDensityCurvature.lean. Imported/reused rather than duplicating logarithmic derivation.
Search found Sieve.sum_card_divisors_sq_div_le_polylog in CriticalDivisorAffineMeanSquare.lean:
sum_{1<=n<=N} tau(n)^2/n <= (1+log N)^4 for N>=1.
This is the coefficient moment used for the new energy estimate.
Search 'coprime vonMangoldt convolution' and 'coprime projection convolution' found no direct match.
Search 'prime power coprime convolution' found CoprimeFiberStabilization.convolution_prime_power, a generic INTEGER arithmetic-function prime-power convolution expansion, not yet a mixed p^k*n deleted-force channel law.

## Notation
a_P=ccmEulerMobius P.
q_P=ccmEulerRough P (indicator n>1 and Coprime(n,P)).
rho_P=ccmEulerCoprime P=1+q_P (1 is the Dirichlet identity).
S_P=ccmEulerSurvivingPrime P=pointwise rho_P*Lambda, equivalently Lambda(n) if Coprime(n,P), else0.
J_P=ccmEulerDeletedPrime P=Lambda-S_P.
b_P=ccmEulerRenewalKernel P=q_P^2 (Dirichlet convolution).
Arithmetic logarithmic derivation Lf(n)=f(n)*log n is existing logDerivation.
Time deficit D(T)=ccmLogChebyshevDeficitPrimitive T and A_P=ccmPrimeDeficitEulerAction P.
Z_f=logarithmicWeightedDilation f.

## Prime split and logarithmic generator
rho_P is completely multiplicative on all naturals, including its map-zero convention.
Both S_P,J_P are nonnegative and S_P+J_P=Lambda.
Exact:
L rho_P = rho_P*S_P.
L q_P = (1+q_P)*S_P.
(q_P*S_P)(n)=q_P(n)log n-S_P(n).

Dual retained-Euler dynamics:
L a_P = -a_P*J_P.
(a_P*J_P)(n)=-a_P(n)log n.
L^2 a_P = a_P*(J_P*J_P)-a_P*L J_P.
a_P*L rho_P - L a_P*rho_P = (a_P*rho_P)*Lambda.
These use a_P*zeta=rho_P and Mobius inversion. They do not assert an unforced system or conserved positive energy.

## Exact half-logarithmic force balance
L b_P=2*(b_P+q_P)*S_P.
Coefficient statement:
b_P(n)log n=2(b_P*S_P)(n)+2(q_P*S_P)(n).
All terms on RHS nonnegative.
Consequently (b_P*S_P)(n)<=b_P(n)log n/2.

Work definitions:
ccmEulerSurvivingWork = Z_(b*S) Klin.
ccmEulerDeletedWork = Z_(b*J) Klin.
ccmEulerLogMomentWork = Z_(L b) Klin.
ccmEulerLowerPrimeWork = Z_(q*S) Klin.
Existing full ccmPrimeDeficitEulerPrimeWork is exactly survivingWork+deletedWork.
Exact moment balance M=2*survivingWork+2*lowerPrimeWork.
lowerPrimeWork>=0, so survivingWork<=M/2.

For T>=0, COMPLETE signed error:
D-A_P=EulerExponentialWork-M/2+lowerPrimeWork-deletedWork.
Every term is retained. No bound on E-deletedWork has been assumed.

## Cubic causality for factorial completion
q_(m!) and S_(m!) vanish below m+1.
b_(m!) vanishes below (m+1)^2.
b_(m!)*S_(m!) vanishes below (m+1)^3.
Thus if floor(exp T)<(m+1)^3:
survivingWork=0;
fullPrimeWork=deletedWork;
M/2=lowerPrimeWork EXACTLY.
For T>=0 in that window:
D-A_(m!)=EulerExponentialWork-deletedWork.
The remaining deleted force includes prime powers of primes dividing m!; it cannot be discarded.

## Arithmetic support orthogonality
q_P,b_P and b_P*S_P vanish when n is not coprime to P.
b_P*J_P vanishes when n is coprime to P.
Therefore (b_P*S_P)(n)*(b_P*J_P)(n)=0 at every arithmetic index.
Hence exact coefficient Pythagoras:
(b_P*Lambda)(n)^2=(b_P*S_P)(n)^2+(b_P*J_P)(n)^2.
The equality survives every finite carrier and every external real weight.
This is COEFFICIENT orthogonality, not a claim that delayed/summed time profiles are orthogonal.

For arbitrary finite I:
sum_I (b*S)(n)^2/n <= 1/4 sum_I (b(n)log n)^2/n.
No smallness of the RHS was assumed.

## Uniform complete-force energy (final audit outcome appended)
b_P(n)<=tau(n), from q in [0,1].
The logarithmic derivative of zeta^2 gives
L(zeta^2)=2*zeta^2*Lambda.
Monotonicity of positive finite convolutions yields:
0 <= (b_P*Lambda)(n) <= tau(n)log n/2.
Combining with existing harmonic square-divisor estimate yields, uniformly for ALL P and N>=1:
sum_{1<=n<=N} (b_P*Lambda)(n)^2/n
 <= (log N)^2/4 * (1+log N)^4.
By exact support orthogonality, the SUM of surviving and deleted critical coefficient energies obeys the SAME bound.
This controls the actual complete prime-force coefficient energy with an explicit logarithmic scale. It does not prove pointwise square-root control of D(T) or E_P(T)-primeWork_P(T); the transfer between arithmetic delays still needs cancellation.

## New leaf files / public counts
CCMPrimeDeficitEulerPrimeSplit:10.
CCMPrimeDeficitEulerForceBalance:9.
CCMPrimeDeficitEulerPrimeCausality:9.
CCMPrimeDeficitEulerDeletedDynamics:4.
CCMPrimeDeficitEulerForceOrthogonality:8.
CCMPrimeDeficitEulerForceEnergy:5.
All live in GaloisForLFunctions/RHTower.

## Next mathematical work
The coefficient-energy estimate is not a time-domain bound. Need a signed/oscillatory transfer that preserves cancellation between E and primeWork; crude Cauchy-Schwarz reintroduces a factor from carrier length.
A precise further conjecture:
For prime p dividing P, n coprime to P, and k>=1,
(b_P*J_P)(p^k*n)=log(p)*b_P(n).
Deleted force should vanish when an index has two distinct prime divisors shared with P. This would resolve deleted forcing into disjoint small-prime channels and may support sharper shifted-energy estimates. NOT formalized yet; search existing EulerDeletion/Sieve smooth-support infrastructure before implementing.
The mathematical reason: b only supports coprime indices, while J only supports prime powers sharing P; all bad-prime valuation must lie in the J factor.
Do not claim the resulting channel energies alone give RH.
Another possible direction: Mellin/logarithmic generator balances connect the existing half-density normalization to the arithmetic cutoff, but generator identities alone do not supply positive conserved coercive energy.

## Lean details
- Explicit ArithmeticFunction Real products are Dirichlet convolution; pointwise masks use ArithmeticFunction.pmul.
- ArithmeticFunction lacks sub_apply/sum_apply here: use add_apply, neg_apply, sub_eq_add_neg.
- mul_le_one0 lemma (Lean subscript zero) argument order is a<=1, 0<=b, b<=1.
- Reused logDerivation_zeta is stated with nat-cast zeta but matches Real arithmetic zeta.
- Final force energy split normalizes 1/n times squares using div_eq_mul_inv, one_mul, mul_comm.


## Additional next bridge found in current source
Sieve.GeneralAffineMeanSquare.lean:138:
integral_Icc_normSq_LSeries_le_general_affine hs0 hsupp sigma hT
bounds finite-supported LSeries mean square by generalMeanSquareConst + generalMeanSquareRate*T for T>=1.
At sigma=1/2 the constant charges sum F(n)^2 and the rate charges sum F(n)^2/n.
Constants are 5*pi*exp(1) and 5*pi/2 respectively.
The new harmonic force energy controls the rate uniformly in P.
The ordinary coefficient mass should be bounded by
(log N)^2/4 * N*(1+log N)^3
using the already inspected Sieve.DivisorSquareMoment.sum_card_divisors_sq_le N, whose RHS is N*invSum(N)^3, and the existing harmonic upper bound.
This gives an averaged Mellin profile bound O(N log^5 N+T log^6 N). NOT yet formalized here, and not a pointwise time-domain RH estimate. A careless coefficient-to-time transfer still loses the carrier length.


## Final validation
All SIX final leaf audits passed sequentially in foreground using lake --old env lean FILE -o matching .olean. Combined 45-public-theorem axiom audit exited0; every theorem depends only on [propext, Classical.choice, Quot.sound].
Six fresh objects, exactly one umbrella import each, no forbidden constructs/trailing whitespace. Umbrella git diff --check passed.
Final ForceEnergy fix: simplification of (1/n)*F(n)^2 also needs mul_one alongside one_mul after ordered mul_comm. No mathematical proof changes were needed.
Temporary /Users/michael/Documents/Codex/2026-09-26/new-chat-2/work/EulerPrimeForceAxiomAudit-0lebavgq.lean deleted.
Index refresh succeeded, wrote LEAN_API/GAPS/OVERVIEW and updated7 search files.
Global lint exited1 for20 unrelated unreachable modules and stale LEAN_API.md, LEAN_GAPS.md, LEAN_OVERVIEW.md during concurrent work. No own module errors. Do not claim global lint clean or repeatedly chase other chats' unfinished modules.
Unreachable RHTower modules at final lint: ClusterInterpolationContour, ClusterNodeFrame, CompositeResolventDivision, CuspSeriesBulkTailBounds, HedenmalmCompactSourceEigenmode, MobiusDiscretePacketCriticalHorizon, MobiusDiscretePacketEdgeEstimates, MobiusDiscretePacketGeneralOrder, MobiusDiscretePacketHorizon, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, RiemannKernelCuspSeries, XiGaussianHeatRetentionObstruction, XiWindowQuotient, ZetaZeroDensityPowerSaving.
Unreachable HTGeometry modules: ExponentialLagrangeContour, FixedAdjoinIndependentDescent, PolynomialExtrapolationRemez, PontryaginNeutralEigenvectorBound.
Last scoped git status: six new leaves untracked; umbrella modified. Concurrent edits preserved. No commits/pushes, no full or umbrella builds.
All own build/audit/index/lint/search handles terminal. No own live process.
RH remains UNPROVED. Active goal remains ACTIVE. This turn is progress: actual unconditional coefficient-energy bound and exact prime-force cancellation/support identities added and checked. The time-domain square-root bound remains the central unresolved task.

# Actual Möbius convolution and completed dilation first variation

RH remains UNPROVED. Active goal stays ACTIVE. Previous goal turn made verified progress: 8 new leaves / 35 new public theorems, including the actual signed convolution, complete prime-deficit balance, completed scalar functional, and a rigorous failure of the isolated Mellin symmetry. Continue from `mem:research/noether_divisor_source_reciprocal_reflection_uniform_bound_2026_09_27` and earlier short quadratic / coprime memories.

## Authoritative state / validation
Repo `/Users/michael/Documents/code/hgt/formal`. All 8 modules listed below passed final foreground `lake --old env lean FILE -o .lake/build/lib/lean/...olean`, one own Lean process at a time. No full or umbrella build. All objects fresh, each leaf imported exactly once in `GaloisForLFunctions/RHTower.lean`, whitespace/diff checks clean. No sorry, custom axiom, numerical experiment, #eval/native_decide or heartbeat increase.

Scratch `/Users/michael/Documents/Codex/2026-09-26/new-chat-2/work/ShortDilationAudit.lean` printed axioms for all 35 public theorems (including simp-attributed twist_zero). Audit exited0: EVERY theorem uses only [propext, Classical.choice, Quot.sound]. Scratch deleted. No own live process at end.

Index refreshed; lint raced with other chats, so index refreshed ONCE more. Final lint still fails on 16 unrelated unwired modules and concurrent stale LEAN_API.md. Do not chase infinite metadata races, wire unfinished other-chat modules, or claim whole repository clean. Last unwired examples CCMPrimePoleSchurEnergyBounds/Modulation, MobiusPrimeInsertionDipoleJet, MoebiusMollified* and HTGeometry branches. Own 8 modules all wired. Prior arithmetic-convolution cast fix in LogarithmicMobiusShortReconstruction is preserved. No commits/pushes/subagents.

## Notation
b(t)=logarithmicCenteredSawtooth t=fract(exp t)-1/2.
C(T)=logarithmicReciprocalSawtoothCorrelation T=int_0^T b(T-s)b(s)ds; prior |C|<=5/4.
U(T)=floor exp(T/2).
D(T)=ccmLogChebyshevDeficitPrimitive T.
R(T)=ccmPrimeDeficitDilationRemainder T, prior |R|<=7/2 and exponentially settling limit L.
B(T)=ccmPrimeDeficitShortQuadraticWork T, prior RH iff B=O(exp(T/2)); D-B=2 short_mu_U R and |D-B|<=7exp(T/2).
H(T)=ccmPrimeDeficitDivisorSource T is explicit tau/log divisor source from prior turn.
kappa_T=ccmPrimeDeficitDivisorMainCoefficient T is a TIME-DEPENDENT finite force integral, not a proved fixed constant.
J(T)=ccmPrimeDeficitReciprocalErrorWork T, prior |J|<=3/2.

## New modules
### 1 LogarithmicFiniteEntryProfile.lean (5 public theorems)
Defines logarithmicFiniteEntryProfile w U f t = sum_{1<=n<=U} 1_{log n<=t} w(n) f(t-logn).
- eq_min_prefix: equals sum to min(U,floor exp t), all real t.
- logarithmicShortMobiusInverse_eq_min_prefix.
- short inverse = finite entry profile with actual mu coefficients.
- short inverse = full inverse when floor(exp t)<=U.
- finite entry profile vanishes for t<0.
All cutoffs including negative times are retained; no convergence hypotheses.

### 2 LogarithmicSawtoothEntryCorrelation.lean (4 public theorems)
logarithmicSawtoothEntry p t = 1_{p<=t} b(t-p).
Measurable, abs<=1/2; product entry_p(s) entry_q(T-s) is interval integrable on every bounded interval.
For p,q>=0, p+q<=T:
int_0^T entry_p(s)entry_q(T-s)ds = C(T-p-q).
Private exact closed-window indicator integral uses integral_Icc_eq_integral_Ioc, avoiding endpoint omissions.

### 3 LogarithmicFiniteSawtoothConvolution.lean (4 public theorems)
- entry profile b equals sum w_n entry_log n.
- intervalIntegrable_logarithmicFiniteEntryProfile_pair for arbitrary real signed w,v, fixed U, arbitrary bounded interval and reflection T.
- integral_logarithmicFiniteEntryProfile_pair: for ANY real T, arbitrary w,v, cutoff U(T):
  int_0^T F_w,U(s) F_v,U(T-s)ds = sum_{a,b<=U} w_a v_b C(T-log(ab)).
  For T<0 U=0, so formula remains exact. Positive-index log bounds prove p+q<=T on every actual summand.
- logarithmicShortMobiusInverse_reciprocalCorrelation_square (line103): actual double mu correlation = integral of actual short mu sawtooth profiles.
No independent phase, randomness, positivity or cancellation assumption.

Lean implementation lesson: rewriting sum multiplication with simp can exchange row order. First rw [Finset.sum_mul], then simp_rw [Finset.mul_sum]. For interval integrability of a sum of functions, `.congr; intro s _; simp only [Finset.sum_apply]` avoids failure to eta-expand a bare function-valued sum; passing (s := finset) is required by IntervalIntegrable.sum.

### 4 LogarithmicMobiusSawtoothPrefix.lean (4 public theorems)
Reuses existing Möbius inversion of Z rather than duplicating natural-floor inversion.
- logarithmicMobiusInverse_floor_exp: mu inverse of floor(exp t) is1 for t>=0, since floor(exp t)=Z1.
- full inverse of b exactly
  exp(t) sum_{n<=exp t}mu(n)/n -1 -(1/2)sum_{n<=exp t}mu(n).
- same short inverse when floor(exp t)<=U.
- logarithmicShortMobiusInverse_centeredSawtooth_first_half (line56): for0<=t<=T/2, actual U(T)-truncated profile has that exact full-prefix arithmetic formula.
This exposes actual Mertens/harmonic data; it does not bound them at square-root scale.

### 5 LogarithmicWeightedSawtoothConvolution.lean (1 public theorem)
weighted_reciprocalSawtooth_square_eq_profile_integral, arbitrary signed w and realT:
sum_{a,b<=U} w_a w_b [(T-log(ab)-2)/2 * C(T-log(ab))]
= int_0^T F_{w(n)*(T/2-1-logn),U}(s) F_{w,U}(T-s) ds.
Proof transfers half the product logarithm to one coefficient using symmetry of the FULL square. Private symmetric_weight_average does exact finite averaging. Every sign and logarithmic moment retained.

### 6 CCMPrimeDeficitShortReflection.lean (5 public theorems)
Defines S(t)=ccmPrimeDeficitDivisorReflectionMain t:
(gamma+1) Z(exp-1)(t) - c Z(id)(t) + exp(t) kappa_t - R(t)/2, c=log(2pi)/2.
Defines:
M(T)=ccmPrimeDeficitShortReflectedMainWork T = 2P_U - sum mu_a mu_b S(T-logab).
E(T)=ccmPrimeDeficitShortReciprocalErrorWork T = sum mu_a mu_b J(T-logab).
I(T)=ccmPrimeDeficitShortReciprocalPairing T = integral of centered-logarithmic-coefficient mu profile against ordinary reflected short mu profile.
Proves H(t)=S(t)-(t-2)C(t)/2-J(t), t>=0.
I(T) equals actual weighted mu square above.
**B(T)=M(T)+I(T)+E(T)**, T>=0.
**D(T)=M(T)+I(T)+E(T)+2 short_mu_U R(T)**.
Corresponding |D-(M+I+E)|<=7exp(T/2).
MAIN AND ERROR TERMS MUST STAY COUPLED. Bounding I alone is not sufficient for RH.

### 7 CCMPrimeDeficitShortDilationAction.lean (8 public theorems)
logarithmicDilationTwist T z n=exp(z*(T/2-1-logn)). Exact additive-parameter group law twist(z+u)=twist(z)twist(u), twist0=1.
Q_T(z)=ccmPrimeDeficitShortCorrelationAction T z:
sum_{a,b<=U} mu_a mu_b exp(z*(T-logab-2)) C(T-logab).
Equals exact convolution integral of two finite profiles with weights mu_n*twist(T,z,n).
**HasDerivAt Q_T (2I(T)) 0**, all realT.
Thus actual D balance also contains Q'_T(0)/2 rather than I.

Defines explicit COMPLETED scalar functional
A_T(z)=ccmPrimeDeficitShortCompletedDilationAction T z
=Q_T(z)+2z*(M(T)+E(T)).
Definition uses explicit divisor-source terms and finite mu coefficients; D or B is NOT inserted into the definition.
For T>=0:
**HasDerivAt A_T (2B(T)) 0**.
**D(T)=A'_T(0)/2 + 2 short_mu_U R(T)** (line122).
**|D(T)-A'_T(0)/2|<=7exp(T/2)** (line131).
Hence uniform square-root slope control of A_T is the actual remaining target. This is a precise reformulation/reduction, NOT a new bound on B or A'. The linear completion packages the explicitly derived main/error terms; it is not a demonstrated physical Lagrangian or Noether symmetry. No invariance, coercivity or stationarity is claimed for completed A.

### 8 CCMPrimeDeficitShortDilationSymmetryTest.lean (4 public theorems)
Analytic, no numerical experiments:
For0<=T<=log(4/3), both sawtooths on0..T are <=-1/6, hence **C(T)>=T/36**.
Cutoff U(T)=1, so **Q_T(z)=exp(z*(T-2))C(T)**.
For0<T<=log(4/3), **Q'_T(0)<0** (line72).
Unconditional theorem **ccmPrimeDeficitShortCorrelationAction_not_invariant** (line89): at T=log(4/3), Q_T is not constant in z.
This refutes the isolated Mellin deformation as a Noether symmetry; it does NOT refute RH, all possible symmetries, or establish anything about invariance of completed A. It is a concrete failed symmetry candidate, guiding the next loop toward complete coupled terms.

## Mathematical audit of tempting old coprime shortcut (reasoned from current source, NOT new Lean theorem)
Read current CCMPrimeDeficitCoprimeBalance, CCMPrimeDeficitCoprimeHeadControl and LogarithmicCoprimeEnergy this turn.
- Coprime energy sums the FULL square a,b<=expT, NOT hyperbola ab<=expT. Both a,b>exp(T/2) can occur; head block does not cover all cross interactions by symmetry.
- Let Q=mu R. Row1=ZQ=R. In cross sum excluding diagonal, row1 contributes Q(T)*(R(T)-Q(T)), including **-Q(T)^2**. Therefore summing the polynomial bounds for all other rows does NOT give a square-root bound for Q: endpoint energy cancels exactly with this row1 term. The earlier tempting inference would be a false proof of RH (even constant-source R would expose it). Do not drop row1 or treat complete row bounds as a coercive energy estimate.

## Next work
Goal remains actual RH proof, not more equivalent criteria alone. Try to bound the COMPLETE slope A'_T(0), keeping M,I,E coupled, or derive a genuinely useful symmetry/energy for the complete system. Current exact finite convolution supports a rigorous energy/Gram calculation for the actual mu profiles; first-half profile formula identifies Mertens/harmonic quantities exactly. Avoid replacing actual mu signs by arbitrary-vector PSD assumptions (previous source 2x2 matrix has determinant -1) or independent random phases.

Possible further concrete normalization, not implemented here: earlier CCMPrimeDeficitShortQuadraticWork already proves |D-B-2L M(U)|<=(T+14)/2. Adding the explicit linear boundary term 4z L M(U) to completed A gives a logarithmic-error first-variation representation. At cutoff T=2log n the B jump should be -2mu(n)R(logn); subtracting the limiting jump with 2L M(U) leaves exponentially small defect. This endpoint/jump statement is an UNPROVED next conjecture requiring exact truncation-boundary analysis; source G(0)=R(0)=0 may permit extending the strict short identity to the boundary. Do not present these as established results.

# Dilation-source bounds and actual Möbius localization (2026-09-27)

## Goal and status
Active user goal remains an unconditional Lean proof of RH via arithmetic conservation/Noether and sustained conjecture/proof loops. RH is NOT proved. The full signed Chebyshev deficit square-root bound is NOT established. Do not mark the goal complete or blocked because the mathematical step is open. Preserve signed cross interactions and explicit main terms.

Repo /Users/michael/Documents/code/hgt/formal. Rules: no sorry/new axioms/computational experiments/heartbeat increases; one foreground own Lean process; no umbrella/full builds; final checks `lake --old env lean FILE`; wire new leaves; no commits/pushes/subagents. Search Lean corpus through ../scripts/formal_tools.py research, then rg/read Lean only, not cards. Other chats edit/build the same tree.

Previous context: `mem:research/noether_chronological_work_and_dilation_conservation_2026_09_27`, `mem:research/noether_chronological_work_validation_2026_09_27`.

## Seven new leaves, 29 public theorems
1 LogarithmicEntryIntegration (3)
2 CCMPrimeDeficitDilationSourceBounds (5)
3 CCMPrimeDeficitDilationOscillation (1)
4 CCMPrimeDeficitDilationUniformBound (8)
5 CCMPrimeDeficitMobiusCenteredEnergy (4)
6 CCMPrimeDeficitDilationLimit (4)
7 CCMPrimeDeficitMobiusTailLocalization (4)
All under GaloisForLFunctions/RHTower, namespace RHTower. All 7 individually passed `lake --old env lean FILE -o .lake/build/lib/lean/...olean`; all wired once into RHTower.lean; all source/object timestamps current. Final AuditDilationBound imported all 7 and printed axioms for all 29, exit 0: ONLY propext, Classical.choice, Quot.sound. No sorryAx/custom axioms. No forbidden source constructs found. Global metadata/index refreshed. Final global lint pending when this memory first written; see follow-up validation memory.

## Definitions and proved formulas
D(T)=ccmLogChebyshevDeficitPrimitive T=integral_0^T (exp t-psi(exp t))dt.
Previous conservation: sum_{1<=n<=exp T} D(T-log n)=G(T), all real T.
G=ccmPrimeDeficitDilationSource=expT*H_N-N-sum logk*(T-logk), N=floor(expT).
Previous exact inverse (T>=0): D(T)=sum mu(n) G(T-logn).

Generic logarithmicEntrySum w t=sum_{1<=n<=exp t}w(n). LogarithmicEntryIntegration proves common-prefix indicator identity, weighted local integrability, and exact finite signed sum/integral interchange:
integral_0^T g(t)entrySum(w,t)=sum_{n<=expT}w(n)*integral_logn^T g(t), continuous g,T>=0.

Define c=log(2*pi)/2, gamma=Euler constant.
F(T)=ccmPrimeDeficitDilationForce=expT*H_N-sum_{n<=N}log n.
R(T)=ccmPrimeDeficitDilationRemainder=G(T)-(gamma+1)(expT-1)+c*T.
F integrates to G. Centered F bound <=T/2+2, hence coarse |R|<=T^2/4+2T. More precise:
Osc(T)=(fract(expT)-1/2)*(T-1).
Err(T)=F(T)-(gamma+1)expT+c-Osc(T).
PROVED |Err(T)|<=3exp(-T), T>=0.
Uses HarmonicStirlingExactBounds:
1/(2N)-1/(12N^2)<=H_N-logN-gamma<=1/(2N).
0<=sum logn-(NlogN-N+logN/2+c)<=1/(12N).
Exact Err=(delta-1/2)(logN-T)+delta/(2N)+expT*a-b.

B(x)=bernoulliPeriodic x=(fract(x)^2-fract(x))/2, |B|<=1/8.
P(T)=ccmPrimeDeficitDilationSawtoothPrimitive=exp(-T)(T-1)B(expT).
C(T)=ccmPrimeDeficitDilationSawtoothCorrection=exp(-T)(2-T)B(expT).
Right derivative P'=Osc+C for ALL real T; uses DeletionMixedRefinement.bernoulliPeriodic_hasDerivWithinAt_right, no missed integer joins.
R(T)=P(T)+integral_0^T [Err(t)-C(t)]dt.
|P(T)|<=exp(-T)(T+1)/8<=1/8.
|Err-C|<=exp(-T)(T+26)/8.
Main uniform theorem: abs_ccmPrimeDeficitDilationRemainder_le_uniform: |R(T)|<=7/2.
Corresponding signed aggregate theorem replaces G by entire sum D(T-logn). This bounds a transformed aggregate, NOT pointwise D.
Public reusable helpers: intervalIntegrable_ccmPrimeDeficitDilationErrorCorrection, abs_ccmPrimeDeficitDilationSawtoothPrimitive_le_decay, abs_ccmPrimeDeficitDilationErrorCorrection_le.

## Settling constant, proved
L=ccmPrimeDeficitDilationLimit := integral_{t>0}[Err(t)-C(t)]dt.
Absolute integrability proved, no assumed convergence.
R(T)-L=P(T)-integral_{t>T}[Err(t)-C(t)]dt.
abs_ccmPrimeDeficitDilationRemainder_sub_limit_le:
|R(T)-L|<=exp(-T)(T+14)/4, T>=0.
tendsto_ccmPrimeDeficitDilationRemainder: R -> L at infinity.
Proof envelope antiderivative -exp(-t)(t+27)/8, with integral tail exp(-T)(T+27)/8. Uses IntegralEqImproper APIs, pow_mul_exp_neg limit. L not identified with zeta constants.

## Actual signed inverse and diagonal
moebiusCoeff n already in corpus, real mu, |mu|<=1.
Explicit(T)=ccmPrimeDeficitMobiusExplicitWork
 =(gamma+1)[expT*sum mu(n)/n-sum mu(n)]-c*sum mu(n)(T-logn).
Centered(T)=sum mu(n) R(T-logn).
D=Explicit+Centered exactly.
Diagonal(T)=exp(-T)*sum [mu(n)R(T-logn)]^2.
SignedCross(T)=exp(-T)[Explicit^2+2Explicit*Centered+Centered^2-sum[muR]^2].
Proved 0<=Diagonal<=49/4 for ALL real T.
Full critical energy E=exp(-T)D^2=Diagonal+SignedCross exactly.
No upper bound on SignedCross. Do not treat diagonal alone as the full result.

## Actual square-root divisor localization, proved
Transient(T)=R(T)-L (written inline, no new definition).
For T>=0 and natural m<=floor expT:
|sum_{1<=n<=m} mu(n)Transient(T-logn)| <= exp(-T)*m^2*(T+14)/4.
Theorem abs_ccmPrimeDeficitMobiusTransient_prefix_le.
Define Head(T)=ccmPrimeDeficitMobiusTransientHead, same sum with m=floor exp(T/2).
Define Tail(T)=ccmPrimeDeficitMobiusTransientTail, same sum over floor exp(T/2)<n<=floor expT.
|Head(T)| <= (T+14)/4. All actual signs retained; proof even works by absolute values after subtracting L.
Exact reconstruction:
D(T)=Explicit(T)+L*sum_{n<=expT}mu(n)+Head(T)+Tail(T).
Thus |D(T)-[Explicit(T)+L*M(floor expT)+Tail(T)]| <= (T+14)/4.
This is unconditional control of a complete signed portion at O(log x), x=expT. The combined explicit, constant-Mertens, and large-divisor terms remain UNCONTROLLED at square-root scale. Individual terms may cancel each other; do not bound/discard them separately without proof.

## What to pursue next
Continue actual signed combined remaining work, not another conditional RH criterion. Uniform source and exponentially small transient alone do not control full Möbius inversion. Possible exact arithmetic lcm/divisor-incidence energy route; existing EulerDeletionTruncatedDivisorPairCorrelation already proves lcmMoebiusPairCoefficient_eq_moebius (full lcm fibre) and finite_lcm cross inversion. Complete lcm cancellation fails if weights vary/cutoff misses complement fibres; retain boundary. Earlier MobiusHalfSelectionGrowthObstruction rules out some diagonal-only bounds. Generic bounded kernels cannot imply sqrt cancellation.
Prime-renewal and Mertens self-convolution source criteria already exist (research query 'mobius half source'); do not duplicate criteria as achievements.
One analytic observation not yet formalized: G Laplace transform resembles zeta/(s(s-1))+zeta'/s^2. Full D logarithmic derivative has simple poles even if individual explicit/centered inverse pieces have higher order poles, so their cancellation matters.

## Build race and cleanup
Other chat's lake setup-file rebuilt and temporarily deleted import objects. Our new leaf failed on missing DecayIsDirectional, then ZeroShiftColumnCarriesEverything; both regenerated. Transitive audit found only WeightSitsAtTheMittagLefflerThreshold missing. Created TEMP hard-link fallback of 4640 existing transitive project oleans in /Users/michael/Documents/Codex/2026-09-26/new-chat-2/work/dilation-import-cache. Built ONLY missing WeightSitsAtTheMittagLefflerThreshold leaf, passed, added its olean to fallback. Then all new leaf checks passed with LEAN_PATH pointing at this fallback. Normal paths precede fallback. No unrelated source modifications.
Temporary AuditDilationBound.lean and this entire fallback MUST be removed after all own Lean processes end. At memory creation all own Lean processes have ended; only global lint process 21090 remains. Cleanup scheduled next. Preserve other chats' files/processes.

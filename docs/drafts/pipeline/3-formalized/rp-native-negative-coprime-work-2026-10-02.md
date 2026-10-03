# RP-51: forced negative work of the native coprime history

Status: obstruction and positive survivor formalized and audited; no
positive-damping payment estimate.
Route: RP, native signed coprime payment and both history debts.

Previous turn made verified boundary progress, not a positive-damping
bound. The actual profile h(t)=exp(-t)*H_full(exp t) has locally integrable
square and unbounded partial square energies. Corpus sources are
RoutePNativeCriticalSquareEnergy, RoutePCoprimeSquareNative, and
RoutePCoprimeSquareMellin. Revalidated their current source this turn.

Proved: C(t)=exp(-t)*logarithmicCoprimeCross(nativeProfile,t) has a
nonintegrable negative part on t>0, and is negative arbitrarily late.
Positive survivor: its negative partial integrals exceed every finite
budget at arbitrarily late cutoffs. This concerns zero damping only.

Dependency-closed paper argument:

1. The exact native identity gives B(t)=h(t)^2+C(t), where
   B(t)=exp(-t)*Re A(exp(-t)) and A is the actual Mobius unit-square source.
2. For every epsilon>0, exp(-epsilon*t)*B(t) is integrable. Its integral
   is the real Mellin value at 1+epsilon and tends to zero as epsilon->0.
   Establish the exponential change of variables with the Jacobian;
   do not assume admission of either summand in step 1.
3. If N(t)=max(-C(t),0) is integrable, then
   0<=exp(-epsilon*t)*h(t)^2<=exp(-epsilon*t)*B(t)+N(t).
   This first admits the damped square and then bounds its full integral
   by I_epsilon+integral N. Restrict to a finite interval and let epsilon
   decrease to zero using compact dominated convergence. Every undamped
   partial square integral is at most integral N, contradicting RP-50.
4. Local admission of N follows from the admitted balance at epsilon=1,
   the bounded inverse weight on a compact interval, and local square
   admission. Nonintegrability then gives cofinal negative-mass escape.
   Eventual C>=0 would put all negative mass in a compact interval,
   contradicting the same result.

Hard frontier still open: bounds uniform in physical cutoff at each
positive damping, signed high-LCM control, and the two history debts.
No damping-independent finite budget can serve as the payment input.

## Source search and novelty audit

All three documented deep corpus searches completed without errors or
unfinished stages, partial=false. Results were source-only, semantic
coverage unmeasured, and background refresh incomplete. Compiler audits
below establish the new leaf independently of retrieval metadata.

- Negative-part query: query generation1190199, coverage/current1190203,
  64,600 files, zero pending. Native Mellin identity was applicable. The
  generated recipe conflated unrelated positive energies with the native
  negative part and was rejected.
- Positive-damping cancellation query: query1190319,
  coverage1190345/current1190346, 64,608 files, zero pending; older-coverage
  warning. Native Mellin identity was the relevant source. Generic gcd
  facts and damping bounds did not supply a native cross-work lower bound.
- Source-conditioned coercivity query: query/coverage/current1190363,
  64,609 files, zero pending. Retrieved exact short reconstruction and
  the literal short quadratic form. The proposed residue-class prime
  lower bound concerns a different signed quantity and was rejected.

Read logarithmicCoprimeEnergy, its Mobius-square diagonalization, the
native source identity, logarithmicMobiusInverse_eq_half_correction,
and ccmPrimeDeficitShortQuadraticWork_eq_square. The new result strengthens
the existing one-time negative coprime witness to cofinal negativity and
cofinally unbounded complete negative mass. It uses the RP-50 native
square obstruction, not an assumed RH statement or square admission.

Positive-damping trial: apply the exact short inverse twice and retain
all rectangular product indices. This gives a signed bilinear form, not
a coercive estimate. The actual source correction is already bounded at
the critical scale; the remaining form is explicitly RH-equivalent in
riemannHypothesis_iff_shortQuadraticWork_bound. Absolute control or a
generic inverse norm would discard the needed cancellation. This trial
did not solve the hard payment problem and adds no new theorem. It is
not a counterexample to the native positive-damping conjecture.

## Lean audit

New leaf: RoutePNativeNegativeCoprimeWork.lean.
Public unconditional results:

- not_integrableOn_routePNativeNegativeCoprimeWork
- routePNativeNegativeCoprimeWork_cofinally_unbounded
- routePNativeCoprimeCross_negative_beyond

Foreground leaf audit51819 exit0 with explicit olean, using
`lake --old env lean <leaf> -o <olean>`. Initial audit53688 exposed only
membership elaboration, the eventual-versus-pointwise limit lemma, and
pointwise function subtraction reduction; all repaired without resource
overrides. Scratch/API/axiom audit18596 exit0. Every public result uses
only propext, Classical.choice, Quot.sound. No added axiom, sorry, admit,
unproved premise, numerical experiment, subagent, commit, or push.
Leaf wired into RHTower.lean; no umbrella/full build.

Lint63094 exit1: ten unrelated unreachable modules:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
No new-leaf lint error; global gate is not green.

## Frontier assessment

This closes the zero-damping finite-negative-budget proposal with its
strong positive survivor. It does not close positive-damping admission
or the RH-equivalent signed history floor. Continue with cancellation
between complete native coprime pairs at fixed positive damping, retaining
physical cutoff dependence. Do not infer separate integrability from
the admitted combined Mellin expression. Goal remains active.


# Route TG C9.24A closed; actual signed adaptive remainder next

Goal ACTIVE. No RH proof/falsification. No subagents, full/umbrella builds, computations, axioms/holes or heartbeat overrides.

## New audited mathematics
Leaf formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitCompletePole.lean (404 lines), 5 public theorems + 2 definitions.
F=actual dilation source, H=actual divisor source, c=1+gamma.
g(t)=actual right force F_force(t)-c exp(t); j(t)=fract(exp(t)).
d=integral positive halfline exp(-t)g(t) - c integral positive halfline exp(-t)j(t).
R(t)=H(t)-exp(t)(ct+d).
Both defining integrals proved integrable; no arithmetic cancellation estimate.
Unconditional exists C>0 forall real t: |R(t)|<=C(max(t,0)+1)^2.

Exact full finite pair form, all real signs/shifts:
sum vi vj H(T-ui-uj)
=exp(T)(((cT+d)*m0^2)-2c*m0*m1)+sum vi vj R(T-ui-uj),
m0=sum vi exp(-ui), m1=sum vi ui exp(-ui).
For T>=0, ui>=0, same uniform C bounds full R form by C(T+1)^2(sum|vi|)^2.
m0=0 therefore cancels WHOLE exponential pole, also for adaptive labels crossing half-horizon.
Negative shifted-time terms retained: H(t)=0 for t<=0, R(t)=-exp(t)(ct+d), bounded <=|c|+|d|.
This is stronger than C9.23 leading fixed-packet limit. It does NOT pay actual native energy: coefficient-mass-square can cost exp(T).

Public names/lines:
135 ccmPrimeDeficitDivisorPoleConstant
141 ccmPrimeDeficitDivisorPoleRemainder
271 ccmPrimeDeficitDivisorPoleRemainder_polynomial_bound
311 ccmPrimeDeficitDivisorPoleRemainder_global_bound
328 ccmPrimeDeficitDivisorSource_finite_pair_eq_complete_pole
361 ccmPrimeDeficitDivisorSource_finite_pair_remainder_bound
390 ccmPrimeDeficitDivisorSource_harmonic_neutral_bound

## Audits
Final foreground lake --old env lean GaloisForLFunctions/RHTower/CCMPrimeDeficitCompletePole.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CCMPrimeDeficitCompletePole.olean: exit0 empty diagnostics.
Separate /tmp/tg-c924-complete-pole-axioms.lean: all5 standard propext/Classical.choice/Quot.sound only, exit0.
Umbrella import after CCMPrimeDeficitEulerSignedPole. No umbrella build.
Index exit0; all7 API rows verified.
Lint exit1: 13 unrelated unreachable modules, no owned finding:
CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MertensProductDiamondPintz, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, PMPowerDampedMobiusPrimeCurrent, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving, HTGeometry.CompactMonoidMeasureAlgebra.
Logs /tmp/tg-c924-complete-pole-{final,axioms,index,lint}.log.
No theorem source change after final audit.

## Docs
P3 docs/drafts/pipeline/3-formalized/tg-complete-divisor-pole-cancellation.md full dependency-closed paper proof+audit.
P1 same basename remains live with PartB actual-source attack.
Main log docs/drafts/pipeline/1-in-progress/tg-principal-polar-operator-cancellation.md C9.24 entries.
Frontier TG row after fixed-Euler pole law.
Prior mem:rh/tg-fixed-euler-signed-renewal-pole-2026-10-04 and mem:rh/tg-gamma-clock-nuclear-admission-frontier-2026-10-04.

## Next hard conjecture B (paper proposal, NOT formalized)
N=floor(exp(T/2)); hN=sum_(1..N) mu(n)/n.
Preserve actual head a(n)=mu(n) for n<=N.
Choose a(N+1)=-(N+1)*hN; a(n)=0 n>N+1.
Then full harmonic moment sum a(n)/n=0, and old head-extension symmetry gives unchanged literal action D(T).
Use F0(t)=F(t)-c exp(t) and new global source R to prove exact
D(T)=2 sum_(1..N+1) a(n)F0(T-log n)
      -sum_(m,n in1..N+1) a(m)a(n)R(T-log m-log n).
The linear term should have critical-scale polynomial budget: F0=O(t+1) positive time from uniform dilation remainder; F=0 at negative time; sum|a|<=N+(N+1)(1+logN). Actual SIGNED quadratic R bound remains hard, no proof. Do NOT call absolute-mass-square bound a critical estimate or build another RH equivalence wrapper.
Native ground energy summability, full joint Hardy cubic, strict contraction remain hard gaps.

## Corpus sources read this turn
CCMPrimeDeficitDilationUniformBound: full centered remainder <=7/2.
CCMPrimeDeficitMobiusCenteredEnergy: full D=explicit+centered; normalized centered diagonal <=49/4; signed cross remains.
CCMPrimeDeficitShortSourceMatrix: actual generic source matrix at short2 indefinite (already closed, don't repeat).
CCMPrimeDeficitDivisorQuadrature, DivisorReflection, DivisorSource, DilationLimit read fully; centered floor quadrature known but entire constant residue subtraction was absent.
CCMPrimeDeficitCoprimeRows/Balance read fully: complete nontrivial rows cancel limiting constant, but actual compensating coprime work lower bound open.
LogarithmicReconstructionAction and TailSymmetry read fully.
CCMPrimeDeficitCoefficientAction read fully:
ccmPrimeDeficitCoefficientAction_headExtension v hT gives unchanged D for logMobiusHeadExtension floorhalf v.
LogarithmicFiniteEntryProfile fully read: finite causal indicator profile equals moving min cutoff; shortMobiusInverse eq profile; not yet arbitrary finite-support coefficient adapter.
LogarithmicMobiusShortReconstruction lines118-181 read: short prefix/square identities.
CCMPrimeDeficitDivisorSourceEntry fully read: H=0 nonpositive; H=exp(t)-1 before log2.
DilationSourceBounds lines19-118 read: right force primitive and centered force bound.

## Search evidence
/tmp/tg-c924-moving-neutral-search.json partial reranking workerdisconnect; full source inventory and incomplete background compiler refresh. Mostly irrelevant candidates; rejected.
/tmp/tg-c924-hyperbola-search.json nonpartial full source inventory, incomplete compilerrefresh. Proposed harmonicmean/theta ingredients irrelevant; no estimate.
/tmp/tg-c924-neutral-completion-search.json lexical module Logarithmic any words, returns headExtension/symmetry and harmonic APIs; no native neutral bound, no freshness fields.
Candidates/sourcearguments/ingredientsets inspected. Final theorem applicability checked in Lean.

## Formalization lessons
Use dsimp only before rewriting an integral hidden behind lambda in finite sum.
For private poleFloor, rw integral_add requires explicitly typed interval-integrability proof using that exact symbol; raw Int.fract integrability won't syntactically rewrite.
exp products times extra factors: use linear_combination factor*he, not nlinarith only[he].
congr 1 closed exp(T-s)=expT exp(-s); extra ring was unused.
Final optimized imports: DivisorQuadrature, Mathlib.MeasureTheory.Integral.IntegralEqImproper, DivisorSourceEntry (removed heavy unused DilationLimit).

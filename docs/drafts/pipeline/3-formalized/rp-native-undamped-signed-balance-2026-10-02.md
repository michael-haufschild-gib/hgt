# RP-52: complete native signed balance at zero damping

Status: all six public results formalized; final leaf, API, and axiom checks passed.
Route RP. RH, positive-damping signed payment, high-LCM control, and both
history debts remain open. RP-51 proved negative-part escape but did not
control the full signed cross-work integral.

Hard target remains source-derived signed payment. Initial complete-fibre
integration trial retained the common-scale mu(g)^2 and primitive signs;
there was no new cancellation estimate. Neither the existing coprime
identity nor the short quadratic reconstruction supplies coercivity.

New corpus-grounded theorem: the combined native balance
B(t)=exp(-t)*Re A(exp(-t)) is absolutely integrable at zero damping and
has integral zero. Here A is routePCoprimeSquareSource, with every actual
Mobius coefficient and physical cutoff retained. Consequently the full
signed critical coprime work has partial integrals tending to minus
infinity, with its sum with the positive square energy tending to zero.
This is stronger than nonintegrability of its negative part.

Dependency-closed paper mechanism:

1. U=divisorContinuousUnitHead is globally Lipschitz on [1,infinity).
   Its literal integral integrand is D(floor x)/(2 sqrt x); the corpus
   bound |D(n)|<=24 sqrt n bounds this by12. U vanishes below1.
2. W(y)=y*U(1/y)^2 is bounded, supported on(0,1), and each dilation
   difference W(ny)-W((n+1)y) has L1 mass O(1/n^2). Prove this from
   step1 and U(x)<=3/5 sqrt x. On y<1/n, split the product difference;
   the majorant is O(1/n)+O(1/(n^(3/2)*sqrt y)), whose integral is
   O(1/n^2). Outside that support both terms vanish. No global BV
   assumption for W is used; it need not have finite unweighted variation.
3. Exact finite Abel summation gives A(y)=sum_n M(n)*(W(ny)-W((n+1)y)).
   For each y>0 this is finite. The corpus theorem
   deningerMertensM_invSq_summable makes the norm integrals summable.
   Thus A is L1 without termwise absolute Mobius summation.
4. Integrating each admitted Abel atom gives
   M(n)/(n*(n+1))*integral W. The corpus harmonic-Mobius identity makes
   their sum zero. Valid norm-summable integral interchange gives
   integral A=0. Exponential change of variables admits B and preserves
   this zero mass. The alternative damped dominated-convergence proof
   is unnecessary.
5. The literal identity B=h^2+C now holds with B in L1 and both h^2,C
   locally integrable. Hence integral_0^T C + integral_0^T h^2 tends to0.
   RP-50 square energy escape and monotonicity force integral_0^T C
   to tend to minus infinity. Also max(C,0)<=|B|, so all positive native
   coprime work is integrable even at zero damping. All steps concern
   complete native sources. This isolates negative work as the remaining
   fixed-positive-damping admission/payment obligation.

Source anchors read: RoutePNativeNegativeCoprimeWork,
RoutePCoprimeSquareMellin, LogarithmicCoprimeEnergy,
DivisorContinuousUnitMoment, DivisorContinuousHeadRegularity,
DeningerMertensInvSquare. MobiusThetaNativeCriticalEuler exhibits the
same signed Abel-admission mechanism on another carrier; its Schwartz
assumptions cannot be substituted for the actual divisor source.

This settles a new signed native boundary law, not the remaining
positive-damping lower budget. Do not claim RH from compensated zero mass.

Formalization detail: step1 already exists as
abs_divisorContinuousUnitHead_sub_le in MobiusDivisorUniformLocalRegularity.
For r>=1,y>0, positivity and U<=sqrt give
|W(y)-W(r*y)| <= (r-1)*(1+24/sqrt(y)). Both terms vanish for y>=1.
Integrating gives49*(r-1). Rescale y by n and set r=(n+1)/n to obtain
49/n^2 for each adjacent dilation difference. This closes the analytic
admission mechanism without a new differentiability or BV framework.

RoutePNativeUndampedBalance contains the full argument. Final foreground
leaf audit2035 exited0 using `lake --old env lean <leaf> -o <olean>`.
The leaf is wired into RHTower.lean without building the umbrella.
Final scratch37380 exited0 and printed only propext, Classical.choice,
Quot.sound for all six public results. Earlier scratch63765 found two
wrong namespaces in unused API checks; both were corrected.
Earlier audits45157,16505,5324,78047 exposed only local elaboration or
syntax errors, repaired without new resource options. No added axiom,
sorry, admit, numerical experiment, subagent, commit, or push.

Public results:

- integrableOn_routePCoprimeSquareSource
- integral_routePCoprimeSquareSource_eq_zero
- routePNativeCriticalBalance_integrable_zero
- integrableOn_routePNativePositiveCoprimeWork
- routePNativeSignedCoprimeWork_compensated_limit
- routePNativeSignedCoprimeWork_tendsto_atBot

Lint49480 exited1 with ten unrelated unreachable modules:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
No new-leaf lint error. Global gate is not green.

Search audit: signed-payment query57351 completed partial=false, no
errors/unfinished stages, query1190444, coverage1190457/current1190462,
64,612 files, zero pending. Boundary-admission query87451 completed
partial=false, no errors/unfinished stages, query1190444,
coverage/current1190478, 64,613 files, zero pending. Both semantic
coverage unmeasured and background refresh incomplete; source-only
statements. Candidate lemmas, source arguments, proof ideas (empty) and
ingredient sets inspected. Generic coprime inversion and proposed
Mobius-decay recipes did not prove a payment estimate; not used.

## Why the successful admission does not yet pay the square

Let v(x)=U(x)/sqrt(x), zero below1. The full head is
sqrt(x)*sum_{d<=x} mu(d)*v(x/d). At fixed damping epsilon the finite
pair kernel is integral v(x/d)*v(x/e)*x^(-2-epsilon) dx, with every
physical activation retained. Its full-ray homogeneous degree is
-1-epsilon under simultaneous dilation of d,e. A double Abel bound
using only pointwise Mertens saving and absolute mixed kernel variation
therefore has a growing dyadic envelope at epsilon<1; logarithmic
savings do not remove that power. This is insufficiency of that absolute
majorant, not divergence of the actual signed pair sum. The successful
single-Abel argument for the combined source cannot be promoted to a
native square estimate. The next producer must retain cancellation
between the two actual coefficient variables (or equivalent native
negative-work cancellation), beyond separate Mertens envelopes.

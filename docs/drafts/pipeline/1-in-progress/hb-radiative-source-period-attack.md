# HB: direct source-period attack on radiative extinction

Status: analytical source reduction; physical extinction and RH unproved. Frontier map remains read-only.

Verified findings and scoped no-gos from this work: [concise research log](hb-extinction-own-research-log.md).

## Actual cap derivative attack, 12 September 2026

**CN and scalar time/normal horizon traces verified in Lean; isolated cached exact-leaf audit passed (216 seconds, 2 jobs).** The complete correction
exchange (WBCQ) still requires differentiated physical boundary limits.
For the original cap arm write `c(x)=exp(x)/cosh(x)=1+tanh(x)` and
`M(x,h)=mean_Q(arcosh(1+c(x)*(exp(h)-1)))`. The original field is
`A(v,x)=integral_0^infinity g'(v+h)*M(x,h) dh`, with the full literal `Q`
and unchanged onset `g(u)=chi(u)*exp(2s*u)`.

The new `ThetaCuspHawkingBMCapRadialMemory` leaf passed scratch Lean and
its isolated cached final audit (88 seconds, 2 jobs); it is wired into
`RHTower.lean`. Generated indices were refreshed. Global formal lint still
reports the unrelated unwired `Sieve.KloostermanGlobalCollisionCoprime`
module; no global lint pass is claimed.

The two derivatives of its circle argument satisfy
`partial_x M=(2-c(x))*(1-exp(-h))*partial_h M` away from the removable
characteristic. Integration by parts therefore predicts the exact law

```
partial_x A = -(2-c(x))*integral_0^infinity
  [g''(v+h)*(1-exp(-h))+g'(v+h)*exp(-h)]*M(x,h) dh.   (CN)
```

This must be justified without assuming a global bound for the derivative
of the circle mean. Set `u=c(x)*(exp(h)-1)` first. The same arm becomes

```
integral_0^infinity
  g'(v+log(1+u/c(x)))/(u+c(x))*mean_Q(arcosh(1+u)) du. (CI)
```

The circle field in (CI) is independent of `x`. The existing source bound
and strict gap `sourceGrowthExponent < decayExponent` admit both the density
and its differentiated onset weight, locally uniformly in `x`. Differentiating
that weight and substituting back gives (CN), so no differentiated-theta
majorant is required. The lower integration-by-parts factor is zero; the
upper factor decays by the same strict gap.

At the ingoing horizon `M(x,h)->Q`, while the bracket in (CN) integrates to
`[g'(v+h)*(1-exp(-h))]_0^infinity=0`. Thus `partial_x A->0` is the target
normal trace. Similarly `partial_v A=integral g''(v+h)*M(x,h) dh` tends to
`-g'(v)*Q`. These scalar arm claims and the full two-arm cap's actual time
contact are now Lean-verified in `ThetaCuspHawkingBMCapNormalTrace`.
The formal change uses the equivalent bijective delay map
`flow(b,h)=log((b+exp(h)-1)/b)`, with `b=c(x)/c(x0)` and Jacobian
`exp(h)/(b+exp(h)-1)`, fixing `M(x0,h)`. Formula (CI) remains a paper
version of the same change, not a separately formalized declaration.
They concern the actual source cap; angular-current passage, the reduced
future response, independent SS/SV/VV corrections and full extinction remain
separate terms in the original boundary balance.

**Direct-arm normalized normal limit and first radial jet checked in Lean; isolated cached exact-leaf audit passed (88 seconds, 2 jobs).** The first field expansion in (CJ), full two-arm passage (CFJ) and late memory evaluation remain paper-only. Let
`K(z)=mean_Q(arcosh(z))`, `z>=1`. The current corpus proves continuity of
its actual right derivative through `z=1`, with
`K'(1)=Delta_H Q/2` (`angularKernel_closed_derivative` and
`characteristicFirst_at_one`). It also proves
`|mean_Q(r)|<=C exp(a0*(r+|k|))`, with `1<=a0<d<2`.
At fixed `X,k`, these facts give the global estimate

```
|K(1+u)-K(1)| <= C_(X,k)*(u+u^a0),   u>=0.          (CR)
```

For `0<=u<=1`, integrate the bounded continuous derivative on `[1,2]`.
For `u>=1`, use `arcosh(1+u)<=log(4u)`, the global growth bound and the
constant `K(1)`, absorbed into `C*u^a0`. Thus, for `0<c<=1`,
`|K(1+c*(exp(h)-1))-Q|/c <= C*(exp(h)+exp(a0*h))`.
The original `g`, `g'`, `g''` decay with exponent `d>a0>=1`, so this is
an integrable difference-quotient majorant for both arm weights.
Dominated convergence and the actual derivative at one give

```
A(v,x) = -g(v)*Q-c(x)*(Delta_H Q/2)*I_g(v)+o(c(x)),
normalArm(v,x)/c(x) -> (Delta_H Q/2)*I_g(v),
I_g(v) = integral_0^infinity g(v+h)*exp(h) dh.        (CJ)
```

The two required weighted moments are derived by integration by parts:
`integral g'(v+h)*(exp(h)-1)=-I_g(v)`, and
`integral normalWeight(v,h)*(exp(h)-1)=I_g(v)`.
Every lower boundary factor is zero; every upper product decays since
`d>1`. The second identity uses
`normalWeight=partial_h[g'(v+h)*(1-exp(-h))]`, followed by the first.

For the actual exterior radius `r=-coth(x)`,
`r=1/(1-c(x))` and `r^2-1=r^2*c(x)*(2-c(x))`. Therefore (CN) and (CJ)
give the original direct arm's finite radial derivative at fixed `v`:

```
partial_r A -> -(Delta_H Q/2)*I_g(v).               (CRJ)
```

The image arm and its time/normal partial derivatives have size
`O(exp(2*d*x))=O(c(x)^d)` at fixed `v`. The exact same delay substitution
admits joint differentiation in `v,x`: the additional time term is
`g''` times the Jacobian and obeys the same local majorant. The chain rule
therefore retains both image derivatives in the full normal derivative;
after division by `r^2-1`, all image terms tend to zero because `d>1`.
For `C_cap(v-x,x)=-l*(A(v,x)-A(v-2*x,-x))`, this yields

```
partial_r C_cap |_(fixed v) -> l*(Delta_H Q/2)*I_g(v). (CFJ)
```

This scalar radial trace is an explicit source-derived boundary memory,
not a zero assertion. On the original late region `v>=1`,
`I_g(v)=-g(v)/(2*s+1)` by the unchanged physical exponential and
`Re(2*s+1)<0`; this is an integral evaluation, not a new frequency.
No nonvanishing of `Delta_H Q` or of the complete boundary pairing is
claimed. Angular differentiation of the admitted cap limits, the
reduced response's differentiated limits, cusp admission and complete
SS/SV/VV cancellation remain unproved here.

**Original-time transport of the boundary memory checked in Lean; isolated cached exact-leaf audit passed (88 seconds, 2 jobs).**
Differentiating the admitted `I_g(v)` integral gives `integral g'(v+h)*exp(h) dh`.
Its source majorant is `C exp((1-d)*h)`, locally uniform in `v`, with `d>1`.
Integration of `partial_h[g(v+h)*exp(h)]` retains the lower contact `g(v)`
and a zero upper endpoint. Consequently

```
I_g'(v)+I_g(v)=-g(v),
exp(T)*I_g(v+T)-I_g(v)=-integral_0^T exp(h)*g(v+h) dh. (CTM)
```

The second identity follows by integrating the actual derivative of
`exp(h)*I_g(v+h)` on the oriented interval `[0,T]`; it holds for every real
`T`, including the user-predeclared positive physical-clock step. The onset
inside the finite source-work integral is unchanged. The factor `exp(T)` is
fixed by the radial transport equation, not a frequency correction.
For the direct arm radial trace `R(v)=-(Delta_H Q/2)*I_g(v)`, (CTM) gives
`exp(T)*R(v+T)-R(v)=(Delta_H Q/2)*integral_0^T exp(h)*g(v+h) dh`.
This supplies an exact source term to retain in the translated boundary
balance. It asserts neither invariance of this datum nor vanishing of its
actual angular/left-QNM contraction, and it does not replace the complete
nonlinear balance (WBCQ).

**Angular transposition of the actual radial current, paper interface.**
The corpus search suggested moving angular derivatives onto the fixed test
before the infinite-delay limit. The exact original coordinate convention is
`coexact(u)=(u_y,-u_X)` and `A=roughLaplacian-1`, hence
`A(coexact(u))=coexact((Delta_H-2)u)`. In the already volume-weighted radial
current, let `P=coexact(u)`, let `V` be the independent test stream, and set
`D=(r^2-1)*partial_r+partial_v`. At a finite exterior radius,

```
r^2*(J+B)_r = coexact(Du) dot (A V) - (D V) dot coexact((Delta_H-2)u).
```

For a smooth angular cutoff `eta` and a bounded piecewise smooth positive-height
region `Omega`, define `R(W)=partial_X W_y-partial_y W_X`,
`Lstar(psi)=partial_XX(y^2*psi)+partial_yy(y^2*psi)-2*psi`, and
`b(f,W)=f*(W_X*n_y-W_y*n_X)` on the outward Euclidean unit normal. Two
coordinate integrations by parts give the exact boundary-retaining identity

```
r^2*integral_Omega eta*(J+B)_r dXdy
 = integral_Omega [Du*R(eta*A V)-u*Lstar(R(eta*D V))] dXdy
 + integral_boundaryOmega [b(Du,eta*A V)-b((Delta_H-2)u,eta*D V)
     -y^2*R(eta*D V)*partial_n u
     +u*partial_n(y^2*R(eta*D V))] ds.              (WT)
```

Indeed `coexact(f) dot W=f*R(W)+div(-f*W_y,f*W_X)`.
Then apply the scalar Green formula to
`integral (Delta_H u)*R(eta*D V)` with `Delta_H=y^2*(partial_XX+partial_yy)`.
This derives all signs and the changing height weights in (WT).
If `eta` is supported inside `Omega`, the displayed edge integral vanishes
and every derivative of `eta` remains in the two test factors. Thus the
compactly tested expression requires limits of `u` and `Du`; it does not
require separate strong limits of three angular derivatives of `u`.

For a finite-delay truncation of the original cap, angular smoothness follows
from the native circle's joint smoothness and compact integration. Formula
(WT) therefore gives a source-specific finite-truncation interface. Passing
its scalar terms to the full arm uses the admitted scalar/time/normal bounds,
locally uniformly on a compact angular set. The same compact derivative
argument behind (CR) makes its constant uniform on compact base sets.
This does **not** yet identify the limit with the complete physical left-QNM
action: the actual cutoff limit, both radial normalizations, all other faces,
source contacts and SS/SV/VV correction terms must still be admitted and
summed. Products of two independently weakly converging fields are not
covered. Formula (WT) is not Lean-formalized here.

The already logged contact-corrected radial current (item 22) contains
`(r^2-1)*partial_r+partial_v=partial_x+partial_v`. Its weighted normal
term is controlled by (CN). Temporal and angular faces retain further
normal/mixed derivatives, for which (CRJ)/(CFJ) specifies the scalar
source datum to identify. This is a refinement of that existing
interface, not a second claim of the same current identity.

**Search check.** The new deep corpus query for a weighted characteristic
remainder covered the cached inventory of 57,388 files (`partial=false`);
its generic Taylor candidates supplied no complete cap/current theorem.
The direct source derivative and growth results above are the applicable
ingredients. Broad recent Mellin search found Poldaru's
[expansion by regions](https://arxiv.org/html/2607.26291v1) (28 July 2026),
which studies positive-polynomial integrals. That result is not applied
to the complex theta integral; (CR) uses the source's own bounds.

A further deep query for angular derivative/covariance passage covered the
cached inventory of 57,391 files (`partial=false`, no retrieval errors;
compiler metadata is predominantly source-only/pending). Its proposed
boundary-growth ingredient was an unrelated squarefree-convolution theorem
and was rejected. Applicable source results were the native mean's joint
smoothness, its Laplacian commutation and the actual coexact curvature shift.
They motivate (WT), but do not supply its complete-action cutoff limit.

Broad Noether/semigroup/rigidity searches found the July 2026 publication
[Hinterbichler–Saha–Yan](https://arxiv.org/html/2602.10188), whose equations
(1.2), (1.23) and (1.24) concern special-mass fields and explicitly retained
current improvements. No identification of those fields with the complete
HB metric was obtained. [Arnold's August 2026 semigroup paper](https://arxiv.org/html/2608.13397v4)
gives a growth improvement under a Kreiss resolvent bound; no such bound for
the complete HB evolution was established here, and the cited estimate itself
is not finite-time extinction. [Cunden et al., September 2026](https://arxiv.org/html/2609.04057v1)
classify limits of invariant-distribution-preserving stochastic matrices;
no positive stochastic realization of the HB action was found. These papers
are not used as premises in the Lean proofs.

## Actual weighted correction discrepancy, 12 September 2026

**Cross-source tensor comparison, paper derivation.** The current source corpus
has a shift-two inverse and a principal-tensor cancellation for the square of
one literal scalar. This is relevant to the retained quadratic correction but
does not directly identify the exchanged source `E2(H,M)` in (WBC).
For the normalized symmetric tensor
`X=[(dS tensor dT+dT tensor dS)/2]^TF`, direct covariant differentiation gives

```
div X = (lambdaS*S*dT+lambdaT*T*dS)/2
      = (lambdaS+lambdaT)*d(S*T)/4
        +(lambdaS-lambdaT)*(S*dT-T*dS)/4.             (XP)
```

The mixed Hessian terms cancel against the derivative of the trace; the two
remaining Laplacians are replaced by the original scalar eigen-equations.
If the original shift-two inverse of `S*T` is admitted, its Hessian cancels
only the first term: with `(2-Delta)U=S*T`,
`div[X+(lambdaS+lambdaT)*HessTF(U)/2]
=(lambdaS-lambdaT)*(S*dT-T*dS)/4`. This follows from
`div HessTF(U)=d(Delta U)/2-dU` on the original curvature-minus-one metric.
No mixed inverse is constructed or assumed in the closed Lean results here.

For a same-copy first source and its actual marked scalar reader, the current
definitions give `lambdaS=rho*(rho-1)` and
`lambdaT=rho*(rho-2)/4`, hence
`lambdaS-lambdaT=rho*(3*rho-2)/4`. This coefficient is nonzero at every Xi
occurrence since its possible roots are real and the occurrence has nonzero
imaginary part. This does not establish nonvanishing of the current itself.
The positive result is the explicit additional source current in (XP),
which a cross-source tensor reconstruction must retain. Its complete
Einstein-channel identification and Lean formalization remain open; no
failure of HB or new extinction claim follows from this comparison.

**Positive second pass on (XP), paper calculation.** Put
`J=S*dT-T*dS` and retain the original bilinear metric contraction and
coexact convention `*dT=(T_y,-T_x)`. Metric compatibility, the product rule,
`div(*dT)=0` and `<dT,*dT>=0` give the exact identity

```
<J,*dT> = -div(S*T *dT).                            (XF)
```

There is no complex conjugation in (XF). In the original upper half-plane
coordinates, its density is `-T*(S_x*T_y-S_y*T_x) dx dy`, equal to
`-d(S*T*dT)`. The outward flux of `S*T *dT` on a horizontal upper edge
is `-S*T*T_x dx`; the opposite edge carries the opposite orientation.
Thus even an eigenvalue-mismatch current can have a boundary-only
same-reader projection. A nonzero mismatch coefficient is not an
obstruction to its integrated vanishing.

For a different response scalar `U`, however, direct differentiation gives

```
<J,*dU> = -div(S*T *dU)+2*S*<dT,*dU>.               (XFU)
```

The second term is the remaining Jacobian pairing. This is the relevant
distinction when the correction contains the source-derived angular
inverse rather than the reader scalar itself. If a finite integration
domain and its actual fields admit Stokes, (XF) specifies its entire edge
flux; it does not prove those fluxes zero. Horizontal evenness would cancel
the displayed horizontal flux on a symmetric cell, but the retrieved
evenness theorem concerns the absolutely convergent Poincare domain.
It has not been transported here to every literal continued field,
correction and boundary. No complete Einstein pairing is identified with
(XF) or (XFU), and neither paper identity is claimed as a Lean theorem.

**Check against the actual scalar/vector source.** The original
`D4BMQuadraticMixedSource.tensor` contains
`squareCovector=*d(S^2/2)` and
`gradientCovector=*d(y^2*(S_x^2+S_y^2)/2)` with its stated radial/time
coefficients. Pairing either with the actual coexact reader `*dT` gives
`<*dF,*dT>=<dF,dT>=div(F*dT)-lambdaT*F*T`, using the literal reader's
equation. This is a gradient product, not the Jacobian in (XF).
Consequently (XF) cannot erase that existing scalar/vector overlap.
This recovers the source-contact overlap already recorded in log item 15,
with its original reader eigenvalue and flux; it is not a new general
extinction mechanism or a reason to drop the independent channels in (WBCQ).

**Continuation attack closed at the local metric equation.**
`ThetaCuspHawkingBMLeftQNMMetricEquation` passed scratch verification and its
isolated cached exact-leaf audit (133 seconds, 2 jobs). Both prescribed
fundamental frequencies and both original radial normalizations are covered.
The continued radial equations and their smooth potentials supply the third
radial derivative and complete ordered metric two-jet. The actual source
master curl vanishes by the literal angular equation. All 16 cosmological
Einstein components vanish on the original time-zero action slice; the
field is identified with the original `physicalLeftModeStream` reconstruction
on the entire exterior. No frequency or clock is changed. This supplies
the `L M=0` fact needed in (WBC); the remaining correction/source pairings
and full boundary limits still require cancellation.

**Closed source identity; scratch and cached exact-leaf audit passed.** The actual
weighted `++-` Einstein source is affine in changes of the full quadratic
corrections. For first jets `P,Q`, quadratic discrepancies `A_pp,A_pm` and
cubic discrepancy `B_ppm`, the exact change is

```
<W0(M), L B_ppm+E2(P,A_pm)+E2(Q,A_pp)>
 +<W1(Q,M), L A_pp>+<W1(P,M), L A_pm>.                 (WC)
```

Here `L` is the original cosmological Einstein linearization, `E2` its actual
second derivative, and `W1` the full determinant-volume and inverse-index test
weight derivative. Every tensor entry and independent scalar/vector amplitude
remain. The Lean proof differentiates the original nonlinear source coefficient;
the original physical first modes discharge the vacuum and linear equations.
No quadratic equation for the discrepancies is assumed. This identifies the
exact local integrand which the source translation defect has to cancel after
physical projection. It does not itself admit the differentiated causal
correction fields or remove a
horizon, cusp, characteristic or source-contact contribution. In particular,
the auxiliary quadratic discrepancy term in (TV) is not a substitute for (WC).

`RHTower.D4BMWeightedCorrectionDiscrepancy.physical_mixed_discrepancy`
proves (WC) with no supplied field equation. The 219-line leaf is wired;
its isolated cached `lake build` passed (2 jobs). No heartbeat, recursion-depth
or transparency override was added.

**Derivation of the identity.** For an on-shell first jet `H`, the original
cubic coefficient is
`W0*(L l+E2(H,k)+E3(H,H,H)/6)+W1(H)*(L k+E2(H,H)/2)`.
Replacing `k,l` by `k+A,l+B` cancels the third-variation term and leaves
`W0*L B+W0*E2(H,A)+W1(H)*L A`. Differentiate this identity at
`H=P+z Q`, with all four polynomial correction slots retained. Only `A(0)`,
`A'(0)` and `B'(0)` survive, yielding (WC). This uses the actual nonlinear
source coefficient; it does not require a quadratic equation for `A`.

**Completed local attack.** The original weighted bulk second derivative now
retains both first residuals. The cyclic identity is specialized to original
physical first modes, complete symmetric correction jets, and the actual
ingoing mixed correction. This keeps the quadratic source residual in its
geometric weight contraction. The target remains the integrated physical
pairing and its fixed-clock cancellation; local exchange alone does not prove it.

**Boundary exchange test, paper calculation.** Let `Theta_g(M)` be the original
connection-current divergence with its determinant weight, as defined by
`EinsteinCyclicVariation.boundary`. On the original vacuum background, for
linearized solutions `H,M` and a symmetric correction jet `A`, the product
rule and the existing local cyclic-action identity give

```
W0(M)*E2(H,A)+W1(H,M)*L A
 = W0(A)*E2(H,M)
   +D_H D_A Theta(M)-D_H D_M Theta(A).                (WB)
```

All products here contract every tensor entry. To verify (WB), differentiate
`W(g;M)*E(g)` in directions `H,A`. The vacuum residual and `L H` vanish,
leaving the left side. Exchange `A` with `M` in the cyclic identity. Both
`L H` and `L M` then vanish, leaving the first term on the right. The
remaining two derivatives are exactly the original boundary-divergence
defect, with the displayed order and sign. No field equation for `A` has
been used. The specialization to original Xi first modes is now Lean-proved below,
and the general independent test retains its full residual in (WBT).
Boundary admission for the actual causal corrections is still unproved.

Thus (WC) transfers to two explicit correction/source pairings plus original
boundary divergences, not to zero by cyclicity alone. In a cutoff physical
action, (WB) retains every oriented face before taking a common limit.
Horizon, cusp and characteristic faces and the response's source-contact
terms still need their actual differentiated integrals and matching limits.
Neither the already admitted field-value limits nor the on-shell-only
Hessian pairing theorem discharges this obligation.

**Independent full-test refinement.** Before proving any equation for the
actual left metric, the same product-rule argument gives the sharper identity

```
W0(M)*E2(H,A)+W1(H,M)*L A
 = W0(A)*E2(H,M)+W1(H,A)*L M
   +D_H D_A Theta(M)-D_H D_M Theta(A).                (WBT)
```

Only the original first source `H` is on shell in (WBT). In particular, (WC)
now has an exact full-test interface: its two correction terms become
`W0(A_pm)*E2(P,M)+W0(A_pp)*E2(Q,M)` plus
`(W1(P,A_pm)+W1(Q,A_pp))*L M` and the two original boundary defects. The
linear cubic work `W0(M)*L B_ppm` remains. A proof of the actual left metric's
full linear equation removes precisely the displayed test-residual term;
it does not remove either correction/source pairing or boundary defect.

This distinction is visible in the current reconstruction itself.
`D4BMMixedActionCurrent.mixedJet` retains the metric and its first derivative
and sets its second derivative slot to zero. `streamMetricJet` uses that
constructor because the Einstein action current needs only the first metric
jet. The actual stream two-jet therefore suffices for that current, but this
placeholder metric second slot must not be used as the actual metric
second derivative in (WBT). A separate complete derivative realization is
required for its Einstein residual. This is an interface distinction, not
a defect in the proved first-jet current theorem.

The original `CoordinateEinsteinOnShellPairing` has now been extended and
its exact cached leaf audit passed. `testCoefficient_first` identifies the
actual weight derivative; `bulk_second_eq_hessian_and_weights` retains both
inhomogeneous first residuals. The previous on-shell theorem follows as a
short specialization. `ThetaCuspHawkingBMInhomogeneousCorrectionBoundary` now proves the physical
correction/test specialization of (WBT), its two-original-Xi-mode specialization
of (WB), and the unchanged original mixed ingoing correction case. Scratch and
the cached exact-leaf audit passed; the 210-line leaf is wired. The actual
left-metric derivative realization is now closed by the continuation result
above; integrated cancellation remains open.

The complete composition is now closed in
`D4BMMixedCorrectionBoundary.complete_mixed_exchange`:

```
Delta C = W0(M)*L B_ppm
        + W0(A_pm)*E2(P,M)+W0(A_pp)*E2(Q,M)
        + (W1(P,A_pm)+W1(Q,A_pp))*L M
        + boundaryDefect(P,A_pm,M)+boundaryDefect(Q,A_pp,M). (WBC)
```

Here each `boundaryDefect` is exactly the two differentiated original
divergences in (WBT). The 38-line leaf passed scratch verification and its
isolated cached exact-leaf audit (86 seconds, 2 jobs); it is wired after the
inhomogeneous exchange leaf. The proof uses the actual mixed source
derivative, retaining all four correction slots before differentiation.
It neither substitutes an invented functional nor sets the displayed
work, residuals, faces or contacts to zero. Applying (WBC) to the physical
action still requires the original fields' derivative admission and common
boundary limits. It is a local integrand identity, not an integrated
extinction theorem.

**Actual left-QNM specialization of the complete exchange.**
`D4BMLeftQNMCorrectionExchange.complete_mixed_exchange` passed scratch
verification and its isolated cached leaf audit (290 seconds, 2 jobs).
The 95-line module is wired; generated documentation was refreshed and
`scripts/formal_tools.py lint --check-generated` passed. The actual symmetric
metric field supplies symmetry of every derivative slot and, by the source
equation just proved, both test residuals vanish. At the unchanged time-zero
action slice, for either prescribed frequency and radial normalization,

```
Delta C = W0(M)*L B_ppm
        + W0(A_pm)*E2(P,M)+W0(A_pp)*E2(Q,M)
        + boundaryDefect(P,A_pm,M)+boundaryDefect(Q,A_pp,M). (WBCQ)
```

The first source copies and scalar/vector amplitudes remain independent;
all correction and tensor slots still enter the original mixed derivative.
No correction equation is supplied. In particular the moving metric weights
were exchanged by (WBT), not suppressed. The right side of (WBCQ), with
the actual translated causal correction discrepancies substituted, is the
exact surviving local work to integrate. Removing `L M` has not proved
derivative admission for those causal fields, integration by parts over the
physical domain, or cancellation of its horizon, cusp, characteristic and
source-contact terms. Nor does an identity for the *change* of the complete
source assign zero to its value at the source-predeclared clock.

**Complete left metric: source-derived derivative route.** The current corpus's
`physicalTortoiseMode_hasDerivAt` gives both `Y'=Y1` and
`Y1'=(w^2-lambda*angularWeight^2)*Y` on the original response band. Thus the
actual third derivative is obtained by differentiating the displayed
smooth-potential right-hand side, not by assigning a free third jet.
For the original radius lift `c(r)=r*Y(tortoise(r))`, direct differentiation
of the already proved `c''=(r*Y''-2*Y')/(r^2-1)^2` gives

```
c'''=(r*Y'''-3*(r^2+1)*Y''+8*r*Y')/(r^2-1)^3.       (LJ)
```

All `Y` derivatives in (LJ) are evaluated at the same original tortoise
coordinate, whose derivative is `1/(r^2-1)`. In the complete metric jet,
`D4BMVectorStream.cosmological_component` expresses the Einstein residual
through the original `master` and `masterFirst`. The actual left time phase
is `exp(-w*tau)`, so this construction uses `-w` in the metric reconstruction
and the unchanged `w^2` radial equation. Formula (LJ), the complete physical-left
metric realization and its residual closure on the original action slice are
now Lean-proved in `D4BMLeftModeRadialEquation`. The existing stream metric
first-jet constructor has not been used as a placeholder for that realization.

**Current research search record.** Deep and method-view searches used the full
available index (latest successful deep search: 57,348 files, `partial=false`;
most compiler metadata was pending, so applicability was checked in scratch).
A subsequent reciprocity search reported a disconnected semantic worker;
lexical fallback returned 637 matches. The broad recent-paper searches also
opened the abstracts of [Yun, 1 June 2026](https://arxiv.org/abs/2606.01507),
[Garnek, 8 June 2026](https://arxiv.org/abs/2606.10181),
[Ghosh, 2 September 2026](https://arxiv.org/abs/2609.02699), and
[Tesfaye--Palumbo, 9 September 2026](https://arxiv.org/abs/2609.10541).
These were screened as cross-field leads; no extinction theorem or physical
positivity hypothesis was imported from them.

The inhomogeneous-boundary deep search, causal-correction method-view search,
and full-left-metric deep search subsequently completed without partial
results, with 57,354, 57,360 and 57,362 inventoried files respectively.
The last search exposed the original radial derivative/ODE interface used
in (LJ); no retrieved premise was accepted as an extinction proof. Broad
duality, memory, transport, reciprocal and Lagrangian searches also screened
the primary abstracts of [Sujanani--Ghadimi--Wolkowicz, 4 August 2026](https://arxiv.org/abs/2608.03170)
and [Xu--Zhao, 10 September 2026](https://arxiv.org/abs/2609.11072).
These concern convex augmented-Lagrangian complexity and reciprocal
multiple-polylogarithm/Cauchy-number identities respectively. Only their
abstracts were read; neither supplies a source equation, boundary
cancellation or positivity theorem for this calculation.

The continuation attack used another six full-index deep/method-view searches.
The first full-left-equation search had a semantic-retrieval budget timeout
(`partial=true`, 57,366 files); five subsequent searches completed without
errors or partial results, ending at 57,373 indexed files. These covered
radial derivative methods, complete variational work, tensor cancellation,
cross-reader currents and coexact/parity mechanisms. Most compiler metadata
remained pending. The adopted `TwistedRadial.contDiffOn_of_linear_ode` method
was checked against the original radial equation in Lean. The other searches
did not supply a complete boundary cancellation. Broad reciprocity, virial
and rigidity searches reopened [Vu et al., 3 September 2026](https://arxiv.org/html/2609.04169v1),
Sections 2 and 3.2–3.3: transpose reciprocity and an additional positive
matrix condition have distinct roles there. No positivity or Einstein
identity is imported from that finite-network setting.

## Fixed time translation of the original future fields, 12 September 2026

**Closed source translation identity.** Keep the same physical time coordinate
and any source-independent `T>=0`. Write `g_s(u)=chi(u) exp(2su)` and
`d_T g_s(u)=g_s(u+T)-exp(2sT)g_s(u)`. Direct differentiation leaves the
actual first-derivative defect. Both defects are supported on `[-T,1]`.
Consequently the original reduced source obeys

```
F_red(tau+T,y)-exp(2sT)F_red(tau,y)
 = reducedCoefficient(s,0,a,1,y) d_T g_s(tau+y)
   +2 radialLiftFirst(s,0,a,1,y) d_T g_s'(tau+y).        (TC)
```

The source's exponential factor is retained in (TC); no QNM frequency or clock
is replaced. Actual translation has difference `(exp(2sT)-1)F_red` plus this
onset defect. Linearity of the admitted original future integral gives
its response to precisely (TC). On the late ingoing region `tau+x>1`, `x<0`,
both native causal supports imply `tau+h+y>1`, so the defect integral
vanishes. The cap's two arms and original lift obey the same late
translation law. This test does not reach the past-horizon datum: at fixed
outgoing `v`, `tau=v+x` gives `tau+x=v+2x->-infinity`. A late-region law cannot
be passed to that boundary. Source/current projection and complete-action
cancellation remain unproved.

`ThetaCuspHawkingBMSourceTimeTranslation` now proves (TC), the actual onset
derivative and its strip support, absolute admission and the exact defect
integral, and all three late-field translation laws. It also derives the
defect integral's past limit as
`pastResponse(v+T)-exp(2sT)pastResponse(v)`. Scratch checking and the cached
exact-leaf audit passed; the module is wired. The strip is bounded in ingoing
time only, not in spacetime. No global clock covariance of the radiative data
or complete corrected action follows from these theorems.

The alternative passivity test is being checked against the actual complex
Einstein action and all boundary supply terms, rather than assuming a positive
storage functional. The existing centered-QNM finite-clock covariance theorem
is explicitly RH-equivalent and is not used as an input.

**Complete-action checkpoint; physical realization unproved.** In the symmetric
quartic expansion recorded below, let the translated first fields be
`p'=alpha p`, `m'=beta m`, and write the actual correction discrepancies as
`a'=alpha^2 a+A`, `b'=alpha beta b+B`, `c'=beta^2 c+C`. Here `a,b,c` are
the `++`, `+-`, `--` corrections, and `A,B,C` must eventually be the translated
original solutions, not chosen replacements. Multilinear expansion gives

```
I4' - alpha^2 beta^2 I4
 = alpha^2 E_a(C)+alpha beta E_b(B)+beta^2 E_c(A)
   +L(A,C)+L(B,B)/2,                                  (TV)
E_a(z)=L(a,z)+T(p,p,z)/2,
E_b(z)=L(b,z)+T(p,m,z),
E_c(z)=L(c,z)+T(m,m,z)/2.
```

To check (TV), expand `L(a',c')` and `L(b',b')/2`; their linear discrepancies
are `alpha^2 L(a,C)+beta^2 L(c,A)+alpha beta L(b,B)`. Expanding the three
cubic terms supplies exactly the remaining terms in `E_a,E_b,E_c`; the pure
quartic term scales by `alpha^2 beta^2`. Thus even formal stationary
cancellation of the linear discrepancies leaves `L(A,C)+L(B,B)/2`.
For the original rates, `alpha beta=exp(-3T)`; the physical clock is unchanged.
The actual `L,T` would have to be derivatives of the complete geometric action
with its determinant and inverse-index weights. Transferring `E_a,E_b,E_c`
to source equations then retains the original horizon, cusp, characteristic,
source-contact and switching-residual terms. The scalar-source theorem (TC)
does not identify the independent SS/SV/VV correction discrepancies in (TV).

The tempting passivity inference is not established. The actual residual
expression in (TV) is complex-bilinear; no source-derived positive storage
identity for it has been constructed. [Borja, arXiv:2608.15218](https://arxiv.org/html/2608.15218v1),
Section 2, assumes a nonnegative storage function and retains the external
input/output supply. Its damping argument gives asymptotic decay under added
feedback and detectability conditions. Those conditions have not been derived
for the original complete left-QNM action. Neither that argument nor (TV)
produces fixed-clock extinction here. This is an unclosed physical comparison,
not a new conditional Lean wrapper or a retired HB route.

**Search record.** Deep finite-clock and hybrid angular-method searches both
returned `partial=false` with 57,336 indexed files. The passivity/coercivity
deep search returned `partial=false` with 57,338 files. The retrieved fixed-weight
Ward and finite-QNM clock conditions are RH-equivalent or cancel with zero
total weight; neither is a source producer. Angular mean smoothness/commutation
and cusp-energy bounds remain relevant to the separate differentiated boundary
admission, but did not supply complete-action positivity. The original source
and cap translation proofs above use the checked onset, causal-support and
Bochner-integral APIs, without a retrieved covariance premise.

## Original advanced response at the past face, 12 September 2026

**Current source-level test.** The proved gradient absorption has the sign
`F_original=L lift+F_reduced`. Combined with the paper cap Green identity,
the candidate advanced original field is `lift-H+R_adv(F_reduced)`. Its
past face must retain both the cap and the reduced response. Neither can be
set to zero from the ingoing future trace.

Use source ingoing time `a=t_source+y` and fix target outgoing time `v`,
`tau=v+x`. The actual reduced response integrand becomes

```
K_D(a-y-v-x,x,y;z) * timeReducedCoefficient(s,amplitude,a-y,y).
```

Its limiting kernel is one half the original direct/image difference:

```
1_(a>=v+2y) M_Q((1+u_y) exp(a-v)+u_y;z)
 -1_(a>=v) M_Q((1+u_y) exp(a-v)-u_y;z),
u_y=-tanh y.                                                   (PK)
```

This is the existing source-horizon kernel limit after the actual symmetric
kernel's two radial arguments are exchanged. Both characteristic inequalities
remain. The source is zero for `a<0`.

**Closed Lean majorant and coordinate change.** For `a>=0`, both direct/image
invariants at every finite target radius are at most `5 exp(a+|v|)`.
Indeed, put `b=a-y-v`; `cosh(b-x)<=2 cosh b cosh x`,
`|sinh x sinh y|<=cosh x cosh y`, and
`cosh b<=2 exp(a+|v|) cosh y`. The corresponding angular radius is at most
`a+|v|+log 10`, uniformly in target `x` and source `y`.
The established source bound in these coordinates is
`|F_reduced coefficient|<=C exp(-c0 a+2y)`. Thus the full theta density is
bounded by a constant (depending on `v,z`) times
`exp((a0-c0)a) exp(2y)` on `a>0,y<0`, with the original `a0<c0<2`.
The exact source-coordinate change in the original Bochner response is now
proved. The proof uses zero source before onset, zero kernel at negative delay,
Haar translation and admitted Fubini in both coordinate systems. Dominated
convergence then identifies the actual response's outgoing past-horizon limit
with the integral of (PK) times the original source coefficient divided by two.
The limiting density's absolute integrability is independently proved.
`ThetaCuspHawkingBMPastSourceResponse` passed scratch checking and the cached
exact-leaf audit; the module is wired. No derivative or wave-equation assertion
is inferred from the value limit.

**Connection to the actual physical left test.** The existing
`physicalProjectedModeAction_transport` gives, on its physical frequency band,
the exact finite radial identity

```
j_R(t)-j_R(s) = [-(mu-2) integral_s^t g(x) F(x) dx
                 -(C(t)-C(s))] N,                            (PA)
C(x) = [R(x) g(x)+R(x)^2 g'(x)/(R(x)^2-1)] F(x).
```

Here `F` is the actual continued angular source projection, `g` the original
left radial mode, `N` its angular bilinear square, and
`mu=physicalAngularParameter^2-1/4`. The theorem uses
`3/2<Re(w)<2`, `Im(w)!=0`; it is not a direct endpoint assertion at a QNM.
This source/current identity retains both endpoint contacts. To use the new
past datum in (PA), the actual projected differentiated field must be identified
with its admitted source integral, and the original horizon and cusp operations
must commute with the projection and continuation. The cap must undergo the
same operations. The existing value majorant proves none of these exchanges.
Even their completion would leave the independent SS/SV/VV channels, solved
`++` and `+-` corrections, retained spin two, changing weights and remaining
characteristic/source-contact faces in the complete action. No cancellation or
fixed-clock invariance of that sum is asserted.

**Search record.** The source-cap and Green-method searches returned partial
coverage of 57,326 files. A subsequent deep/all-views request for actual horizon
radiation and the left projection returned `partial=false`, 57,331 indexed files,
741,597 declarations and 692,151 ready method records; 44,831 compiler entries
were pending. Its proposed boundary-pairing and residue ingredients did not
supply the differentiated source-integral or cancellation theorem. The actual
finite-current identity above was checked directly in its source. Broad recent
arXiv searches also retrieved [2606.20825](https://arxiv.org/abs/2606.20825),
whose abstract derives power-correction scaling from boost invariance, and the
[Waves 2026 abstract collection](https://arxiv.org/abs/2607.19425). Only their
abstracts were inspected; neither supplies an HB extinction theorem used here.

## Cap trace and physical contact, 12 September 2026

**Current attack.** Test whether the source cap that cancels the lift value also
cancels its physical charge. The existing all-component Einstein stream current,
not a scalar substitute, fixes the interface. For ingoing covector jets `P,Q`, put
`f=R^2-1`, `A=rough angular Laplacian minus one`,
`O P=R^2 f P_RR+R^2(P_vR+P_Rv)+2R P_R-2R P_v`, and `M=O+A`.
The original source contact has components

```
B_v = sum(P_R M Q-Q_R M P)/R^2,
B_R = sum((f P_R+P_v) M Q-(f Q_R+Q_v) M P)/R^2,
B_X = B_y = 0.
```

Adding it to the actual regular Einstein current cancels only the orbit-master
terms. Its radial component is exactly

```
(J+B)_R = sum((f P_R+P_v) A Q-(f Q_R+Q_v) A P)/R^2.       (CR)
```

At `R=1`, this is `sum(P_v A Q-Q_v A P)`. Thus a contact-corrected
**radial** horizon limit needs the admitted time/angular traces and control of
the `f P_R` terms; it does not require a separate second-normal-derivative
limit. Evaluating a regular jet at `R=1` alone does not prove that limit.
The time component retains normal derivatives. The two angular components
retain the original mixed time/radius curls, so (CR) removes no cusp face.

The cap's already derived scalar trace is `l_infinity g(v) Q`. Its associated
angular covector trace is `l_infinity g(v) *dQ`. Testing these literal trace
fields against each other gives a source-specific angular Wronskian, retaining
`*d(Delta Q-2Q)`. This is the same contact-corrected radial **trace expression**
as the original lift. It is not a zero-charge theorem. Identification with the
integral cap's differentiated current still requires admitted angular/time
traces and the weighted normal remainder. The complete left-QNM, SS/SV/VV,
correction, changing-weight and other boundary contributions remain separate.

**Lean status.** `ThetaCuspHawkingBMCapTraceAction` proves the all-face
current/contact identity, its identification with the original exterior
Einstein action and source contact, the literal trace's actual coexact/time/
angular derivatives, and the trace pairing's clock and square/gradient
formulas. The finite time integral and late fixed-translation law are closed.
Scratch check, exact cached leaf audit and formal lint passed; the module is wired.
The cap integral's differentiated horizon flux remains unproved.

**Precise remaining trace admission.** Write `D_R P=f P_R+P_v` and let
`p_v,q_v,a_p,a_q` denote the proposed time and angular traces. With
`Phi=sum(p_v a_q-q_v a_p)`, (CR) gives the exact finite-radius defect

```
(J+B)_R-Phi = (R^(-2)-1) Phi
  + R^(-2) sum((D_R P-p_v) A Q+p_v(A Q-a_q)
               -(D_R Q-q_v) A P-q_v(A P-a_p)).          (CD)
```

Triangle inequality bounds the right side by the sum of the absolute products
displayed. For the cap/physical-left pairing, this requires convergence and
integrable majorants for these actual products on each admitted time/angular
cutoff, followed by the original cusp subtraction and QNM continuation. The
previous scalar value limit proves none of those derivative interchanges.
This is a narrower interface than separately demanding every second normal
jet, but it still retains the weighted normal remainder and all source contacts.
For the cap, the physical stream uses `R H`; its radial factor belongs inside
`D_R P` and cannot be deleted merely because `R=1` in the boundary value.

**Fixed translation test.** The literal trace expression has clock factor
`exp(-6v) chi(v)^2`. For `v>=1` and any fixed `T>=0`, its translation is
`exp(-6T)` times itself. This statement concerns a boundary density, not the
complete action. It provides no finite-clock invariance and no extinction.
No frequency has been retuned. The angular factor still contains both
`(2lambda-2) sum(*dQ)^2` and `sum(*dQ)(*dE)`, since the original
`fullGradientEnergy_coexact` theorem identifies `*dE=2 fullGradientCovector`.

**Search record.** Two whole-corpus requests, deep and method views, returned
57,317 indexed files with `partial=false`; the compiler snapshot still had
44,818 pending files, so candidates were verified locally. Useful current
hits were the complete stream current, original contact, full incoming chart
identity, and native angular-Laplacian primitive. Broad arXiv searches for
symplectic, characteristic, Darboux and observability did not supply a verified
June–September 2026 theorem for this interface; direct date-sorted searches
failed with a cache miss and HTTP 429. The retrieved
[Getzler deformation paper](https://arxiv.org/abs/math/0002164) is from 2000
and concerns Hamiltonian operators of hydrodynamic type. Its abstract gives
no HB boundary or source-action theorem; none is imported into this argument.
A follow-up derivative-admission query returned partial coverage of 57,326
files and no verified theorem admitting the actual cap's derivative limits.

### Opposite horizon of the actual cap: paper calculation

The same cap construction also determines a past face. At fixed outgoing
time `v`, put `tau=v+x` and let `x->-infinity`. With `M_Q(Z,z)` the complete
theta circle mean at `arcosh Z`, the resulting boundary value is

```
H_past(v,z)=-l_infinity [integral_0^infinity g'(u) M_Q(1+2 exp(u-v),z) du
                       -integral_v^infinity g'(u) M_Q(2 exp(u-v)-1,z) du]. (PH)
```

**Derivation.** The direct arm is `A_s(v+2x,x)`. Shift its integration
variable to `u=v+2x+h`. Its mean argument becomes exactly
`1-c(x)+c(-x) exp(u-v)`, where `c(x)=exp x/cosh x`. For all sufficiently
negative `x`, its lower limit is negative; `g'(u)=0` for `u<0` removes that
interval. Since `c(x)->0` and `c(-x)->2`, the direct argument tends to the
first argument in (PH). The image is `A_s(v,-x)`; the same shift
`u=v+h` gives `1+c(-x)(exp(u-v)-1)`, hence the second argument.
Its support remains `u>=v`, so this argument is at least one. The onset
again removes any negative-`u` portion.

**Admission.** On the remaining `u>=0` domain the direct radius is bounded
uniformly in `x` by `u+|v|+log 6`, because `0<=c(±x)<=2`. The image has
the already proved radius bound `u+|v|+log 4`. Full source growth and the
original onset derivative give a common constant times `exp((a0-c0)u)`,
with the existing `a0<c0<2`. Both integrals converge absolutely and dominated
convergence proves (PH). No principal angular term or clock derivative was
discarded. This is a paper proof; (PH) has not been formalized in Lean.

**Whole-chain consequence.** A comparison with a retarded physical response
must compare this past datum with the other advanced/seed/pulse terms as well
as the future trace. No vanishing or nonvanishing of (PH) is asserted. In
particular, subtracting the cap is not by itself a proof of causal-response
identification. This exposes an explicit source-derived datum for that test.

## Future null-cap Green calculation, 12 September 2026

The retained lift trace is now tested against the **original future source kernel**.
This attacks the boundary term needed in a causal/transpose comparison. It does
not identify that comparison with the complete corrected Einstein action.

Put `p=tau+x`, `r=tau-x`, `x<0`, and fix a finite source outgoing cap `B>=r`.
Source null coordinates are `a=t_source+y`, `b=t_source-y`. The direct future
region is `r<=b<=B, p<=a<=b`; the image region is `r<=b<=B, r<=a<=b`.
Let `K_D(a,b)` and `K_I(a,b)` be the actual full theta-square Riemann means in
these two regions, without the kernel's factor one half. For the literal lift,

```
ell(t_source,y,z)=l(y) g(a) Q(z),
beta(a,b)=l((a-b)/2) g(a),
g(a)=timeOnset(2s,a),
l_infinity=-s(s-1) 2^(2s) amplitude²/4.
```

**Finite identity (paper derivation).** Let `G_B` mean the direct-minus-image
circle average of a source over those regions, with the original null Jacobian
and kernel normalization, hence factor `1/4`. The exact Green identity is

```
G_B(L ell)=ell(tau,x,z)
  + integral_p^B beta_a(a,B) K_D(a,B) da
  - integral_r^B beta_a(a,B) K_I(a,B) da.                 (FG)
```

Here `L` is the original full angular wave operator. To derive (FG), the
proved source-variable Goursat equation gives the averaged integrand
`K beta_ab-beta K_ab`. Write this as
`partial_a(K beta_b)-partial_b(beta K_a)` and integrate each finite triangle.
The characteristic identities are `K_D(p,b)=Q`, `K_I(r,b)=Q`, and
`(K_D)_a(a,r)=0`. The diagonal has `beta(a,a)=0`; the two diagonal terms
`K(a,a) beta_b(a,a)` cancel because the original direct and image kernels
agree there. Integrating the cap term `beta K_a` once in `a` cancels its
corner with `-Q beta(p,B)` (respectively `-Q beta(r,B)`). The direct vertex
leaves `Q beta(p,r)=ell`; the image vertex is on the zero diagonal. This
derivation keeps the onset derivative in `beta_a`; it sets no contact to zero.

**Cap limit.** With `a` fixed and `b->infinity`, the original invariants tend to

```
Z_D(a)=(exp(a-tau)-sinh x)/cosh x,
Z_I(a)=(exp(a-tau)+sinh x)/cosh x.
```

This follows from `cosh(a-tau-y)/cosh y` and `sinh y/cosh y`, with
`y=(a-b)/2`. Causal supports remain `a>=p` and `a>=r`, including their
characteristic values. The full source mean is evaluated at `arcosh Z`;
no principal-mode truncation is used.

Also `beta_a(a,B)->l_infinity g'(a)`. The radial lift and its first
derivative are bounded for compact radius in `[0,1]`, and the derivative
tends to zero at the horizon. The actual source rate has `Re(2s)<-2`.
Choose the existing majorant exponent `a0<c<2`, with
`a0=1+2|Re(rho-1/2)|`. On the direct cap,
`arcosh Z <= a-p+|x|+log 4`. Thus the cap integrand is bounded by a constant
times `exp(-(c-a0)a)`; the image obeys the corresponding bound. Dominated
convergence gives the paper consequence

```
lim_B G_B(L ell)=ell-H,
H=-l_infinity [integral_p^infinity g'(a) mean_Q(arcosh Z_D(a)) da
               -integral_r^infinity g'(a) mean_Q(arcosh Z_I(a)) da].       (FH)
```

The exponent `c` is only an integrable majorant. It changes no physical rate
or clock. This is a cap-exhaustion identity; identification with any separately
defined advanced Bochner wave inverse needs its own admission. In particular,
no differentiated Einstein flux or left-QNM projection is inferred from (FH).

**Consequences for the whole chain.** Finite retarded lift reconstruction and
(FH) differ by a specific source boundary operator. The existing future
admission for the reduced forcing cannot remove it. Testing the complete
action therefore requires the lift and angular-seed boundary operators,
retarded/future pulse difference, every scalar/vector channel correction,
changing weights, and the actual left-mode source contacts in one pairing.
The source-level sign or cancellation of that assembled pairing remains open.

**Derivative test for the actual current (candidate, not proved).** In physical
radius `R=-coth x`, the direct mean's argument is exactly
`1+(1-1/R)(exp h-1)`. Define
`G_j(v)=integral_0^infinity exp(j h) g(v+h) dh`, `j=1,2`.
Both time integrals converge because the actual source has `Re(2s)<-2`.
The native angular equation predicts the following ingoing traces for (FH):

```
H|R=1       = l_infinity g(v) Q,
H_R|R=1     = (l_infinity/2) G_1(v) Delta Q,
H_RR|R=1    = -l_infinity G_1(v) Delta Q
               +(l_infinity/4)(G_2(v)-G_1(v)) Delta(Delta-2)Q.
```

The first line is now proved in Lean; the other two require differentiating
the admitted full-source integral and proving derivative bounds. They are not
consequences of value convergence. The displayed candidates satisfy the
algebraic horizon recurrences for the original wave expression:
`2(partial_v+1)H_R+Delta H=0` and
`2(partial_v+2)H_RR+(Delta+2)H_R-2Delta H=0`, using
`G_j'=-g-j G_j`. This is a paper consistency check, not derivative admission.
The image has lower ingoing time `v-2x`; showing its first two physical-radius
derivatives vanish requires corresponding estimates, not just its zero value.
The metric stream reconstruction uses `R H`, so the Einstein-current test must
also retain this radial factor before taking its derivatives.

The angular seed has a different source field. Substitution of its actual
`parameter=(2s+1)(2s+2)` into `sourceSeedPolynomial` gives `-parameter*u`;
its scalar horizon coefficient is therefore
`-parameter*2^(2s)*amplitude²`. Applying the future comparison to it needs
a growth/admission proof for the constructed `fullAngularField`, not an
unjustified reuse of the theta-square bound. The source equation
`Delta A=parameter*(A+Q)` identifies the field, but does not alone bound its
global circle means or set its physical pairing to zero.

**Formal status.** `ThetaCuspHawkingBMFutureHorizonCap.lean` proves the original
source-horizon kernel limit with both causal supports, absolute admission and
uniform bounds for the full theta/onset cap integral, its exact onset endpoint,
zero Dirichlet value, and the original lift horizon trace. Combining that trace
with the earlier reduced future admission proves
`lift_response_sub_cap_ingoing_zero`. These are field-value statements. The
finite Green identity (FG), its cap-exhaustion identification (FH), the two
derivative formulas, and Einstein left-QNM incidence have separate statuses;
none is promoted to a Lean theorem by this field-value result.

Scratch checking passed. The final isolated cached command was
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFutureHorizonCap`;
the exact leaf passed in 70 seconds without proof diagnostics, and its guarded
artifacts were installed. Source SHA-256:
`700d7eea5d3d129e58011e29b0ec550c53d480e64bb09c4668090d15485409e8`.
The leaf is wired into `RHTower.lean`. Formal lint passed, with existing
large-file warnings; no umbrella or full build was run. The new leaf sets only
`autoImplicit false`, with no heartbeat, depth, transparency or instance overrides.

**External method comparisons.** The June 2026 curved-duality paper derives
an on-shell boundary contribution in a different action; it gives no reason
to delete the BM cap ([Chakrabarti–Manna–Raman](https://arxiv.org/html/2606.18013v1)).
The September stationary tidal-resonance model distinguishes conserved energy
from other resonant changes ([Bonga et al.](https://arxiv.org/abs/2609.03732)).
Those comparisons motivate retaining the actual observable; neither supplies
an Einstein-source or extinction premise. Current deep and method searches
covered 57,309 indexed files without partial results; retrieved generic
Poisson and Euler-boundary objects did not identify this physical cap.

## Future-response admission and the retained lift boundary

**12 September 2026 continuation; source admission and boundary values audited in Lean.**
The complete-action reflection test led to a concrete missing interface property:
the actual retarded-minus-advanced response requires admission of a future
integral for the original source. The existing abstract Peierls reflection
theorems assume both the physical incidence and the requisite cyclic pairing.
They do not produce either property. In particular, the actual left reader is
still distinct from the source field used in the abstract cyclic contraction.

There is an independent positive source estimate. Write `a(q)=1+2*|Re(center q)|`.
The full theta-square growth theorem gives `1 <= a(q) < 2`, including its uncut
cusp remainder. The original reduced source, including the onset derivative,
already satisfies for every `c < 2`

```
|F_red(t,y)| <= B exp(-c*t) exp((2-c)*y), y<0.
```

Choose `c=(a(q)+2)/2`. This is a majorant exponent, not a physical frequency or
clock modification. The source rate, fixed onset and response kernel remain
unchanged. For each supported direct or image kernel, the original hyperbolic
circle radius is at most its time separation `h`. Consequently the actual
Dirichlet kernel, with both supports and its factor `1/2`, satisfies

```
|K_D(q;h,x,y;X,k)| <= A exp(a(q)*(h+|k|)), h>=0.
|K_D(q;h,x,y;X,k) F_red(t+h,y)|
 <= A B exp(-c*t+a(q)*|k|)
           exp(-(c-a(q))*h) exp((2-c)*y).                 (A1)
```

Both exponents have strict gaps. The product majorant is integrable on the
entire future half-strip `h>0, y<0`; enlarging the actual cones does not discard
the image subtraction in the integral being bounded. Its integral is
`1/((c-a(q))*(2-c))`. Thus the **full reduced-source future convolution** exists
absolutely and obeys a uniform-in-`x,X` bound

```
|U_future(t,x;X,k)| <= C exp(-c*t+a(q)*|k|).              (A2)
```

This uses the two original powers of horizon decay. Using the full exponential
rate while forgetting that radial factor would obscure the two simultaneous
gaps. No theta-product projection, principal-only replacement or numerical
estimate enters (A1).

**Boundary consequence and whole-chain significance.** At fixed original
ingoing time `v=t+x`, (A2) gives `U_future(v-x,x;X,k) -> 0` as `x -> -infinity`.
The retained local lift has a different trace:

```
lift_h(v,z) = -s*(s-1)/4 * 2^(2*s) * amplitude^2
               * timeOnset(2*s,v) * fullSquarePotential(q,z).       (A3)
```

It follows that adding the lift to this future convolution retains (A3).
The existing finite retarded wave-image theorem does reconstruct the lift.
One cannot reuse that theorem for the infinite future domain: the advancing
time cap approaches an original horizon characteristic. A claimed identity
`G_advanced L(lift)=lift` must account for that characteristic contribution.
The prospective homogeneous correction carrying (A3) is an explicit boundary
obligation, not an additional assumption or an established advanced solution.

Admission of the integral and its scalar horizon trace do **not** yet prove its
wave equation, reconstruction of the original tensor advanced response, or
retarded/advanced transposition in the physical left-QNM action. This is a
potential trace, not a proved vanishing of its differentiated symplectic flux.
Angular derivative admission and finite-part cusp pairing remain necessary.
Nor do these results remove the independent SS/SV/VV corrections, changing metric weights, or source
contacts in the complete quartic action. The extinction interface remains a
source-derived sign or reflected cancellation of the actual action identified
with `-Sigma*|D|^2`; no such statement has been obtained.

During this pass another worker completed
`BMQuadraticConservation.physical_quadratic_source_conservation`. Its statement
and original-Taylor-source identification were checked directly. The actual
quadratic source has zero background covariant divergence, with both independent
parity amplitudes in each physical branch. This supplies a tensor constraint for
reconstruction. It does not identify a Killing current with the radiative reader
or remove the boundary in (A3); mixed branches and the complete physical pairing
still need their own derivation. Together, local conservation and (A1) give
independent source inputs to the response problem rather than an extinction
condition imposed on its output.

The current whole-corpus hybrid request with all retrieval views covered 57,294
files without partial retrieval. Its future-convolution candidates required
integrability as a premise and therefore did not prove this admission result.
The preceding advanced-response deep request was partial and mostly returned
toy integral models; those were not substituted for the native BM kernel.

**Formal status.** The new leaf
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullSourceAdvancedAdmission.lean`
proves `density_integrable`, `response_fubini`, `response_bound`,
`response_ingoing_horizon`, `response_dirichlet` and
`lift_plus_response_ingoing_horizon`, with all source bounds discharged.
The scratch check passed without diagnostics. The isolated cached final
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceAdvancedAdmission`
built only that leaf and passed in 25 seconds; matching artifacts were installed
and the umbrella import was added. No heartbeat changes or umbrella build.
The global lint run found no issue in this leaf but failed on a concurrent,
unwired `RouteEThreeToggleCommonNeighborRigidity` module; that unrelated work
was left untouched. This is a closed source-admission result, not completion of HB.

## Whole-chain test: causal reciprocity, source periods, and the actual reader

**12 September 2026 continuation. No extinction theorem obtained.** The chain remains
literal theta → Xi → retained spin two → actual causal/left-QNM action → extinction
at the common Hawking clock → RH. This pass tested three possible ways to remove
the complete action, rather than continuing the first-field horizon calculation.

**Causal reciprocity test.** The source-verified
`D4BMOnsetGreenReconstruction.kernel_reciprocal` exchanges the two radial arguments
of the original circle kernel. It does not exchange the retarded and advanced
time domains. Applying that exchange to the already derived finite horizon action
in `hb-causal-horizon-circle-kernel.md`, equation (8), therefore does not remove
the source-contact integrals or the final-time/angular-boundary term. In particular,
the kernel's radial symmetry is not the required symmetry of the assembled
quadratic-response pairing. No new no-go for HB follows from this failed inference.
The exact source kernel and its boundary terms remain usable for a direct evaluation.

The proposed auxiliary generator in `hb-causal-source-symmetry-repair.md` has also
been corrected by its author: its commutator includes `-2 K b' partial_v²`.
Consequently its defect is an operator, not the previously written multiplier.
Neither version supplies an independently derived symmetry of the complete
Einstein source. This pass does not revive that generator.

**Theta-product annihilation test.** The current corpus already evaluates the
native period at the actual physical scalar parameter `rho/2` in
`BMNativePeriodPhysicalValue.nativePeriodContinuation_physical_value`. It retains
the four-Lambda product and one principal-contact contribution. The Xi zero
removes one original Weyl coefficient, not those remaining terms. Repeating the
four-Lambda reduction would add no theorem. No vanishing of the original nonlinear
projection has been obtained by this test.

**Reader-pairing test and a positive boundary calculation.** The actual mixed
Einstein current in `BMPhysicalModeAction.physicalProjectedModeAction_value`
contains the complex-bilinear angular factor
`N_r=sum_j (physicalModeAngularJet r z j).value²`. It is the coexact-gradient square
of the original completed scalar reader. The physical calibration gives, with
`u0=(rho-1)/2`,

```
E_u(y) = A(u)y^(1/2+u) + B(u)y^(1/2-u) + R_u(x,y),
A(u)=Lambda(1+2u), B(u)=Lambda(2u),
A(u0)=0, B(u0)=Lambda(rho-1) != 0.
```

Here `Lambda` is the original completed zeta factor, not a new normalization.
The following calculation concerns the displayed principal family; identification
of its finite boundary coefficient with the complete reader integral remains a
separate analytic obligation. Put `p_u=A(u)y^(1/2+u)+B(u)y^(1/2-u)` and differentiate
the family before specializing to `u0`. Direct differentiation gives

```
p_u0 * partial_y(partial_u p_u)|u0
  - (partial_u p_u)|u0 * partial_y p_u0
 = 2*u0*B(u0)*A'(u0) - B(u0)^2*y^(-2*u0).       (R1)
```

The `B'` and logarithmic cross terms cancel. The derivative of the vanished
coefficient survives: `A'(u0)=2*Lambda'(rho)`. Thus replacing the family by its
single surviving Weyl power *before* differentiating loses the constant term.
This is a positive boundary identity, not a proof that this constant is nonzero.
No simplicity of Xi zeros is assumed.

The finite-domain Green identity predicts the precise test for its physical
incidence. The original scalar equation is `Delta E_u=(u²-1/4)E_u`; differentiating
it and applying the product rule gives

```
div(E_u grad(partial_u E_u)-(partial_u E_u)grad E_u)
  = 2*u*E_u².
```

If the parameter derivative is admitted for the complete original family and its
remainder boundary terms are shown to vanish in the prescribed cusp limit, (R1)
then gives

```
FP integral E_u0² dmu = 2*Lambda(rho-1)*Lambda'(rho),
FP integral N_r dx dy
  = -rho*(rho-2)/2 * Lambda(rho-1)*Lambda'(rho).   (R2)
```

The second line follows from integration by parts with the original metric:
`integral |dE|_bilinear² = boundary(E partial_n E)-lambda integral E²`.
At `A(u0)=0`, that boundary product has no constant term. These are complex
bilinear expressions; no positivity is asserted. The squared-gradient integral
uses `dx dy`, since its inverse-metric factor cancels the hyperbolic volume.

The Maaß–Selberg formula in [Humphries, Proposition 2.1](https://arxiv.org/html/1705.05488)
provides an independent normalization check: after completing both Eisenstein
factors, the equal-parameter constant is `B A'-A B'`. It does not by itself prove
the repository's complete physical finite-part identification. That identification,
parameter-differentiated source admission, and a Lean proof of (R1)–(R2) remain
unfinished. No new Lean module is published for these paper calculations.

**Implication for the full chain.** A zero Weyl coefficient does not supply reader
annihilation. The positive survivor is the exact derivative boundary coefficient
which any such proof must retain. Even an identified value of this reader pairing
would still leave the complete quartic action: both quadratic responses, the
independent SS/SV/VV channels, changing metric weights, and the horizon, cusp,
characteristic and source-contact contributions. The next extinction attack must
evaluate their assembled pairing or derive its sign against
`K=-Sigma*|D|²`; neither a symmetric radial kernel nor (R1) supplies that sign.

The corpus searches used hybrid/deep retrieval with method and source-argument
views. The five saved requests covered snapshots of 57,285–57,286 files without
partial retrieval; most compiler entries were pending. The Maaß–Selberg query
returned no applicable closed theorem, and its proposed unrelated method hits
were not treated as proof ingredients. Broad recent-paper searches also examined
reciprocity (arXiv:2609.04169), H-duality (2609.03281), and wave-packet stability
(2607.21578). No identity from those papers was transferred to the HB action.

## Horizon-charge test: moving null cut and retained shear

**New comparison, 12 September 2026; source deformation audited in Lean.** The
[Wald–Wang boundary-condition paper](https://arxiv.org/pdf/2609.10805), submitted
9 September, gives zero asymptotic charges for its nonstandard gravitational
boundary conditions and modified symplectic structure. Its equation (226)
explicitly replaces the linearization-instability constraint in the black-hole
case by a horizon entropy variation. This does not establish HB extinction.
The original HB scalar boundary coefficient is already proved nonzero, and
neither a common mixed electric/magnetic Weyl boundary condition nor agreement
with the paper's modified action has been derived. Merely retaining the same
bulk Einstein equations would not identify the boundary action.

The positive test is to derive the horizon contribution from the original
fields. Write `s = u-3/2` or `-u-3/2`, `E=exp(s*(v+log 2))`,
`S=scalar u`, `V=*dS`, and keep independent amplitudes `aS,aV`.
The original ingoing reconstruction gives

```
h_vv = aS*E*s*(s-1)*S,
h_vA = -aV*E*s*V_A,
h_AB = -aS*E*(1+s*(s+1)/2)*S*gamma_AB.
```

Consequently the background cut `r=1` is not in general the perturbed null
surface. Its separated first displacement is `R=-s*aS*E*S/2`:
`2*R-h_vv-2*partial_v R=0`. This solves the linearized null equation at the
original background surface gravity `1`; it does not construct a global event
horizon or change the Hawking clock. The angular generator covector is
`X_A=-partial_A R-h_vA=s*E*(aS*dS_A/2+aV*V_A)`.

On this displaced cut, `delta gamma_AB=2*R*gamma_AB+h_AB`. Taking half its
Lie derivative along the displaced generator gives

```
K_AB = (s/2)*(2*R-aS*E*(1+s*(s+1)/2)*S)*gamma_AB
       + (nabla_A X_B+nabla_B X_A)/2.
```

The literal equation `Delta S=(s+1)*(s+2)*S` and actual `div V=0` force
`tr_gamma K=0`. They leave, rather than eliminate, the spin-two tensor

```
K = s*E*(aS*H/2+aV*JH),
H = Hess S-(Delta S/2)*gamma,
JH = sym nabla(*dS).
```

In the original upper-half-plane chart, if `H=[[A,B],[B,-A]]`, then
`JH=[[B,-A],[-A,-B]]`. Thus `H:JH=0` and `JH:JH=H:H`, with both indices
raised by the same original metric. For two independently polarized branches
of this same literal angular source the exact bilinear horizon expression is

```
K_p:K_m = s_p*s_m*E_p*E_m*(aS_p*aS_m/4+aV_p*aV_m)*(H:H).
```

This identifies the SS and VV contributions separately and the pointwise
vanishing of their mixed angular contraction. It is not positivity of a
complex bilinear expression. In particular an imposed complex polarization
can make its self-contraction zero without making the tensor zero; independent
polarizations cannot be specialized to that relation.

**Independent angular reader retained.** For a second literal angular parameter
`w`, the stronger pairing is

```
K_u(aS,aV):K_w(cS,cV) = s_u*s_w*E_u*E_w *
  ((aS*cS/4+aV*cV)*(H_u:H_w)
   +(aS*cV-aV*cS)/2*(H_u:JH_w)),
H_u:JH_w = 2*y^4*(A_u*B_w-B_u*A_w).
```

The latter determinant is antisymmetric in the angular fields. Its cancellation
for `w=u` does not license discarding it in a comparison with an independently
parameterized reader. This is a tensor identity for the original first-field
families, not identification of either family with the actual left-QNM reader
at an arbitrary radial frequency. The original metric weight `y^4` and the
connection terms in `A,B` are part of the theorem.

**Whole-chain consequence and next test.** A zero first expansion is compatible
with a live radiative shear. The nonlinear horizon identity must account for
this quadratic shear and the second-order displacement, including the actual
`++` and `+-` corrections; their zero angular entries on a fixed cut do not
prove zero moving-horizon area. At cubic action order, all further metric
weights and cross variations also remain. No identification with the actual
left-QNM projection, sign of its complete boundary sum, or extinction is yet
proved. The source-derived shear is a candidate quantity in that missing
identification, not a replacement definition of the complete cokernel.

**Nonlinear continuation to test, not an assumed premise.** Expanding the null
Raychaudhuri identity in the original nonaffine time with background surface
gravity `1`, write
`g=g0+a*p+b*m+a²*k_pp+ab*k_pm+b²*k_mm+...`. If this is an actual null
congruence of the corrected metric, its degree-two identities, using the
first-order zero expansion derived above, are

```
(partial_v-1) Theta_pp = -K_p:K_p - E_pp(l0,l0),
(partial_v-1) Theta_pm = -2*K_p:K_m - E_pm(l0,l0),
E_pp = L(k_pp)+B(p,p)/2,   E_pm = L(k_pm)+B(p,m).
```

Here `E` denotes the original cosmological Einstein residual, and all graph,
generator and inverse-metric variations belong in `Theta`. The cosmological
term drops out by the null equation, and variations of the nonaffinity multiply
the zero first expansion. Thus this coefficient comparison does not require a
frequency adjustment. A full quadratic solution removes `E_pp,E_pm`, leaving
the shear forcing, not zero expansion. These are paper consequences of the
nonlinear geometric identity; neither that identity nor the complete corrected
null congruence has been formalized by the new first-order result. If the first
field itself is switched, its derivative contacts must be included before using
zero first expansion.

The June [second-order entropy paper](https://arxiv.org/html/2606.16757v1),
equations (72)–(80), supplies a primary-source check of the shear/expansion
normalizations in affine gauge. The July
[Einstein–Maxwell extension](https://arxiv.org/html/2607.12794v1), equations
(11)–(20), retains equations-of-motion contributions and time-cap terms in
canonical energy. Its area derivation discards angular divergences on compact
cross-sections; HB requires actual cusp traces instead. No sign or coefficient
from either paper's modified global energy is imported into the HB left action.

This comparison also distinguishes the orders in the proof chain. The new
`K_p:K_m` is the quadratic contraction of the original first fields. The complete
Peierls target acts on their *quadratic sources and causal responses* and is
quartic in first-field amplitudes. Identifying these two objects would be an
order error. The second corrected shear, its constraint contributions, the
moving weights and all boundary terms must be derived before testing that
quartic physical quantity. The independently proved physical-reader transport
remainder also remains. A local horizon identity valid for every complex `u`
does not by itself select the Xi divisor or its critical line.

The first four new deep/hybrid searches covered 57,272–57,276 inventoried files
and all retrieval views, including method/source arguments, with no unfinished stages.
Most compiler metadata remained pending; candidates were checked against source.
The returned cosmological `cyclicRaychaudhuri` is an algebraic model, not a null
congruence theorem, so it cannot discharge this geometric identity. The new
BV-AKSZ paper's displayed presymplectic equations explicitly omit boundary terms;
they also cannot close the HB boundary sum. A subsequent rotated-Hessian-current
search covered 57,281 files and returned partial results after its decomposition
worker disconnected; those results are not a completed method search.

**Formal status.**
`ThetaCuspHawkingBMOriginalHorizonDeformation.lean` proves the complete original
ingoing metric identification, its actual one-sided horizon limit, the separated
first null equation, the angular generator obtained from that metric, zero trace
of the first cut deformation, and both same-source and independent-parameter
bilinear pairings above. It contains no supplied field-equation or covariance
premise; the upper-half-plane and exterior subtypes specify physical domains.
It does not formalize a global event horizon or the nonlinear Raychaudhuri/
entropy/Peierls identifications described as remaining work above.

Validation: `lake env lean /tmp/hb-moving-horizon.lean` passed without diagnostics.
The final isolated, cached
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalHorizonDeformation`
built only that leaf and passed (191 seconds). Audited source SHA256:
`ad718e39cd4ed42e6911102e14107a8151fc4829dc4e7fa930fc3186ffff636e`.
The finished module is wired into `RHTower.lean`; no umbrella was built.
Formal lint passed with existing large-file warnings. No heartbeat or recursion
limits were raised, and no computational or axiom-printing checks were used.

## Whole-chain comparison: variational elimination, angular rigidity, reader transport

The shared obstruction remains theta → Xi occurrence → retained spin-two source →
physical causal/left-QNM action → fixed-clock extinction → RH. The following tests
compare different possible mechanisms at that obstruction. None supplies extinction.

**Variational elimination test.** For a symmetric action expansion
`I(x)=L(x,x)/2+T(x,x,x)/6+U(x,x,x,x)/24`, substitute
`x=e p+d m+e² a+ed b+d² c`, with the linear fields in the kernel of `L`.
The exact `e²d²` coefficient is

```
L(a,c)+L(b,b)/2+T(p,p,c)/2+T(p,m,b)+T(m,m,a)/2+U(p,p,m,m)/4.
```

If the quadratic equations are stationary equations on this SAME variational
domain, substituting `L(a,z)=-T(p,p,z)/2`, `L(b,z)=-T(p,m,z)` and
`L(c,z)=-T(m,m,z)/2` reduces it to
`-L(a,c)-L(b,b)/2+U(p,p,m,m)/4`. This follows by multilinear expansion;
it is a paper comparison, not a source-level premise-free theorem. For a causal
domain, the equalities used in this substitution acquire boundary variations.
In particular, symmetry of an effective action must not identify a retarded
inverse with its transpose. The expected transpose is advanced, subject to
proof of the actual domain and all boundary terms. The existing abstract cubic
Peierls polarization already describes what survives that exchange; repeating
it as a conditional theorem would not advance the source proof.

The physical source files checked here prove finite radial transport and
absolute endpoint admission, with actual endpoint currents retained
(`BMPhysicalResponseGreenTransport`, `BMPhysicalGreenSourceAdmission`).
They do not assert a complete Einstein retarded/advanced transpose identity.
`BMMixedActionCubicCoefficient` retains the changing weights multiplying BOTH
full quadratic residuals. The particular angular correction in
`BMQuadraticIngoingCorrection.correctedAngularCoefficient_eq` still leaves
`B²(aV² vectorWeight-aS² scalarWeight) gradientPair`. Its own declaration
explicitly excludes a solution of all components. Thus the complete solved
`++`/`+-` equations needed by this elimination have not been obtained from those
constructors. The current frontier also retains their global assembly as open.

**Angular rigidity test.** Absence of a holomorphic cusp-form sector would only
help after identifying the retained tensor with that sector. For the original
hyperbolic metric `h=y^-2(dx²+dy²)`, direct coordinate differentiation gives

```
div_h(TF Hess_h S) = d(Delta_h S)/2-dS.
```

For an eigenfield `Delta_h S=lambda S`, this is `(lambda-2)dS/2`.
Trace-free therefore does not imply transverse. No holomorphic/transverse
identification of the complete tensor source has been proved. The existing
positive survivor is stronger than merely rejecting that shortcut:
`BMEisensteinActualBalancedSpinTwoCoefficientExtraction` retains the exact
balanced period and two actual cusp currents. Its closed finite-cutoff identity
must remain in any scalar reduction. No new Lean claim is made for the displayed
divergence calculation here.

**Reader-transport test.** The actual
radial mode equation in `BMPhysicalRadialModeMatching` is

```
L_u(w) f := f''-w² f+(u²-1/4) sech²(t) f = 0,
u=(rho-1)/2,       u_ref=-u-1/2.
```

Keep `w` unchanged. Put `lambda=u²-1/4`, `mu=v²-1/4`, `delta=mu-lambda`,
and `D=partial_t+A(t)`. Product differentiation, with all derivative terms
retained, gives

```
(L_v D-D L_u) f
 = [2 A'+delta sech²(t)] f'
   +[A''+delta sech²(t) A+2 lambda sech²(t) tanh(t)] f.       (D1)
```

Cancelling the `f'` coefficient requires `A=-(delta/2)tanh(t)+c` on the
connected radial interior. The remaining coefficient is

```
sech²(t) * [delta*c + (2 lambda+delta-delta²/2)tanh(t)].     (D2)
```

For distinct potentials, a monic first-order intertwiner therefore requires
`c=0` and `delta²-2delta-4lambda=0`. Equivalently
`v²=(u+1)²` or `v²=(u-1)²`. This is the positive classification exposed by
the attempted repair: the first-order ladder moves the parameter by a unit.
It does not implement the physical reflected reader's half-shift.

For that half-shift, `delta=u+1/4` and the uniquely derivative-cancelling,
zero-constant candidate is `D_*=partial_t-(u/2+1/8)tanh(t)`. Its exact law is

```
L_u_ref(w) (D_* f)
 = D_* (L_u(w) f)
   +(3/32)(2rho-3)(2rho+1) sech²(t)tanh(t) f.               (D3)
```

Both scalar factors are nonzero at every Xi occurrence, by the independently
proved open critical strip. This calculation concerns the actual radial reader
operator, and the physical clock `w` never changes. On a forced field, `D_* F`
must be retained in addition to the displayed new forcing. On a homogeneous
left mode, the last term remains. Forcing and endpoint traces therefore have
to be transported together; a homogeneous ladder identity cannot be inserted
in their place. The two original modes cannot both vanish at an interior point,
by their nonzero original Wronskian. These statements are being checked against
the original mode functions, rather than replacing them by arbitrary jets.

The same defect reaches the actual complete projected physical response. Let
`Phi` be `physicalCuspProfile(source, reflected reader)` in its original overlap
band, and let `F_ref` be its unchanged `continuedAngularSourceProjection`. The
proved response convention is `L_u_ref Phi=-F_ref`. With `A=D_* f`, define
`J=A' Phi-A Phi'`. Equations (D3) and the actual forced response equation give

```
J' = A F_ref + (3/32)(2rho-3)(2rho+1) sech²(t)tanh(t) f Phi. (D4)
```

Indeed, the two potential terms cancel in `A'' Phi-A Phi''`; these are the
two remaining terms, with the signs displayed. On every finite negative radial
interval, integrating (D4) gives `J(t)-J(s)` with BOTH original endpoint values.
All four source-projection channels remain in `F_ref`. This is not the full
independent SS/SV/VV Einstein action, and it sets no horizon, outer, cusp,
characteristic or source-contact limit to zero. It provides an explicit response
interface error for this proposed reader transport. Its coefficient also survives
on the critical line, so it must not be identified with the clock-defect energy,
which vanishes there. A further cancellation would have to be proved from the
complete source and boundary assembly.

This obstructs a specific local repair of the reader-reflection step. It does
not rule out a nonlocal or higher-order transport, identify the complete action,
or imply failure of HB. A successful alternative must still transport the
angular test, full corrected source, source contacts and physical boundary data.

**Recent external methods checked.**
[Electrovacuum Black Hole Uniqueness](https://arxiv.org/html/2609.11140v1)
(10 September 2026) obtains rigidity from a nonlinear differential inequality
with a positive square and controlled axis/horizon asymptotics in a stationary,
axisymmetric, asymptotically flat Einstein–Maxwell reduction. HB has no proved
identification with that real harmonic-map system. The useful target suggested
by the method is a source-derived scalar inequality retaining a positive
complete term and every limiting face, not assumed stationarity.
[A proof of Hodge universality conjecture at nonzero dispersion](https://arxiv.org/html/2609.11469v1)
classifies specified tau-symmetric Hamiltonian deformations by their diagonal
coefficients. The Hamiltonian/tau-symmetry identification needed to import that
rigidity is absent here.
[A closed signature formula for the Katz–Long–Moody Hermitian form](https://arxiv.org/html/2609.11793v1)
controls quotient signature from unitary input and resonant kernels; that input
is not established for the source's physical clock.
[Theoretical Aspects of Direct Waves in Kerr Black Holes](https://arxiv.org/html/2609.11908v1)
(10 September 2026), Appendix B, retains the screening factor in the complete
source/Green convolution when changing variables. Its linear Kerr calculation
does not establish nonlinear theta extinction. It reinforces the need to
transport source factors with response factors; moving a zero between them
does not evaluate the full observable.

Search records: whole-corpus deep and hybrid requests with all retrieval views,
plus lexical Darboux discovery, are retained in `formal/.lake/hb-extinction-scratch`.
The quartic-elimination request was partial; the subsequent causal-quartic and
tensor/holomorphic deep requests completed. Snapshot coverage was 57,265 files
for the reader search, with predominantly source-only compiler status. Generated
method suggestions and retrieved statements were inspected, not accepted as
proofs or claimed exhaustive semantic coverage.

**Formal status of this comparison.**
`ThetaCuspHawkingBMPhysicalReaderDarboux.lean` passes
`lake env lean /tmp/hb-reader-darboux.lean` with no diagnostics. It proves six
public theorems: `reflectedResidual_eq`, `defectCoefficient_ne_zero`,
`reflectedResidual_wronskian`, `reflectedResidual_pair_ne_zero`,
`transportCurrent_hasDerivAt`, and `transportWork_integral`. These use actual
mode functions and derivatives, the original Gamma Wronskian, and the original
complete projected physical response. Frequency-band and negative-radius
subtypes encode their proved domains. No additional covariance, extinction,
flux-vanishing or physical-incidence assumption is supplied.

The formal no-go is the nonvanishing pair of residuals for the explicitly
constructed `D_*`; its positive survivor is (D3), the exact Wronskian detection,
and the source/response balance (D4) including both finite endpoint values.
The classification of **all** monic first-order intertwiners in (D1)–(D2)
remains a paper argument; the Lean result must not be described as that broader
classification. Neither the symmetric variational elimination interface nor
the full nonlinear cancellation has been formalized as an unconditional HB
result. The next action-level comparison must retain the complete correction
residuals and boundary variations; this radial result does not justify dropping
them or retiring the route.

The 240-line leaf sets only `autoImplicit false`, uses no heartbeat/depth/
transparency setting, and is wired after `BMPhysicalResponseGreenTransport`.
Source SHA256: `341292fd1fc9d09b558c1e4bdc5c288b543dc2660dad973b65527c438252ae21`.
The exact cached isolated audit
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalReaderDarboux`
passed (10 seconds reported for the leaf), with no warnings. Its artifacts were
published after the source-hash check and its isolated directory removed.
Repository formal lint and scoped whitespace checks passed. No full or umbrella
build was run. All owned Lean and research processes from this attack finished.

## Source-contact conservation and the physical left test

**Whole chain:** literal theta → Xi occurrence → retained tensor source → physical
causal/left-QNM action → original fixed-clock extinction → RH. The question tested here
is whether conservation of the switched mixed source removes its onset work. It does
not remove that work by itself. The positive result is an exact characterization of the
contact's coupling to the actual left-mode field. This is a quadratic scalar/vector
source calculation, not a theorem about the complete cubic independent-channel source.

Write `f=r²-1`, `v=t+r_*`, and let `C_A` be the original `orbitCurrent`, with the full
theta-square and gradient-source covectors retained. The existing constructor is

```
S_tA = f C_A,r/r²,             S_rA = C_A,t/(r² f),
Sχ = S[χ C] = χ S + N,
N_tA = χ'(v) C_A/r²,           N_rA = χ'(v) C_A/(r² f).
```

Both symmetric partners are included; other components vanish. Here `χ` is the
original `Real.smoothTransition`, independent of the Xi occurrence. The tensor
decomposition itself was already formalized in `BMMixedCurrentCutoff` and is not a
new result of this attack.

**Conservation calculation (paper proof; covariant-divergence identification not yet
formalized).** For a mixed symmetric tensor with entries `T_A,R_A`, direct contraction
with the original metric and Christoffels gives

```
(div_g S)_A = -∂t T_A/f + f ∂r R_A + (f' + 2f/r) R_A,
(div_g S)_t = (y²/r²)(∂x T_x + ∂y T_y),
(div_g S)_r = (y²/r²)(∂x R_x + ∂y R_y).
```

The angular-index equation vanishes for the displayed current curl by equality of
mixed derivatives. The other two equations vanish because the actual square covector
is `*d(S_theta²/2)` and the gradient covector is `*d(fullGradientEnergy)/2`. All orbit
coefficients and the onset are angular constants. Smoothness and these angular
identifications are available in the source corpus; the orbit smoothness theorem alone
holds the angular point fixed and must not be misused as full spacetime smoothness.
Applying the same calculation to the existing onset tensor gives exactly

```
(div_g (χ S))_A = -χ'/r² (∂r C_A - ∂t C_A/f),
(div_g N)_A    =  χ'/r² (∂r C_A - ∂t C_A/f).
```

The two `χ''` terms cancel. Thus the contact repairs the constraint; it is not an
optional term that conservation permits one to discard.

**Original action pairing.** Define `P(M,T)=(r²/y²)(g0⁻¹ M g0⁻T):T`, with all sixteen
entries and both inverse metrics. For a symmetric test, direct contraction gives

```
P(M,N) = (2χ'/r²) Σ_A C_A (M_rA - M_tA/f).
```

For an arbitrary test, replace each `2 M_iA` by `M_iA+M_Ai`. In particular,
`P(N,N)=0`, while for the original stream reconstruction
`M_tA=f ∂r Ψ_A`, `M_rA=∂t Ψ_A/f`,

```
P(M[Ψ],N) = -(2χ'/r²) Σ_A C_A ∂r|v Ψ_A.                 (N)
```

This is null self-pairing with a retained physical test coupling, not a proof that
the coupling is nonzero for every occurrence. It rules out deleting the contact
merely because its self-pairing vanishes. The left-mode field in (N) is the original
`physicalLeftModeStream`, with actual coordinate derivatives and an independent reader.
The first-jet reconstruction is sufficient for this pairing; its artificial second
jet must not be used to claim an Einstein equation for the test.

**Second pass: does the bulk cancel (N)?** Put `Cχ=χ C` and use the original
`streamAngularAction=A` and `streamMasterValue=R`. Product differentiation gives

```
P(M[Ψ],Sχ) = ∂t [2 Σ_A Cχ_A ∂t Ψ_A/(r² f)]
            -∂r [2f Σ_A Cχ_A ∂r Ψ_A/r²]
            +(2/r⁴) Σ_A Cχ_A (R Ψ_A-A Ψ_A).             (G)
```

For an admitted homogeneous physical left mode, `R Ψ=0` and
`A Ψ=(physicalAngularParameter(reader)²-9/4) Ψ`. The `-2` curvature shift
between `streamAngularAction` and `angularJetOperator` is essential; the same
`lambda-2` factor occurs in `physicalProjectedModeAction_value`. The last term in (G) therefore
survives as an actual source/left-mode overlap. Conservation has not made the physical
projection a pure boundary term. Transferring `A` to the source introduces its angular
Green flux, which must be retained on the truncated cusp boundary. Integrating the
first two terms retains both temporal caps and radial faces; rewriting in ingoing
coordinates retains characteristic faces. No exhaustion or endpoint limit is set to
zero here. Equation (G) is presently a paper identity, not a new Lean theorem.

There is also a domain trap: `physicalLeftModeStream_jet` is evaluated at static time
zero and negative tortoise coordinate. At that spacetime point the causal onset is
zero. That local evaluation cannot be used to erase a time-integrated contact; a time
transform requires its actual onset transform or the field at general static time.

**Consequence for the complete assembly.** The nonlinear Bianchi hierarchy contains
`Div0 E3 + Div1 E2 + Div2 E1=0` at cubic order. Only actual vanishing of the complete
lower-order tensor residuals removes the last two terms. Even after that removal,
conservation supplies gauge-test identities; (G) exposes the extra overlap for the
physical stream test. Independent SS/SV/VV corrections, changing weights, spin-two
retention, and all boundary contributions still have to enter one common tested action.
This failure does not retire HB or show that those terms cannot cancel. It identifies
what such a cancellation must include, without changing the common Hawking clock.

**Alternative mechanism checked against the whole chain.** The source corpus already
proves the exact rank-three Casimir multiplier

```
K(P,Q)=Q²(Q-1)²/16 * [(2P-1)²-Q²] * [(2P-1)²-(Q-1)²]
```

which converts the literal repeated-leg scalar unfolding into its four-Xi normalization
on the strict unfolding chamber. That theorem multiplies the scalar period by `K`; it
does not derive `K` from the complete corrected Einstein action. A candidate worth
checking is whether the operator retained in (G), together with the independent SS/VV
terms and correction/contact contributions, produces that exact multiplier. Counting
three source channels is not a proof of its rank-three realization. Nor does the
strict-chamber normalization alone admit continuation at the required Xi occurrences.
This comparison, and the direct physical flux/sign route, both remain open.

Research: the first source-conservation deep request returned partial results over the
57,260-file snapshot; the subsequent conserved-source/physical-pairing request completed,
but supplied no extinction mechanism. Method hits were mostly unrelated gauges or
rewrites, not source-level cancellations. Broad recent arXiv retrieval found
[Quantifying Symmetry Breaking](https://arxiv.org/abs/2609.11926v1) (10 September 2026):
its abstract concerns finite-dimensional quantum states, compact Lie symmetries, and
i.i.d. asymptotic conversion. Those are not supplied by the HB source. Full HTML retrieval
failed its size limit; no theorem from that paper is claimed to apply. A separate broad
reciprocity API request was rate-limited; it supplied no usable paper.

**Closed formal result:**
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCurrentSourceAction.lean`, namespace
`RHTower.D4BMCurrentSourceAction`, proves `onset_action`, `onset_self_action`,
`onset_stream_action`, `physical_left_onset_action`, and `physical_left_switched_action`.
All public statements have no additional logical hypotheses. They retain the original
all-entry contact pairing, its null self-pairing, actual physical left-field derivatives,
and the original literal source in the switched-source decomposition. They do not prove
nonzero left coupling, full source conservation, complete nonlinear cancellation,
extinction, or RH.

Validation: `lake env lean /tmp/hb-onset-action.lean` passed with no diagnostics.
The exact cached isolated audit
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCurrentSourceAction` passed
(56 seconds reported for the leaf), without warnings. Source SHA256:
`cf60006daccdd1a8a217aec6bc8f826639c623e83a5e8ca909ddc32462185979`.
Only `autoImplicit false` is set; no heartbeat/depth/transparency changes. Artifacts
were published and the isolated audit directory removed. The leaf is wired after
`BMPhysicalModeAction` in `RHTower`; no full or umbrella build was run. API indexing
and repository formal lint passed; scoped whitespace checks passed. Serena symbol
lookup rejects this ignored Lean path, so source inspection used `rg` and file reads.

## Complete-action cyclicity attack: changing metric weights

The current attack tests cyclicity of the original weighted Einstein source, rather than
assuming cyclicity from symmetry of its second derivative. At a symmetric nondegenerate
metric `G`, put `W(M)=G^{-1} M G^{-T}` and `tau(H)=tr(G^{-1}H)`. Direct differentiation of
the existing determinant-normalized testing weight gives the Lean-proved exact identity

```
W'_H(M)-W'_M(H) = [tau(H) W(M)-tau(M) W(H)]/2.
```

The two index-raising derivatives cancel in this exchange; the volume derivative remains.
For the full scalar/vector fields this must be checked without identifying their amplitudes.
Its contraction with the quadratic residual is an additional term in the attempted cyclic
Einstein-source pairing. The existing complete `++-` coefficient has TWO such changing-weight
terms, multiplying the `++` and `+-` tensor residuals respectively. Only their actual solved
equations eliminate them. Boundary-current differentiation remains separate and must retain
horizon, cusp, characteristic and source-contact faces. This identity is proved in
Lean; it is not an extinction law or a proved sign for the complete physical action.

**Closed formal result:**
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMActionWeightExchange.lean`, namespace
`RHTower.D4BMActionWeightExchange`, proves seven public theorems with no additional logical
premises. `literal_corrected_weight_exchange` identifies the actual first testing-weight
derivative on both cubic metric paths, allowing arbitrary quadratic/cubic correction matrices.
`literal_weight_residual_exchange` contracts the exchange with every entry of an arbitrary
tensor residual. `literal_vector_trace` and `literal_trace_scalar` prove that the trace depends
only on the independently retained scalar amplitude. Vector/vector weight exchange is therefore
exactly symmetric; testing a full field against a vector leaves its scalar-trace contribution.
These statements do not claim that the correction matrices solve their forced equations or
that the boundary current vanishes.

Validation: final `/tmp/hb-action-weight-exchange.lean` scratch check passed; exact cached
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMActionWeightExchange` passed in
156 seconds without warnings. Source SHA256:
`23f3e93ef47831f4621702ecfc08bf222b75ec6e6ecc8858b8132c0746d792cd`.
Only `autoImplicit false` is set; no heartbeat, depth or transparency increases. The audited
leaf artifacts are published, the leaf is wired into `RHTower`, and the isolated audit directory
was removed. No full or umbrella build was run.
API indexing refreshed one source file. Repository formal lint passed (150 existing
large-file warnings); scoped whitespace checks passed. No matching Lean/Lake process remains.

Parallel mathematical tests in this attack: an exact Kerr--Schild completion would need to
contain the literal scalar/vector metric and preserve its causal data; no such identification
was found. The existing literal triple-Eisenstein normalization audit already rejects replacing
the meromorphic scalar period by the canonical four-Xi vertex. Neither failure rules out the
complete corrected action. Their positive implication is to keep the tensor source, original
normalization, and boundary remainder in the physical comparison.

**Whole-chain consequence, including a positive second pass.** The local weight exchange is
not by itself a no-go for the Peierls mechanism. Write `L` for the original linearized
cosmological Einstein operator and `B` for its second variation. The formal variational
calculus, with a single fixed reference volume density, gives the following target for the
actual fields:

```
<M,B(H,K)> - <H,B(M,K)>
  + [tau(H)<M,LK> - tau(M)<H,LK>]/2
  + W'_K(M):LH - W'_K(H):LM
 = Div (D_K omega(H,M)),

omega(H,M) = D_H theta(M) - D_M theta(H).
```

Here `<M,R>=W(M):R`, and `theta` is the original volume-weighted Einstein boundary
current, not an assigned bilinear form. Derivation: differentiate
`D_M action = -weightedSource(M) + Div theta(M)` twice, exchange the `H` and `M`
directions in the third action derivative, retain both derivatives of the testing weight,
then apply the exact exchange law above. The background vacuum removes the term containing
the second weight derivative. This higher-variation/boundary identity has **not** yet been
formalized or globally admitted; the existing first-variation theorem and the new weight
identity supply parts of it. No integrated boundary term is declared zero.

Crucially, for a genuine causal difference `K = Kret - Kadv` with the **same complete
tensor forcing** on both sides, `LK=0`. If `H` and `M` are the actual homogeneous seed and
left mode, the other two residual terms also vanish. Thus the bulk changing-weight obstacle
disappears in the causal difference even when scalar traces are nonzero. The surviving
problem is the physical differentiated boundary current, together with proof that the two
responses share all source-contact distributions. This is stronger than requiring every
individual scalar/vector pairing to be cyclic. It also explains why the already-defined
canonical choice of advanced map zero cannot establish the physical common-source equation.

The corpus proves this common-forcing subtraction for the **principal transformed response
versus its endpoint Green correction** (`principalGreenDefect_hasDerivAt`); it is a uniqueness
comparison of two representations of one response, not construction of the advanced solution.
The horizon-monodromy no-go proves that rescaling one normalized Green solution line does not
construct a different causal propagator. Neither statement supplies the missing complete
retarded/advanced tensor incidence. The extinction interface remains the complete sign (or
reflected-sum sign) recorded below, followed by `K=-Sigma*|D|^2`, `Sigma>0`.

**Research coverage and cross-field tests.** Cached hybrid/deep/method searches covered an
inventory of 57,247--57,250 source files; compiler applicability was largely source-only,
and semantic coverage was not measured. The triple-period and third-derivative searches
reported partial results, which were used without claiming exhaustive discovery. Recent
primary sources inspected include Aliev's June 2026
[Kerr--Schild--AdS subclass result](https://arxiv.org/html/2606.02929v1) and Hegde's August 2026
[residual-spectrum construction](https://arxiv.org/html/2608.19129v1). Aliev's decisive
off-diagonal constraint is proportional to the added quadratic-curvature coupling and does
not supply the HB Einstein equation. Hegde derives cancellation of obstructing constant-term
coefficients through an actual equivariant Euler-class construction at prescribed nilpotent
markings; an HB source/current realization of that geometry is absent. The transferable
research question is whether the actual assembled boundary terms have such a source-derived
cancellation representation, not whether an abstract vanishing theorem can be assumed.

## Reflection, conjugation, and the positive-current test

### Whole-chain recheck: cyclicity, clock work, and causal onset

The current corpus contains a stronger local result than the preceding weight calculation
alone: `D4BMCyclicAction.physical_cubicAction_cyclic` and
`D4BMOnShellCyclicSource.physical_quadratic_cyclicity_defect`. For three independent
literal physical modes, including independent scalar/vector amplitudes, the original
quadratic Einstein pairing has exactly half the differentiated boundary-divergence
defect. `physical_bulk_second_eq_hessian` discharges the moving-weight terms using
the actual vacuum and linearized equations. These are existing results, not new work
claimed here. They do not apply the on-shell reduction to a forced quadratic response:
that response has a nonzero linear Einstein source. The explicit trace-wedge expansion
above and the spatial/current admission of its differentiated boundary remain distinct
from this already-proved parameter-derivative identity.

**Conjecture tested:** fixed-clock Noether conservation, combined with the solved
quadratic equations, directly annihilates the complete cubic left-QNM projection.
The geometric calculation instead gives the following precise boundary-work identity.
It is a paper calculation, not a new Lean theorem or a completed physical interface.

Let `g(epsilon)=g0+epsilon*h+epsilon^2*k+epsilon^3*l+...` denote the *actual metric*,
and `E(g)=Einstein(g)-3g`. Fix the original physical time coordinate `x^0` and a single
local coordinate-volume branch `v(g)`. In the BM chart this is the original density
`v0=r^2/y^2` times the determinant ratio used by the action. The factor `v0` must
remain when taking spatial derivatives; the determinant ratio alone is insufficient. Set

```
P^{ab}(epsilon) = v(g) g^{ai} E(g)_{ij} g^{jb},
J^a(epsilon)    = v(g) g^{ab} E(g)_{b0}.

partial_a J^a = (1/2) P^{ab} partial_0 g_{ab}.              (W)
```

Proof of the geometric identity: contract differential Bianchi to obtain
`nabla_a E^a_b=0`, using metric compatibility and the curvature symmetries. Expand
the covariant derivative at `b=0` and use `partial_a v=v Gamma^c_ca`. This leaves
`v Gamma^c_a0 E^a_c`. Substitution of the Christoffel formula and symmetry of the
raised Einstein tensor cancels its two spatial-derivative terms, leaving the right
side of (W). This is the coordinate-time generator; it has not been changed to a
source-dependent frequency or to the shifted angular reader.

Write `P_j,J_j` for ordinary Taylor coefficients, without factorial multipliers.
Since the original BM background is stationary and vacuum, coefficient four gives

```
2 partial_a J_4^a
 = P_3 : partial_0 h + P_2 : partial_0 k + P_1 : partial_0 l. (W4)
```

If the *actual first field* is the uncut literal physical mode, its first Einstein
residual vanishes. Then `P_1=0`, and the original corrected-source formulas give

```
E_2 = L k + B(h,h)/2,
E_3 = L l + B(h,k) + C(h,h,h)/6,
P_2 = W_0 E_2,
P_3 = W_0 E_3 + W_1(h) E_2.
```

Here `W_0 E=v0*g0^{-1} E g0^{-1}` and `W_1` includes that same fixed factor `v0`
times the original varying-volume/index derivative.

Thus (W4) retains BOTH the varying-index/volume work and the derivative of the
quadratic correction. Only complete tensor equations `E_2=0` remove them. If a
clock cutoff is instead imposed on the first field, its derivative contacts enter
`P_1`, so the final term in (W4) must also be retained. No term is declared zero
because a scalar reduced response equation has been solved.

For independent plus/minus amplitude variables, write the degree-two field as
`z_+^2 k_pp + z_+ z_- k_pm + z_-^2 k_mm`. The exact `z_+^2 z_-^2` coefficient of
the first-field-on-shell version of (W4) is

```
2 div J_22 = P_21 : partial_0 h_minus + P_12 : partial_0 h_plus
           + P_20 : partial_0 k_mm + P_11 : partial_0 k_pm
           + P_02 : partial_0 k_pp.                         (W22)
```

All quantities are full tensors. This retains SS, SV, VV and spin-two components
without assigning equal scalar/vector amplitudes. When the complete quadratic
grades vanish, the clock identity controls a sum of the two oriented cubic
pairings. It does not isolate a single radiative grade. A reflected-sum interface
can still be sufficient because both reduced complete cokernels are nonpositive,
but its identification with (W22) is a separate producer obligation.

On any finite exterior region, integrating (W4) or (W22) gives every oriented
boundary integral of `J_4` or `J_22`: two time caps, inner radial face, outer radial
face, angular/cusp faces, and any characteristic faces used to split the region.
Internal faces cancel only when they are traces of the same current with opposite
orientations. Source contacts remain in the volume work or in their corresponding
interface distributions. Horizon and cusp exhaustion require admitted limits;
formal cancellation of two incidence signs does not supply those limits.

**Outcome and positive survivor.** Noether conservation supplies a quartic
boundary-charge balance for cubic source work. It does not give zero boundary
charge. Moreover, the clock test `partial_0 h` has the original source angular
field, whereas the actual projected left-QNM reader has parameter
`physicalAngularParameter`. Their identification cannot be inferred from time
translation: the existing physical-reader half-shift calculation explicitly
distinguishes the two source/reader transports. The remaining target is an actual
source-derived representation of the desired left pairing by the work in (W22),
together with zero or the required sign for its *complete* boundary value. This
test has not disproved such a representation; it has located the two facts it
would have to prove.

A further positivity test also has a precise obstruction. The two original rates
are `s_plus=rho-2` and `s_minus=-rho-1`, so
`s_minus-conj(s_plus)=1-2*Re(rho)`. Treating those two time-dependent fields as a
Hermitian pair would already impose the desired wall. Pairing a field with its
actual conjugate instead is legitimate, but changes the second Xi label and the
observable whose physical incidence must be proved. Thus positivity of a real
gravitational energy cannot simply be assigned to the bilinear pair in (W22).

**Onset compatibility must be checked before using on-shell cyclicity.** The
constructed causal response solves the original *switched* source, including the
explicit pulse in `fullSourceOnset_wave_identity`. At the level of complete
tensor equations, if an uncut first field is retained and a correction solves
`Lk=-chi*B(h,h)/2`, then its unswitched Einstein residual is exactly
`E_2=(1-chi)*B(h,h)/2`. Any extra specified contact forcing contributes its own
term. This algebra is not a claim that the full constructed tensor correction
has already been identified with that simplified equation. It explains why
the causal transform theorem alone cannot discharge `E_2=0` in the weighted
cubic action during the onset. The full source-to-corrected-metric comparison
must establish which residual and contacts occur there.

**Research and formal status.** New cached deep searches covered inventories of
57,256--57,260 files, including installed dependencies and method/source arguments.
The theta-bilinear, square-eigenclosure and Taub searches reported partial results;
semantic coverage is not certified and most declarations remain source-only in
the index. No theta bilinear law closing the Einstein evolution was found.
Broad recent arXiv searches included causality, transgression, reciprocity,
bilinear and Taub. The August 2026
[ordinary-corner descent paper](https://arxiv.org/html/2608.02928v1) supplies signed
codimension-two cancellation under its formal mapping-space hypothesis, not an HB
gravitational boundary realization. The August
[Goldstone thermal-transgression paper](https://arxiv.org/html/2608.09776v2) retains
a separately specified thermal state and dynamical KMS condition; those cannot be
imported as a source proof of fixed-clock invariance. The September
[nonlinear inverse-source paper](https://arxiv.org/html/2609.09845v1) uses the full
boundary derivative at one common real small state, not one complex left-QNM
measurement. Its symmetric coupled linearization suggests checking the complete
boundary response, but supplies neither its HB identification nor a vanishing law.
The September [temporal-localisation paper](https://arxiv.org/html/2609.11577v1)
proves growth followed by decrease across a change of topological phase; that is
not exact extinction at the original fixed clock.

No Lean source was added or rebuilt in this recheck. The contracted/densitized
Bianchi identity (W), its actual corrected-field specialization, finite-domain
admission and left-QNM identification are not claimed kernel-checked here. The
existing uncontracted literal Bianchi and parameter-cyclicity leaves supply parts
of the derivation. Physical extinction and RH remain open.

The actual local action identity `D4BMActionBoundary.literal_action_boundary_near_zero`
and literal differential Bianchi identity hold for arbitrary complex source parameters.
They retain the boundary divergence; they do not select Xi occurrences. The fixed-domain
translation test therefore still requires the completed boundary pairing, as recorded in
`hb-fixed-clock-source-translation.md`.

A second test uses the physical reader itself. Write `rho=x+i t`,
`nu=(rho-1)/2`, `mu=nu^2-1/4`, and
`psi=scalar nu`. All quantities here are the existing literal full Eisenstein field,
including its Fourier tail. Let `S rho=1-conj rho`.

**Conjecture tested:** reflection and conjugation turn the reader's Green identity into
a nonnegative norm with coefficient proportional to `x-1/2`.

The exact coefficients distinguish two different identities:

```
mu(rho)-mu(S rho) = (x-1/2) * (i t-1/2),
mu(rho)-conj(mu(S rho)) = (1-2 rho)/4,
mu(rho)-conj(mu(rho)) = i (x-1) t.
```

The first coefficient multiplies the **bilinear** product `psi(rho)*psi(S rho)`.
Adding conjugation to the second reader changes the spectral coefficient to the second
line. Pairing the reader with its own conjugate gives the positive density `|psi|^2`,
but its coefficient is the third line, nonzero at every Xi occurrence since
`0<x<1` and `t!=0`. In particular it does not vanish on the critical line.
Thus these Green identities do not furnish the proposed positive clock-defect identity.
This rejects that specific substitution, not extinction of the complete nonlinear action.

**Positive survivor, formalized.** With original chart coordinates and original
hyperbolic Laplacian, define

```
J_j = conj(psi) * partial_j psi - psi * partial_j conj(psi).
y^2 * (partial_0 J_0 + partial_1 J_1)
    = i (x-1) t * |psi|^2.
```

Proof: expand both product derivatives; the first-derivative products cancel.
Use the full literal equation `Delta psi=mu psi` and its conjugate, then the third
coefficient identity above. The real number `(x-1)*t` is nonzero. Therefore this
current is divergence-free at a point exactly when the actual reader vanishes there.
The current is not divergence-free everywhere: the existing exact horizontal mean at
height one is `Lambda(rho-1)`, which is nonzero by the physical cutoff calibration.
This is an unconditional source-specific obstruction, with a positive density and an
exact coefficient, rather than a hypothetical off-line Xi example.

The survivor identifies a required term for any attempted Hermitian positive-current
proof. It does not identify this angular current with the complete Einstein left-QNM
action. The solved `++`/`+-` corrections, independent SS/SV/VV channels, changing
metric weights, horizon, characteristic and source-contact terms remain in that
separate comparison. No boundary flux in that comparison is set to zero here.

The broader corpus search also returned `SymplecticCyclicObstruction` and
`PairedTranslationResolventCalculus`. The former requires a common cyclic generator
self-adjoint for the alternating pairing; this has not been established for the two
literal causal sources. The latter proves a positive half-line contact identity for
real damped-exponential packets, not for the complete complex Einstein pairing.
Neither hypothesis may be imported as the missing source law.

**Second pass: the literal nonlinear source, rather than the reader.** The source
field is `S=scalar(rho-1/2)`, with eigenvalue `lambda=rho(rho-1)`. Its current has
the different, critical-line-centered identity

```
div J_S = 4 i delta t |S|^2,  delta=x-1/2.
```

The existing original source is `Q=fullSquarePotential=S^2/2`, with
`E=fullGradientEnergy=y^2[(partial_0 S)^2+(partial_1 S)^2]` and
`Delta Q=2 lambda Q+E`. Applying the same actual derivative calculation gives

```
div J_Q - (conj(Q) E-Q conj(E)) = 8 i delta t |Q|^2,
delta t Im[div J_Q-(conj(Q) E-Q conj(E))]
    = 8 delta^2 t^2 |Q|^2 >= 0.
```

This is the stronger positive survivor: an exact positive local defect density
for the **original quadratic theta source**, retaining its complete nonlinear
gradient contribution. No clock or frequency is adjusted. The gradient term is
complex bilinear before pairing; replacing it with a Hermitian gradient square
would change the source equations.

On a finite smooth angular region D, ordinary Stokes gives the paper consequence

```
delta t Im[integral_boundary(D) J_Q.n ds
             -integral_D (conj(Q) E-Q conj(E)) dmu]
    = 8 delta^2 t^2 integral_D |Q|^2 dmu,
dmu=dx dy/y^2.
```

No infinite-cusp limit or renormalized sign is asserted. The precise remaining
test is whether the full physical causal Einstein pairing cancels the left-hand
flux-minus-gradient-work expression after its `++`/`+-` corrections and all
physical faces are included. The local identity proves neither that cancellation
nor equality of this expression with the reduced complete cokernel. It separates
the source's correct spectral center from the reader's different Green density.

**Lean status, 12 September 2026.**
`ThetaCuspHawkingBMSourceHermitianCurrent.lean` proves the actual reader's exact
spectral density, nonnegative orientation, node classification, and existence of
strictly positive divergence, followed by `source_divergence`,
`square_divergence_sub_gradient_contact`, and `square_oriented_contact_balance`.
Public source conclusions take only an actual Xi occurrence and an original
positive-height chart point; no source equation, covariance, sign, or extinction
premise is supplied. The finite-region Stokes consequence above remains a paper
consequence, not an integrated Lean theorem. Scratch check and exact cached leaf
audit passed without warnings; the leaf audit took 237 seconds. The module is wired
into `RHTower.lean`; no umbrella or full build was run.

## Consequences for the whole HB proof chain

The reader obstruction rejects the substitution of a Hermitian reader norm for
the physical projection. It does **not** reject source conservation, full-source
reflection, a direct sign estimate, or HB. The half-square identity gives a
source-centered positive density, but does **not** prove that this density is the
Einstein action's clock-defect energy. These are different quantities until an
actual comparison is proved.

The current corpus distinguishes three levels which must remain separate:

1. The literal causal response and physical projected mode/action are constructed.
   The normalizable temporal radial join retains both horizon branches and its
   source/contact and counterterm contributions. Its angular integration and
   comparison with the complete independent-channel nonlinear action remain open.
2. `hbXiPeierlsCanonicalFullCokernelCausalCutAt` is a fixed global algebraic model
   with `hbXiPeierlsPropagator` as retarded response and zero advanced response in
   both graded channels. Its exact realization theorem is a theorem about that
   defined split. It does not identify the actual Einstein retarded and advanced
   inverses or the complete physical left-QNM functional with that model.
3. For that reduced complete cokernel, the source-clock transduction is closed:
   `K=-Sigma*|D|^2`, `Sigma>0`, and `|D|^2=delta^2*|cocycle|^2`, with nonzero
   original cocycle. This is the receiver for a source theorem, not the producer.

### Competing mechanisms and their decisive tests

**Source reflection: positive transport and the surviving reader defect.** The
team's `ThetaCuspHawkingBMLiteralSourceReflection` now proves the full scalar,
coexact vector and fundamental metric branch exchange from divisor reversal,
Bessel order reflection and the nonreal completed functional equation. The
new `ThetaCuspHawkingBMSourceReflectionTransport` transports the four-amplitude
raw metric/source family, the switched mixed tensor and its onset contacts,
and the actual constructed mixed-stream response. Its 415-line leaf passed
scratch checking and the exact cached leaf build (164 seconds), without
warnings or increased limits, and is wired once into `RHTower.lean`. Source
SHA-256: `873fecaa24fa5056862718f9ba0de7a39c4e7276d803add870e5a53eb6671029`.
The extinction goal remains open; this card is not promoted as a complete proof.
API indexing and scoped whitespace checks completed. The repository-wide formal
lint check reported a separate shared-workspace failure: the newly present
`ThetaCuspHawkingBMScalarStreamMasterIdentity` was then unreachable from the theorem-area
umbrella. No lint error was reported for the new reflection-transport leaf; this
is not recorded as a passing global lint run. No owned Lean process remains.
The later action-weight-exchange audit above passed global lint after the shared scalar-stream
modules were wired by their author.

Write `qR=xiZeroCopyReflectEquiv q`, `b'=!b`, and `nu(q)=(rho-1)/2`.
The source's three principal indices reverse, `i -> i.rev`, with

```
k_i(qR)=k_(i.rev)(q),  A_i(qR)=A_(i.rev)(q),
s(qR,b)=s(q,b').
```

This transports the actual principal Green responses, their native full-square
subtractions, and all three differentiated cusp cutoffs. Consequently the
continued joint forcing, its admitted class, and its original wave response
agree after branch exchange. At **fixed physical reader** `r`, the resulting
physical profile, complete reconstructed mixed stream and volume-weighted
Einstein current obey

```
F(qR,b;r,w)=F(q,b';r,w),
A(qR,r,b;w)=A(q,r,b';w),
Hcontact(qR,r,b;w)=Hcontact(q,r,b';w).
```

The already proved `physicalProjectedModeAction_transport` supplies the exact
finite radial boundary identity for this same physical current. With
`lambda_r=nu(r)^2-1/4`, original left radial mode `g_r`, and the actual bilinear
angular factor `N_r=modeAngularSquare(physicalModeAngularJet r z)`, it reads

```
A_rad(t)-A_rad(s)
  = N_r * (-(lambda_r-2)*integral_s^t g_r(x)*F(q,b;r,w,x) dx
           -(Hcontact(t)-Hcontact(s))).
```

Thus the reflected source transports the bulk pairing and **both** finite
endpoint contacts simultaneously at fixed reader. No positivity of the
complex bilinear factor `N_r` is asserted. Infinite horizon/cusp limits and the
completed independent-channel action require their own original admissions;
the field identity is not permission to drop any endpoint or counterterm.

The physical frequency `w`, onset, radial inverse, angular measure and testing
weights remain unchanged. The positive transport result concerns the existing
constructed mixed-stream source and response. It does not yet identify all
independent SS/SV/VV channels or the fully corrected nonlinear action.

For the diagonal physical reader, the exact surviving difference is

```
A(qR,qR,b;w)-A(q,q,b';w)
  = A(q,qR,b';w)-A(q,q,b';w).
```

The reader itself satisfies `scalar(nu(qR))=scalar(nu(q)+1/2)`. Its eigenvalue
difference is `lambda(qR)-lambda(q)=(rho-1/2)/2`, which never vanishes at an
actual Xi occurrence because `Im rho != 0`. The literal eigen-equation and the
reader's proved nonzero Weyl mean therefore rule out equality of the two full
reader fields even on the critical line. This rejects the individual-reader
shortcut; it does not show that the complete nonlinear action difference is
nonzero. Its positive survivor is the fixed-reader action transport and the
exact reader-change remainder, including the transported source contact.

The existing `ThetaCuspHawkingBMSourceFaithfulBranchCovarianceNoGo` is a separate
obstruction: canonical left-coordinate source packets exchange only on the
critical line. Actual literal field exchange is now proved without that
condition, so one must derive their proposed physical incidence rather than
identify those two transports by definition. In addition, the source identity
here is complex-linear branch/parameter exchange. The finite-clock receiver
uses a conjugate-linear cocycle-weighted packet operation. Equality of those
operations after physical realization is still a mathematical obligation.

| Mechanism | Source evidence | Required next mathematical result |
|---|---|---|
| Fixed finite clock translation | Exact original onset/history and terminal-flux balances; local literal action variation | Show that the **sum** of translated history, horizon, cusp, characteristic, source-contact, and metric-weight terms has zero actual left-QNM projection. Stationarity of the kernel alone does not show this. |
| Source Hermitian balance | The new full-source half-square identity, including gradient work | Identify its flux-minus-work with the complete corrected action, or derive a coercive estimate controlling that action. Positivity before the required cusp/causal limits is insufficient. |
| Source reflection and Peierls reciprocity | Existing source-fixed cyclic/skew theorem makes a branch-swapped cubic cut odd | Derive literal branch exchange, admitted causal response transport, complete cyclicity/skewness with every boundary term, and the actual oriented BM incidence. Individual physical reader equality is unnecessary, but its failure must be handled in the projection comparison. |
| Direct sign without clock invariance | Exact negative-square transduction on the reduced model | Prove the opposite sign from the **original** complete physical source/action and justify transfer to the reduced model. A positive norm of an unrelated source or a reoriented convention does not supply this sign. |

For precision, let `C` denote the intended complete physical causal orbit, after
all specified corrections, independent SS/SV/VV channels, weights, and physical
faces have been included. The exact sufficient interface is

```
C = K,                  Re C >= 0.
```

Together with the proved transduction these give
`0 <= Re C = -Sigma*|D|^2 <= 0`, hence `D=0`, hence `delta=0` because the
original source cocycle is nonzero. No clock adjustment enters this implication.
Neither displayed interface property has been proved for that complete physical
quantity here; adding them as Lean premises would not close HB.

A second sufficient interface uses the **reflected sum**, so it need not assert
that either individual physical action has the opposite sign. Work at the
original fixed nonzero source normalization for which susceptibility positivity
is already proved. Retain independent SS/SV/VV coefficients throughout the
construction, and exchange their branch amplitude labels in the reflected cut
`Cswap(qR)`. The precise additional target is

```
Re(C(q)+Cswap(qR)) >= 0,
C(q)=K(q),  Cswap(qR)=K(qR).
```

The two established transductions would then give
`0 <= -Sigma(q)|D(q)|²-Sigma(qR)|D(qR)|² <= 0`.
Both susceptibilities are positive at that original normalization, so both
defects vanish. This does not assert strict susceptibility for arbitrary or
zero amplitudes. Exact oddness of the complete physical cut is one possible
producer of the first inequality; no equality of the individual reader fields
is needed. The new transport result supplies a concrete source/response part
of this test, not its complete cyclic/skew action identity, reflected boundary
admission, or incidence.


An exact equality is not the only possible interface. Writing `C=K+R`, it would
suffice to derive, from the actual equations and boundaries,

```
Re C >= 0,       Re R <= theta*Sigma*|D|^2,       theta < 1.
```

Then `0 <= Re C <= -(1-theta)*Sigma*|D|^2` gives the same extinction conclusion.
This identifies a strict relative-error target for an alternative quantitative
attack. No such estimate is established, and an absolute small-error bound would
not suffice uniformly as `delta` tends to zero. This observation is an interface
calculation, not a new source theorem or a formalized conditional wrapper.

The whole-chain source-reflection test must also respect the literal completion
factor: `reflectedCompletedLambda` is `GammaR*zeta`, not definitionally the totalized
completed zeta at every complex argument. Functional-equation transport for the
original nonreal Xi parameters can discharge the exceptional-point exclusions;
an unrestricted parameter claim cannot silently ignore them.

Broad searches for passivity and reciprocity supplied two further comparisons:

- [Borja and Ortega, Introduction to Passivity-based Control, 15 August 2026](https://arxiv.org/html/2608.15222v1),
  Definition 1 and Theorem 1: the storage inequality constrains a specified
  input/output supply pairing. For HB, the missing transfer is identification of
  that pairing with the actual left-QNM action. Choosing a different passive output
  would change the target. The paper supplies neither that identification nor
  finite-clock extinction.
- [Vu et al., Reciprocity can halve what a mechanical network can learn, 3 September 2026](https://arxiv.org/html/2609.04169v1),
  Theorem 1: symmetry of an invertible stiffness matrix constrains the response on
  overlapping drive/read coordinates. The useful HB test is whether reciprocity
  survives its distinct source and reader maps. That finite-dimensional theorem
  does not establish covariance or a sign for the full causal Einstein projection.

The whole-chain deep requests on action identification, source sign, and retarded
reflection were partial; their unfinished semantic stages and unverified ingredient
sets are retained in the search artifacts. A separate whole-corpus theta/reflection
hybrid request completed. None establishes exhaustive semantic coverage. Candidates
were checked against source definitions, including the canonical response split and
the assumptions of the source-fixed reflection theorem.

Corpus-wide deep/hybrid requests used translation/support, cyclic quartic
response, homogeneous character selection, conjugate Green/resolvent identities,
and retarded variational elimination, without a module filter. The retrieved
snapshots inventoried 57,236–57,237 files; most compiler metadata remained pending
and semantic coverage was unmeasured. One reader/norm hybrid request was partial
with interrupted retrieval stages. Returned ingredient groups were inspected but
not treated as proofs; in particular Keldysh resolvent algebra does not by itself
supply a Schwinger–Keldysh physical action.

Broad recent-paper searches also led to two checked primary sources:

- [Moody et al., QMaxCal, 18 June 2026](https://arxiv.org/html/2606.19947v1),
  equations (8)–(10): a drift-difference square controls path-space relative
  entropy under a shared diffusion model. HB has no independently established
  such path measure. Optimizing the reference drift cannot supply the prescribed
  common-clock theorem.
- [Gruber et al., Flexible and Stable Dynamics Discovery with Onsager's
  Variational Principle, 23 June 2026](https://arxiv.org/html/2606.24106v1),
  Definition 2.1: the variational balance requires a specified free energy,
  convex dissipation potential, and process map. These are not established for
  HB's complete complex causal action. This remains an unproved transfer, not a
  counterexample or an extinction theorem.

A further whole-corpus deep source-transport request completed without retrieval
errors, inventory 57,245 files, but without measured exhaustive semantic
coverage. Its generated matrix-defect and generic transport suggestions did
not discharge physical action incidence. A hybrid variational/reciprocity
request (57,246 files) recovered the actual `pairedSource_cubic`: its varying
test/volume term is `testWeightSlope * quadraticResidual` and must remain until
the **complete** quadratic equation is solved. Neither the source's scalar
reflection nor a fixed-background symplectic formula erases that term.

[Ghomi, 28 August 2026](https://arxiv.org/html/2608.28410v1), Theorem 1.1 and
Corollary 3.2, supply a different mechanism worth testing: a convex geometric
functional along a reflection path has equal endpoint values; the original
first-variation equation makes its endpoint derivative zero, forcing constancy
and then rigidity. For HB, the corresponding attempt requires a source-derived
convex complete action with its original boundary variations. No such
convexity or stationary endpoint has been proved for the complex causal
Einstein action. The result does not license choosing a new positive
functional. Broad crossing/polarization/variational searches returned no
additional usable recent theorem in this request; the direct arXiv search
pages failed to fetch. No claim of exhaustive literature coverage is made.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target remains the complete physical quantity `2 Ω(B(p,p)/2, B(m,m)/2)`, including full tensor corrections, time onset, horizon and AdS terms. A scalar source moment is a test of a proposed cancellation mechanism, not a replacement for that target.

## Frozen cancellation conjecture and tests

Conjecture: the literal source relations force cancellation between the complete causal bulk pairing and its actual endpoint terms at the fixed Hawking clock. This remains unproved. No zero-pairing premise may be inserted in its construction.

The working method is conjecture → attempted proof or falsification → pivot. Do not resume general action-current infrastructure unless a specific step in a source-level proof needs it. Failed proof attempts and falsified statements must be distinguished.

The current positive result is the [exact onset decomposition of the full original mixed scalar source](../3-formalized/hb-full-source-onset-reduction.md). It reuses the existing global angular inverse and identifies the actual time-dependent remainder as a fixed ingoing onset pulse. The incoming horizon profile is explicitly `H-s(s-1)Q/4`; it must remain in the causal pairing. The next primary test is cancellation between this horizon contribution and the pulse response in the complete tensor action, including the missing scalar-scalar and vector-vector channels. Do not substitute an isolated scalar-pole or normalization theorem for that test.

**Active tensor test.** The [Einstein radial action current](../3-formalized/hb-mixed-radial-action-current.md) is proved by differentiating the actual volume-weighted action current. The [original-source contact reduction](hb-causal-onset-contact-cancellation.md) identifies the pulse term that cancels the particular field's explicit `D_chi=integral exp(-6v)*chi'^2` coefficient. The remaining local contribution has only `C_chi=integral exp(-6v)*chi²` and the exact complex factor `2s+3`. This is a local analytical source identity; actual causal horizon admission and global integration remain open. The explicit unresolved term is equation (6) in that card: the pulse's horizon pairing through `roughLaplacian-1`, its cross terms with the particular field, and its original-source contact terms. Equation (7) reduces the cross terms to one source-derived test while retaining time and cusp boundaries. Evaluate that causal pulse term next; do not repeat the squared-onset coefficient check. Full extinction also requires every other tensor-sector pairing. With independent branch polarizations, SS–VV and SV–SV carry different amplitude monomials; do not combine their coefficients without a source-derived relation. No physical extinction is proved.

1. **Test: the original fundamental source is a cubic endpoint primitive.** The exact reduction below leaves one period with an explicitly fixed coefficient. At `s=w=0`, the source integral is `2/3`; the coefficient of the remaining period is nonzero. Thus the proposed universal pure-cubic-primitive identity fails. This is not a counterexample to extinction at a Xi divisor, and does not retire HB. The positive result is the explicit primitive-plus-period decomposition.
2. **Test: the complementary period is obtained by exchanging the two physical QNM branches.** The period identity exchanges `(w,2s)`. The actual target frequencies have real part between `-2` and `-1`, whereas the source rates `2s` have real part between `-4` and `-2`. Thus simple physical branch exchange does not perform the needed period exchange. The canonical left connection covectors also act on source/response coordinates at a fixed spectral parameter; their proved normalization is not the missing source-rate exchange. This rejects that proposed proof step, not every possible augmented adjoint identity.
3. **Positive source test: do radial and angular completion use independent affine arguments?** They do not. The original radial quadratic coefficient factors through the same `5 rho/2-1` and `3 rho/2` arguments appearing in the evaluated angular source, and their functional-equation complements. The exact identities are below. Whether the *full tensor causal pairing* uses these factors with the required orientation remains open.

**Causal value construction.** The [source-only circle kernel](hb-causal-horizon-circle-kernel.md) gives an analytical formula for the full horizon response using the literal theta-square field, the original radial source polynomial, and finite hyperbolic circle averages. Its pulse comparison closes by an exact radial flux identity and cancellation of the moving AdS image endpoint. The [scalar Riemann kernel](../3-formalized/hb-causal-riemann-kernel.md) has actual derivative, original BM wave, characteristic, causal support, and AdS boundary theorems in Lean. Full angular Green identification, horizon admission, and evaluation of the resulting Einstein pairing remain open. The next cancellation test uses this explicit source-only response, retaining every tensor sector and all endpoint terms.

## Actual radial source, without setting w = 2s

The starting definitions are `D4BMJointSource.fundamentalSourceCore` and `fundamentalSourceMoment`, together with `D4BMLaplaceRadial.sourceRemainder`. The corpus already identifies the original two-endpoint moment with its full first-subtracted Mellin integral at every physical fundamental QNM.

Put `y=sqrt(1-z)`, `alpha=2s-w`, `beta=2s+w+2`, and

```
A = (5s²+15s+4)/4
C = s(s-1)(alpha+2)(beta+3)/8.
```

The factorization follows directly from

```
(s+2)² - [(w+1)(w+2)/2 - (s+1)(s+2)]
  = (2s-w+2)(2s+w+5)/2.
```

The actual density transforms to

```
2 a² y² (1-y)^w (1+y)^(2s) (A+C y²) dy.
```

This is a change of coordinate in the original source, not a new source model. The original horizon finite part must be transported with the coordinate change.

Let `D=beta(beta+1)(beta+2)`, `U=s(s-1)(alpha+2)`, `V=5s²+15s+4`, and define the denominator-cleared cubic `P(y)=c0+c1 y+c2 y²+c3 y³` by

```
c3 = -U beta(beta+1)(beta+2)/4
c2 = -U alpha beta(beta+1)/4
c1 = -beta [U(3beta+6+alpha²)+2V(beta+2)]/4
c0 = -alpha [U(5beta+8+alpha²)+2V(beta+2)]/4
R  = c1+alpha c0.
```

Its exact polynomial identity is

```
(1-y²)P'(y) + (alpha-beta y)P(y)
  = 2D y²(A+C y²) + R.
```

Both this denominator-cleared identity and the original source factorization passed `lake env lean` scratch checks, with only `propext`, `Classical.choice`, and `Quot.sound`. They have no premises. They are not installed as standalone corpus leaves: the integral/physical-pairing result, rather than two isolated algebra lemmas, is the intended deliverable.

Multiplying by `(1-y)^w(1+y)^(2s)` identifies the left side as the derivative of

```
(1-y)^(w+1)(1+y)^(2s+1) P(y).
```

For `Re w>-2`, `w+1 != 0`, and `D != 0`, define the endpoint period by

```
I(w,s) = lim_(b→1-) [integral_0^b (1-y)^w(1+y)^(2s) dy
                     + 2^(2s)(1-b)^(w+1)/(w+1)].
```

The Taylor remainder at `y=1` is first order, so the subtracted integral converges. Transporting the original `z`-cutoff finite part gives the analytical formula

```
fundamentalSourceMoment(w,s,a) = -a² [c0 + R I(w,s)] / D.
```

To check the finite-part transport, set `z=epsilon`, `b=sqrt(1-epsilon)`. Then `epsilon=(1-b)(1+b)`. The primitive's leading divergent term cancels the original source subtraction and the period subtraction because

```
-2(w+1)P(1) = 2D(A+C)+R.
```

Every remaining endpoint error is `O(epsilon^(Re w+2))`, hence tends to zero. The AdS endpoint is `y=0` and contributes `-c0`. This establishes the paper reduction; the integral identity and its complete Lean admission are not yet formalized.

## Substitution of the actual Xi parameters

For `rho=q.1`, the source rates are `s=rho-2` and `s=-rho-1`; the two target frequencies are `w=-1-rho/2` and `w=-2+rho/2`. They remain independent slots.

| Source rate | Target | alpha+2 | beta+3 | beta |
|---|---|---|---|---|
| `rho-2` | `-1-rho/2` | `5rho/2-1` | `3rho/2` | `3rho/2-3` |
| `rho-2` | `-2+rho/2` | `3rho/2` | `5rho/2-1` | `5rho/2-4` |
| `-rho-1` | `-1-rho/2` | `1-3rho/2` | `2-5rho/2` | `-5rho/2-1` |
| `-rho-1` | `-2+rho/2` | `2-5rho/2` | `1-3rho/2` | `-3rho/2-2` |

Since actual Xi divisors have nonzero imaginary part, `D != 0` in all four cases. The target-branch exchange swaps the two factors in C; it does not change C at a fixed source rate. Both source branches have

```
A = (5rho²-5rho-6)/4.
```

Writing `x=5rho/2-1`, `v=3rho/2`, the two C coefficients are

```
C_plus  = (rho-2)(rho-3) x v / 8
C_minus = (rho+1)(rho+2) (1-v)(1-x) / 8.
```

Thus `C_plus*C_minus` contains the completion polynomial `x(x-1)v(v-1)`. These are exactly the two non-repeated affine arguments in `physicalSelfSourceCoefficient_fourLambda`; the repeated argument is `rho/2`. This is an exact source normalization relation, not evidence by itself that the full pairing vanishes.

## Complementary-period candidate: required admission and missing identification

In the ordinary convergence chamber, splitting the complete interval at zero gives

```
I(w,s) + I(2s,w/2)
  = integral_(-1)^1 (1-y)^w(1+y)^(2s) dy
  = 2^(w+2s+1) integral_0^1 t^w(1-t)^(2s) dt.
```

Continuation to the physical parameters cannot use the same first subtraction in both terms. For the exchanged term, `-4<Re(2s)<-2`, so subtract the three actual Taylor terms of `(2-t)^w`:

```
2^w [1 - w t/2 + w(w-1)t²/8].
```

The corresponding restored boundary terms are

```
2^w [1/(2s+1) - w/(2(2s+2)) + w(w-1)/(8(2s+3))].
```

The remainder is `O(t³)`, giving absolute admission because `Re(2s)+3>-1`. These coefficients are forced by the candidate period, not adjustable counterterms. None has yet been identified with the actual augmented Einstein horizon/AdS/onset terms. The continuing hard attack is that identification with the *complete* scalar-scalar, scalar-vector, and vector-vector source and its causal corrections. A scalar period completion must not be promoted to physical extinction without it.

## Actual source-reflection test, 12 September 2026

This tests cancellation in the requested physical pairing, not the deferred invented differential generator. No extinction theorem or new Lean leaf results from the test.

At the input, reflection `rho -> 1-rho` exchanges `s=rho-2` and `t=-rho-1` without changing the original clock or onset. The completed angular scalar is even in its centered parameter: in its Fourier coefficient `n^u sum_(d|n) d^(-2u)`, the divisor substitution `d -> n/d` gives the coefficient at `-u`; the Bessel factor satisfies `K_u=K_(-u)`, and the two Weyl terms exchange by the completed functional equation. Hence the literal half-square is unchanged. This literal source identity is now proved in Lean; the actual metric/source coefficients exchange with their scalar/vector amplitude labels, and the source-reflection transport result above reaches the constructed mixed response at each fixed physical reader. It does not establish the complete corrected physical pairing's reflection law.

The marked physical reader has a different transformation. The current definitions and proved formulas are `physicalAngularParameter_eq`, `physicalScalar_principal`, `physicalScalar_cutoff_calibration`, and `physicalFundamentalFrequency_eq`. For their actual testing field `psi_q`, put

```
nu_q=(rho-1)/2,               mu_q=nu_q²-1/4=rho(rho-2)/4,
nu_Rq=-rho/2,                mu_Rq=(rho²-1)/4,
mu_q-mu_Rq=(1-2rho)/4.
```

The difference is nonzero at every actual Xi occurrence because `Im rho != 0`. In particular it is not a defect that disappears on the critical line. The two original fundamental frequencies obey

```
w_+(Rq)=w_-(q)+1/2,
w_-(Rq)=w_+(q)-1/2.
```

These are comparisons of the original frequencies, not replacements of them. Thus input branch exchange does not preserve the marked angular eigenspace or exchange the prescribed QNM frequencies without a shift. The independent angular source equations give the exact paper identity

```
(Delta-mu_q)(psi_q-psi_Rq)=(1-2rho)psi_Rq/4.
```

The right-hand field is nonzero: the existing cutoff-calibration theorem gives a nonzero actual period for it. The Xi zero removes one Weyl coefficient, but leaves the explicit principal reader terms

```
psi_q,principal  = Lambda(rho-1)y^(1-rho/2),
psi_Rq,principal = Lambda(-rho)y^((1+rho)/2),
```

with both coefficients nonzero. Consequently an argument using antisymmetry at a *fixed* reader must still evaluate the difference of the two actual readers, including its forced bulk and principal cusp terms. Antisymmetry alone does not cancel this difference. This does not prove that the complete nonlinear difference is nonzero: every solved correction, all nine independent channel pairings, and their original boundary terms can still contribute to its evaluation.

There is a further scope restriction on a proposed arithmetic cancellation. `physicalSelfSourceCoefficient_fourLambda` assumes `1/2 < Re rho`. Its reflected copy lies in the opposite half-strip. Substituting that copy into the theorem, or continuing an identity known only at discrete Xi occurrences by the identity theorem, is not licensed. No new formula for the reflected complete physical source coefficient is asserted here.

The direct unresolved task remains evaluation of the complete source pairing with these original readers. Neither the source reflection identity nor the one vanished Weyl coefficient proves `Cphys=0` or `Re Cphys>=0`. The reduced identity `K=-Sigma|D|²`, with `Sigma>0`, remains a receiver until that actual cancellation or sign is produced.

The deep four-source and source-reflection searches and the hybrid response-pairing method search returned no retrieval errors with 57,233 inventoried files; most compiler metadata remained pending. Candidate statements, source methods and ingredient groups were inspected. Abstract reflection-odd Peierls theorems require source/reader incidence; the retrieved rotation, matrix-norm and generic Maass-flux ingredients do not evaluate the present pairing. Broad searches used scattering, crossing, sum rules, resonance and reciprocity. [Khankhoje–Kundu, 12 June 2026](https://arxiv.org/html/2606.14486v1), Sections I–III, distinguish full reciprocal scattering from coefficients that omit coupling and boundary effects. Their linear electromagnetic reciprocity does not supply an Einstein source identity or the marked QNM-reader comparison. No numerical work or external theorem premise was used.

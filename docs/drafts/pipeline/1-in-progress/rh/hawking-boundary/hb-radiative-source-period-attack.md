# HB: direct source-period attack on radiative extinction

Status: analytical source reduction; physical extinction and RH unproved. Frontier map remains read-only.

Verified findings and scoped no-gos from this work: [concise research log](../../hb-extinction-own-research-log.md).

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

**Direct-arm normalized normal limit and first radial jet checked in Lean; isolated cached exact-leaf audit passed (88 seconds, 2 jobs).** The full two-arm passage (CFJ) and late memory evaluation subsequently passed combined scratch verification; their updated isolated cached leaf audit passed (32 seconds, 2 jobs). The first field expansion in (CJ) remains paper-only. Let
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
`O(exp(2*d*x))=O(c(x)^d)` at fixed `v`. Joint differentiation follows
from continuous partial derivatives: for either transferred source weight,
the original density is jointly continuous in `(v,x)` and, locally in `v`,
is dominated by `C exp((a0-d)*h)` uniformly in `x`. Dominated convergence
therefore gives continuity of `timeArm` and `normalArm`. The corpus's
`hasStrictFDerivAt_uncurry_coprod` then gives the actual joint derivative.
The image chain rule and the original scale identity give

```
d/dx A(v-2x,-x) = -2*timeArm(v-2x,-x)
                   +(2-c(-x))*normalArm(v-2x,-x),
2-c(-x)=c(x),
exp(2*d*x)/c(x)=[exp(2*d*x)+exp((2*d-2)*x)]/2.      (CIJ)
```

Both exponents are positive. Hence the full image derivative divided by
`c(x)` tends to zero; division by `r^2-1` has the same conclusion because
`(r^2-1)/c(x)->2`. This retains both image derivatives before taking the
limit. **The joint and image extension passed combined scratch verification and its
isolated cached exact-leaf audit (42 seconds, 2 jobs).**
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

**Positive physical-clock source work, checked in combined scratch.**
On the original late region `v>=1`, exact integration gives
`I_g(v)=-exp(2*s*v)/(2*s+1)`. Since `Re(2*s+1)<0`,
`exp((2*s+1)*T)!=1` for every real `T>0`, as follows already from
its norm being less than one. Thus

```
exp(T)*I_g(v+T) != I_g(v),
W(v,T)=integral_0^T exp(h)*g(v+h) dh != 0.           (CNV)
```

The full cap's finite-clock radial difference tends to
`-l*(Delta_H Q/2)*W(v,T)`. This limit coefficient vanishes exactly when
`l*Delta_H Q=0` at the indicated angular point. This is a classification
of the source-derived cap datum; no nonzero angular coefficient is assumed.
It does not classify a contracted left-QNM finite part or the complete
nonlinear current. The physical clock and original onset remain unchanged.
The updated isolated cached radial leaf audit passed (32 seconds, 2 jobs).

**Reader-weighted cap remainder: source proof on compact angular tests (paper).**
The current corpus's `normalizable_fundamental_value` and
`horizon_eq_normalizable_fundamental` identify both original fundamental
normalizations with `z^(w/2)*(1-z)^(1/2)`. Here
`z=1-r^(-2)`, `radiusLift=r*Y`, and `tau=v-x`. Consequently the original
left stream is exactly

```
V(v,x,z_ang)=exp(-w*v)*c(x)^w*V0(z_ang),
D V=w*(1-c)*V,  D=partial_x+partial_v.               (CLF)
```

Positive real bases fix the logarithms in this formula. The source and target
frequencies are unchanged. At the prescribed roots, `-2<Re w<-1`.
An `o(c)` cap remainder therefore does not establish a vanishing product
with this reader.

There is a stronger source estimate. Let `a0=sourceGrowthExponent q`,
choose `max(a0,-Re w)<p<d<2`, and write `K(1+y)` for the original
full-theta mean. The auxiliary `p,d` are bound exponents only. On every
compact angular set inside the upper half-plane,

```
|K(1+y)-Q-(Delta_H Q/2)*y| <= C_p*y^p,  y>=0.      (CTR)
```

Proof near `y=0`: apply the original circle construction to `G=Delta_H Q`.
Its first radial derivative at zero is zero, by the sine/cosine first
moments; its second derivative is bounded on the compact circle/center
parameter set because the literal source is smooth. Hence
`|mean_G(d0)-G|<=C*d0^2`. Since
`arcosh(1+y)^2<=3y` for `0<=y<=1`, the actual `angularAction(1+y)` differs from `G` by
`O(y)`. The already proved Volterra formula
`K'(1+y)=(2+y)^(-1)*integral_0^1 angularAction(1+t*y)dt`
then gives `K'(1+y)-G/2=O(y)`. Integration gives an `O(y^2)` remainder,
which is bounded by `O(y^p)` for `0<=y<=1`. For `y>=1`, original global
theta growth and `arcosh(1+y)<=log(4y)` bound the three terms by
`C*(y^a0+1+y)<=C'*y^p`. All local constants can be chosen uniformly
on the indicated compact angular set.

Substitute `y=c*(exp(h)-1)` into (CTR). The unchanged onset and its
first two derivatives admit `C_d*exp(-d*(v+h))`: their physical rate has
real part below `-2`, and their switching derivatives are supported in
`[0,1]`. The dominating integral is `integral_0^infinity exp((p-d)*h)dh`.
Use the source endpoint moments already derived in (CJ)/(CTM), then include
the image arm, whose value and transferred partials are `O(c^d)`.
For the full original scalar cap `u`, uniformly on compact `v` and angular
sets, this yields

```
u=l*g*Q+l*c*I_g*(Delta_H Q/2)+O(c^p),
D u=l*g'*Q+l*c*(I_g-g)*(Delta_H Q/2)+O(c^p).        (CTJ)
```

For a smooth compactly supported angular test `eta`, define
`Phi(F)=integral F*R(eta*V0)` and
`Psi(F)=integral F*Lstar(R(eta*V0))`, with the original operators in
(WT) below. Weak angular transposition retains every derivative of `eta`.
Using `A V0=(mu-2)V0`, the contact-corrected radial current, including
its original `r^2` volume factor, has the distributional angular pairing

```
exp(-w*v)*c^w*(B0+c*B1+O(c^p)),
B0=l*((mu-2)*g'*Phi(Q)-w*g*Psi(Q)),
B1=l*((mu-2)*(I_g-g)*Phi(Delta_H Q/2)
       -w*I_g*Psi(Delta_H Q/2)+w*g*Psi(Q)).         (CLB)
```

Thus subtraction of these two explicitly source-derived terms leaves a
quantity tending to zero, since `p+Re w>0`. This proves a compact-test
remainder estimate, **not** identification of this subtraction with the
prescribed physical finite part. The infinite-cusp cutoff limit, actual
angular metric realization, other faces, independent SS/SV/VV corrections
and complete nonlinear balance remain open. The pointwise-in-centre version
of (CTR), its local quadratic bound, and its characteristic derivative bound
are now proved in `BMCapReaderRemainder`; its isolated cached leaf audit passed
(49 seconds, 2 jobs). The compact-uniform bound and the full-cap/angular passage
in (CTJ), (CLF) and (CLB) remain paper results.

**Leading cap coefficient after physical-time projection, 13 September 2026 (paper).**
The pointwise `c^w` coefficient in (CLB) and the original continued radial
current have different leading orders before time and angular projection.
This difference has an exact source-level decomposition. Keep independent
source occurrence `q`, reader occurrence `r`, both original branches,
`g(v)=timeOnset(2*physicalRate q branch,v)`, and
`w=physicalFundamentalFrequency r side`. The source strip gives
`Re(2s)<-2<Re w`; hence the current corpus's actual onset transform proves

```
integral_0^infinity exp(-wv)*(g'(v)-w*g(v))dv=0.
```

This includes the derivative of the fixed transition. Its lower endpoint
is zero because `g(0)=0`; its upper endpoint is zero because `Re(2s-w)<0`.
Define the complete compact-cutoff defect
`H_eta(Q)=Psi(Q)-(mu-2)*Phi(Q)`. The leading coefficient therefore satisfies

```
exp(-wv)*B0
 = partial_v[l*(mu-2)*exp(-wv)*g(v)*Phi(Q)]
   -l*w*exp(-wv)*g(v)*H_eta(Q),
integral_0^infinity exp(-wv)*B0 dv
 = -l*w*onsetTransform(2s,w)*H_eta(Q).             (CLT)
```

The zero time-boundary term and the exact time projection with independent
angular coefficients are now proved in `BMCapLeadingTimeCurrent`; its isolated
cached exact-leaf audit passed (97 seconds, 2 jobs). The realization of those
coefficients as the angular pairings below remains a paper statement.

The angular defect is explicit. Put `S_r` for the unchanged reader scalar,
`V0=(partial_y S_r,-partial_X S_r)`, and let `Delta_flat` denote the
Euclidean coordinate Laplacian. The original equation is
`y^2*Delta_flat S_r=mu*S_r`. Thus `R(V0)=-mu*S_r/y^2` and
`Lstar(R(V0))=(mu-2)*R(V0)`. With `J=-grad eta dot grad S_r`, direct
Leibniz expansion gives

```
Lstar(R(eta*V0))-(mu-2)*R(eta*V0)
 = -mu*S_r*Delta_flat eta-mu*grad eta dot grad S_r
   -Delta_flat(y^2*grad eta dot grad S_r).          (CLA)
```

Every term is supported where derivatives of the angular cutoff occur.
This explains why the leading pointwise divergence cannot be compared
directly with the already time-projected radial finite part. The actual
`continuedHorizonSourceCounterterm` starts at the first integrated Mellin
power, and its restored current is proved only in its stated projected
interface. Equations (CLT)/(CLA) do not admit the infinite-cusp cutoff
limit or identify the complete nonlinear finite part. Their positive
survivor is the exact transfer of the leading time-boundary term to
angular-cutoff work, with source/reader frequencies unchanged.

Recent broad-search sources supplied comparison tests, not HB premises:
[2608.26244, introduction](https://arxiv.org/html/2608.26244v1) distinguishes
fixed physical and field-dependent coordinate cutoffs;
[2608.09858, abstract](https://arxiv.org/abs/2608.09858) distinguishes
cancellation of divergent terms from invariance of the finite action.
Neither establishes the required original-source cancellation.

**Source flux behind the angular-cutoff defect, 13 September 2026 (paper).**
Let `F` be the original source scalar, `Q=F^2/2`, `E=y^2*|grad F|_bilinear^2`,
`lambda=center(q)^2-1/4`, and `S=S_r` the independent actual reader scalar
with `Delta_H S=mu*S`. For smooth compactly supported `eta`, (CLA) and two
coordinate integrations by parts give

```
H_eta(Q)=integral grad eta dot K,
K=mu*S*grad Q-(Delta_H Q)*grad S
 =mu*S*grad Q-(2*lambda*Q+E)*grad S.              (CLK)
```

For example, put `P=(Delta_H-mu)Q`. Transposing `Lstar` first gives
`H_eta=integral P*(-mu*eta*S/y^2-grad eta dot grad S)`.
The first summand equals `-mu*integral eta*div(S grad Q-Q grad S)`.
A further integration by parts yields (CLK), retaining the gradient-energy
term `E`. The full bounded-region edge terms are those in (WT); the compact
support assumption is what removes them here.

This is not just the first Stokes current. Define
`J_Q=S grad Q-Q grad S`, `J_E=S grad E-E grad S`. Direct Leibniz expansion gives

```
K=(lambda+mu/2)*J_Q+J_E/2-grad(S*P)/2.            (CLD)
```

The finite-region identity retains the last gradient flux and the domain
comparison. The residue calculation (CLSR) below now removes its independent
constant-sector contribution; this does not remove it at finite cutoff.

For constant Weyl powers `Q=A*y^beta`, `S=B*y^gamma`, where
`mu=gamma*(gamma-1)`, the actual vertical flux is
`A*B*beta*gamma*(gamma-beta)*y^(beta+gamma-1)`. Its specialized constant
coefficient can survive at `beta+gamma=1`. For the original diagonal reader,
`u=rho-1/2`, `v=(rho-1)/2`, every boundary exponent is
`1/2+(epsilon1+epsilon2)*u+epsilon3*v`.
Its imaginary coefficient of `rho` is one of `+/-1/2,+/-3/2,+/-5/2`,
so no exponent is zero because the original Xi occurrence is nonreal.
This source-specific diagonal fact is stronger than merely discarding a
nonzero affine exponent before specialization. It does not assert the same
noncollision for independent source and reader occurrences.

**Finite angular boundary and exact source residue, 13 September 2026.**
On a bounded smooth region `Omega` in `y>0`, put
`psi=R(eta*coexact(S))=-div(eta*grad S)`. The same calculation retains
all edges:

```
H_eta(Q)=integral_Omega grad eta dot K
 +integral_boundary [Q*partial_n(y^2*psi)-y^2*psi*partial_n Q
                    -mu*eta*(S*partial_n Q-Q*partial_n S)].    (CLKB)
```

Indeed Green's second identity first contributes the first two displayed
edge terms. Using `div(J_Q)=S*(Delta_H-mu)Q/y^2` and integrating
`-mu*eta*div(J_Q)` once contributes the last. Normal orientation fixes
the sign on every edge; at the upper cusp it is `n=+partial_y`. The
changing weight `y^2`, derivatives of the cutoff, and lower and side
edges remain explicit. Compact interior support removes these terms;
that fact does not identify a physical horizon or characteristic face.
This boundary identity and (CLD) are paper proofs, not new Lean claims.

The new `BMCapAngularFluxCusp` leaf identifies `K_y` with the actual full
Fourier expression, retains `E`, and proves that subtracting its literal
constant sectors leaves rapid decay after every complex height weight
at each fixed horizontal position. It also proves zero of the specialized
diagonal constant coefficient. Scratch checking and an isolated cached
exact-leaf audit passed (98 seconds, 2 jobs); the leaf is wired.

The independent-reader test gives a sharper source-specific classification.
Let `C(e1,e2,e3)` be the exact coefficient `constantCoefficient` in that
leaf, evaluated at `u=center(q),v=physicalAngularParameter(r)`. Then

```
R(q,r)=specializedFamily(q,r)(0)
 =1_{rho_r=4-4*rho_q}*C(false,false,false)
  +1_{rho_r=4*rho_q}*C(true,true,false).                       (CLR)
```

The literal Xi condition kills the reader's `true` coefficient, as follows
from the already source-proved `physicalScalar_principal` at height one.
The two mixed source Weyl sectors have nonzero specialized exponent by
the reader's nonreal Xi occurrence. The remaining two exponents vanish
exactly at the displayed resonances. `independent_specialized_constant`
proves (CLR) in Lean without assuming their absence. This is not a proof
that such pairs exist or that either displayed coefficient is nonzero.

**The extra gradient has no independent constant residue.**
Set `a_i=1/2+epsilon_i*u`, `gamma=1/2+epsilon_3*v`,
`beta=a_1+a_2`, `alpha=beta+gamma-1` and
`c=A(u,epsilon_1)*A(u,epsilon_2)*A(v,epsilon_3)`.
The original Weyl equations give `a_i*(a_i-1)=lambda` and
`gamma*(gamma-1)=mu`. For the actual ordered coefficients of `K_y` and
the existing first Stokes current `J=2*J_Q`, direct expansion gives

```
C_K-(mu/2)*C_J=-(c*gamma/2)*(beta-gamma)*alpha.                (CLSD)
```

Thus the discrepancy vanishes exactly where a constant height term could
occur. Summing after specialization proves, for arbitrary original complex
parameters (including every collision),

```
constant_residue(K_y)=(mu/2)*constant_residue(J_y).            (CLSR)
```

Both statements are Lean-proved in `BMCapAngularFluxResidue`, with no
spectral nonresonance premise. At the paper level, the constant coefficient
of `partial_y(S*P)` in (CLD) is
`(c/2)*(beta+gamma)*(beta-gamma)*alpha`, so it also vanishes at `alpha=0`.
This refines the earlier obstruction: the gradient is a necessary finite
boundary term, but supplies no new constant residue. The obstruction that
survives is the domain/physical finite-part comparison and the actual first
Stokes residue at independent reader parameters. An unspecialized affine
finite part cannot replace that specialized residue at a collision.

**Uniform cusp admission and cutoff residue: paper proof.**
The finite signed-tail identity `signedTail_eq_value` and the source bound
`D4BMAngularSeries.value_height_decay` hold uniformly in horizontal
position. The actual first vertical tail is exactly its height-divided
zero-order tail minus the two adjacent-order tails times `pi`
(`d4BM_completedEisensteinSignedSqrtWhittakerVerticalFirstJetTail_decomposition`);
the horizontal derivative is the frequency-weighted tail. Thus each
nonconstant factor among `F,F_X,F_y,S,S_y` has a bound
`C*Y^a*exp(-Y/2)` for `Y>=1`, independent of `X`. Each corresponding
constant sector has a finite polynomial height bound. Expanding the cubic
flux minus its constant sectors leaves a finite sum with at least one tail
in every term, including the `Y^2*F_X^2*S_y` term. Increasing the real power
and summing the finitely many constants gives

```
sup_X |K_y(q,r;X,Y)-constantVerticalFlux(u,v,Y)|
 <= C*Y^m*exp(-Y/2),  Y>=1.                                  (CLU)
```

No Fourier truncation or source-dependent frequency is used. This
uniform strengthening is paper-proved from those literal bounds; the new
Lean leaf currently proves only its fixed-horizontal-position consequence.

For a smooth height cutoff `chi(Y/H)` with `chi=1` below one and `chi=0`
above two, define its cusp-band work alone by
`W_H=integral_{H}^{2H} integral_{-1/2}^{1/2}
       H^(-1)*chi'(Y/H)*K_y(X,Y) dX dY`.
Finite expansion and `Y=H*t` give

```
W_H=sum_alpha R_alpha*H^alpha*integral_1^2 chi'(t)*t^alpha dt
    +O(H^m*exp(-H/2)).                                      (CLW)
```

The error follows from (CLU), the finite cutoff derivative bound and the
band length `H`; its inverse `H` prefactor cancels that length. Here
`R_alpha` groups the actual specialized exponents. Consequently the
constant-power finite part of this cusp-band work is exactly `-R(q,r)`,
since `integral_1^2 chi'=-1`. For the diagonal it is zero, independently
of the transition shape. This is a paper result about the displayed band
work and its explicit asymptotic expansion. Identifying it with the
prescribed physical finite part requires the full domain comparison,
including (CLKB), other faces and correction channels. It does not
produce complete radiative extinction.

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

The current positive result is the [exact onset decomposition of the full original mixed scalar source](../../../3-formalized/hb-full-source-onset-reduction.md). It reuses the existing global angular inverse and identifies the actual time-dependent remainder as a fixed ingoing onset pulse. The incoming horizon profile is explicitly `H-s(s-1)Q/4`; it must remain in the causal pairing. The next primary test is cancellation between this horizon contribution and the pulse response in the complete tensor action, including the missing scalar-scalar and vector-vector channels. Do not substitute an isolated scalar-pole or normalization theorem for that test.

**Active tensor test.** The [Einstein radial action current](../../../3-formalized/hb-mixed-radial-action-current.md) is proved by differentiating the actual volume-weighted action current. The [original-source contact reduction](../../hb-causal-onset-contact-cancellation.md) identifies the pulse term that cancels the particular field's explicit `D_chi=integral exp(-6v)*chi'^2` coefficient. The remaining local contribution has only `C_chi=integral exp(-6v)*chi²` and the exact complex factor `2s+3`. This is a local analytical source identity; actual causal horizon admission and global integration remain open. The explicit unresolved term is equation (6) in that card: the pulse's horizon pairing through `roughLaplacian-1`, its cross terms with the particular field, and its original-source contact terms. Equation (7) reduces the cross terms to one source-derived test while retaining time and cusp boundaries. Evaluate that causal pulse term next; do not repeat the squared-onset coefficient check. Full extinction also requires every other tensor-sector pairing. With independent branch polarizations, SS–VV and SV–SV carry different amplitude monomials; do not combine their coefficients without a source-derived relation. No physical extinction is proved.

1. **Test: the original fundamental source is a cubic endpoint primitive.** The exact reduction below leaves one period with an explicitly fixed coefficient. At `s=w=0`, the source integral is `2/3`; the coefficient of the remaining period is nonzero. Thus the proposed universal pure-cubic-primitive identity fails. This is not a counterexample to extinction at a Xi divisor, and does not retire HB. The positive result is the explicit primitive-plus-period decomposition.
2. **Test: the complementary period is obtained by exchanging the two physical QNM branches.** The period identity exchanges `(w,2s)`. The actual target frequencies have real part between `-2` and `-1`, whereas the source rates `2s` have real part between `-4` and `-2`. Thus simple physical branch exchange does not perform the needed period exchange. The canonical left connection covectors also act on source/response coordinates at a fixed spectral parameter; their proved normalization is not the missing source-rate exchange. This rejects that proposed proof step, not every possible augmented adjoint identity.
3. **Positive source test: do radial and angular completion use independent affine arguments?** They do not. The original radial quadratic coefficient factors through the same `5 rho/2-1` and `3 rho/2` arguments appearing in the evaluated angular source, and their functional-equation complements. The exact identities are below. Whether the *full tensor causal pairing* uses these factors with the required orientation remains open.

**Causal value construction.** The [source-only circle kernel](../../hb-causal-horizon-circle-kernel.md) gives an analytical formula for the full horizon response using the literal theta-square field, the original radial source polynomial, and finite hyperbolic circle averages. Its pulse comparison closes by an exact radial flux identity and cancellation of the moving AdS image endpoint. The [scalar Riemann kernel](../../../3-formalized/hb-causal-riemann-kernel.md) has actual derivative, original BM wave, characteristic, causal support, and AdS boundary theorems in Lean. Full angular Green identification, horizon admission, and evaluation of the resulting Einstein pairing remain open. The next cancellation test uses this explicit source-only response, retaining every tensor sector and all endpoint terms.

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

Research check for this continuation: the full-index joint-partial deep/method
search reported `partial=true` with 57,392 inventoried files; its
`ClockMultivariateC1` source argument led to the applicable Mathlib partial-
derivative theorem, verified in the finished source proof. The nonlinear
adjoint search reported `partial=true`, 57,395 files, and returned the
existing inhomogeneous correction exchange rather than a closed source
cancellation. Most compiler metadata was pending. Broad balance, rigidity,
memory and reciprocity searches read
[Bösch–Gediz–Türeci, August 2026, Section 6.2](https://arxiv.org/html/2608.11585v1)
and the abstract of
[Wang–Xie–Yu, June 2026](https://arxiv.org/abs/2606.30130).
The former distinguishes a nonlinear trajectory's tangent adjoint from
background reciprocity; this motivates checking additional source work,
not assuming it vanishes. The latter concerns three-dimensional scalar-
curvature rigidity; no HB metric or positivity hypothesis was supplied
from it. Neither paper is used as a premise of the Lean results above.

Verification checkpoint for (CIJ), (CFJ) and (CNV): combined scratch
`/tmp/hb-cap-combined.lean` passed; the two isolated cached leaf audits
passed sequentially (42 and 32 seconds, 2 jobs each). Both existing
umbrella imports remain present. No heartbeat/depth/transparency override
was added. Index refresh completed (4 changed, 0 removed).
`/tmp/hb-cap-full-radial-lint.log` records the unchanged unrelated failure:
`owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionCoprime`.
No global lint pass or complete extinction theorem is claimed.

## Full angular source potential attack, 13 September 2026

The current corpus proves `D4BMAngularTwoCuspDecay.actual_tensor_zero`;
its cached declaration was independently checked in a scratch import. This is
an existing result, not a new proof claimed here. For the original source S,
write F=S², lambda=rho(rho-1), and U=(2-Delta_H)^(-1)F, with U the already
constructed response. Put H(f)=(f_xx-f_yy-2f_y/y, f_xy+f_x/y) and
R(A,B)=(2B,-A/2). The proved tensor identity gives G=-lambda H(U), where
G=(S_x²-S_y²,S_x S_y). Product differentiation gives H_old+G=H(F)/2.
Consequently the original three-channel angular Einstein coefficient of
the fundamental unswitched metric is

```
B² [aS² ws H(F) + (aS aV wm/2) R H(F)
      + lambda(aS² ws-aV² wv) H(U)].                 (CAP)
```

Here ws, wv, wm are the original scalar, vector and mixed radial weights.
The existing explicit angular correction removes the first two terms and
leaves exactly the final H(U) term. This retains the complete Fourier source
and both tensor components. It does not identify that explicit angular
correction with the complete causal ++ or +- correction.

For an actual densitized trace-free left test (a,b), define

```
D(a,b)=a_xx-a_yy+2b_xy-2b_x/y+2a_y/y-2a/y²,
Jx(f)=a f_x+b f_y-f(a_x+b_y-2b/y),
Jy(f)=b f_x-a f_y-f(b_x-a_y+2a/y).
```

Direct product differentiation gives
`a H(f).1+2b H(f).2 = div J(f)+f D(a,b)`.
Each Hessian in (CAP) transfers to the full test and boundary normal flux J.n;
the rotated term uses test (-b,a). Changing density/inverse-metric weights
must be included in a,b before differentiation. On a bounded smooth angular
domain, integration gives the complete boundary integral. Extension to the
cusp finite part remains a separate domain obligation. A vanishing
holomorphic remainder alone therefore gives this scalar-potential action,
including boundary work; it does not give zero left action. The original
Hawking clock has not changed.

The source tensor identity and product rule prove (CAP). The actual physical
combined metric jet and (CAP) are now Lean-formalized and audited below.
The Green identity above remains a paper calculation; no complete physical
boundary cancellation is claimed.

For a scalar left angular eigenfield psi with `Delta_H psi=mu psi`, its
actual raised Hessian density has
`a=y² H(psi).1/2`, `b=y² H(psi).2`. Substitution in D gives

```
D(a,b)=Delta_H(Delta_H-2)psi/(2y²),   D(-b,a)=0.
```

These follow by expanding the four coordinate derivatives; in the first
identity the second-order terms cancel and the remainder is
`y² Delta_flat² psi/2+2y partial_y Delta_flat psi`.
Put `W=psi grad U-U grad psi`, with flat gradient in these coordinates.
The original inverse equation gives
`div W=((2-mu)U psi-F psi)/y²`. Consequently

```
<HessTF U,HessTF psi> dvol/dxdy
  = -mu F psi/(2y²) + div[J(U)-mu W/2].          (CAPG)
```

There is no division by `2-mu` in (CAPG). It therefore also holds at mu=2.
The complete three-channel source (CAP), tested against HessTF psi, has
bulk density

```
B² mu/2 [aS² ws(mu-2-lambda)+aV² wv lambda] F psi/y²
```

and boundary current

```
B² [aS² ws J(F;a,b)+(aS aV wm/2)J(F;-b,a)
     +lambda(aS² ws-aV² wv)(J(U;a,b)-mu W/2)].
```

Thus the mixed term is an explicit angular boundary current for this scalar
Hessian test. This is not a deletion of the mixed channel: a rotated test,
changing metric weights, or a corrected field changes the test entering D.
In particular the original physical left metric in
`D4BMLeftQNMMetricEquation.metricField` is a vector metric with mixed
(time/radial,angular) entries; it is not this pure Hessian test. (CAPG)
controls an angular tensor pairing inside assembly, not the complete
left-QNM action. The distinct source/reader current in log item 34 remains
in the correction exchange. These Green identities are paper-proved;
full quotient finite-part admission and Lean formalization remain open.

The full-index angular-potential deep/method search completed with
`partial=false`, 57,433 files and no inventory errors; most compiler
metadata was pending. Its source-argument retrieval supplied the actual
scalar/vector metric split used in the new proof. Broad Noether and
transgression searches found [Akil et al., 9 September 2026](https://arxiv.org/html/2609.10533v1).
Theorem 1 and its proof preserve a transition along a symmetry orbit once
a seed transition and invariant endpoint states exist. Applying that
argument here would still require the original HB boundary invariance
and a vanishing seed value. The paper does not supply either, and is not
a premise of the Lean theorem.

Verification checkpoint for (CAP): the final scratch passed, including the
original second Taylor coefficient, reconstructed coexact and combined metric
jets, independent amplitude polarization, and the explicit corrected angular
coefficient. `ThetaCuspHawkingBMPhysicalAngularPotential` passed its isolated
cached exact-leaf audit (37 seconds, 2 jobs) and is wired into `RHTower`.
Source SHA256: `082bdf871722264f45b9bba6c1056135275d76edfa40cb26271ef71d17afa464`.
No heartbeat/depth/transparency override was added. The Green identities
(CAPG), their finite-part admission, and complete physical extinction remain
outside this Lean result.

The final index refresh completed (7 changed, 0 removed). Formal lint with
`--check-generated` finished with one unrelated error: existing module
`GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionCoprime` is
unreachable from its theorem-area umbrella. No generated-file error was
reported. Scoped whitespace checks passed; the installed source hash and
unique umbrella import match the audited leaf. All owned processes finished.

## Spatial reflection of the actual causal response, 13 September 2026

This is horizontal spatial reflection `(X,Y) -> (-X,Y)`, not functional-equation
reflection of a spectral parameter. The literal scalar is even for every complex
parameter: its positive and negative Fourier phases exchange term by term, and
the two Weyl terms are independent of X. No convergence-chamber substitution or
critical-line premise enters this argument.

The original circle chart obeys
`circle(d,2*pi-theta,(-X,Y)) = reflect(circle(d,theta,(X,Y)))`.
Consequently its literal half-square source and circular average are even in X.
The original native Riemann kernel, supported Dirichlet kernel (including the
image), and full null response are even in X. For the last statement, the exact
defining double integral has circle radius
`arcosh(max(1,invariant((p+r-a-b)/2,(p-r)/2,(a-b)/2)))`; its radius, source
rectangle, odd radial source and normalization are independent of X. The three
subtracted cutoff powers depend only on height, so the residual and its actual
double time primitive inherit the same reflection. This preserves the original
clock and all characteristic support in these scalar response formulas.

Put `S=S_u(X,exp k)`, `T=S_v(X,exp k)` with independent complex u,v, and let C
be the actual full null response. Define

```
J_X = S*T_X-T*S_X,     J_k = S*T_k-T*S_k,
W = J_X*C_k-J_k*C_X.                                  (SRC)
```

Differentiating the established reflection identities gives odd horizontal and
even vertical derivatives. Thus J_X is odd, J_k is even, and W is odd. Actual
source and causal-response smoothness admits W on every bounded horizontal
interval. Its integral over `[-L,L]` is zero. The same holds after any factor
depending only on time, radius and height. In original coordinates,
`<S dT-T dS,*dC>_H = exp(k)*W`; the hyperbolic density changes this by a further
height-only factor. Hence the cross-eigenvalue current from item 34 has zero
horizontal work on these slices without equating its two eigenvalues.

The boundary flux used to transfer this current is `S*T*(*dC)`.
Its horizontal component is even and its vertical component is odd. Paired
vertical sides have cancelling outward flux; each horizontal edge has zero
integrated flux on a symmetric slice. In logarithmic coordinates its densitized
components are `P=(S*T*C_k,-S*T*C_X)` and the exact identity is
`W=-div(P)+2*S*(T_X*C_k-T_k*C_X)`. These identities, actual smoothness and all
four oriented rectangle boundary cancellations are now checked in Lean.
Reflection also cancels its flux on paired smooth boundary arcs of a symmetric
bounded angular domain [paper calculation]. Identification with the prescribed
full physical finite part and its coupled horizon/source-contact faces is not
claimed.

The positive survivor is a source-produced cancellation of this extra Jacobian
work, including the actual causal scalar response. It does not annihilate the
complete action: `exp(2k)*T_X*C_X+T_k*C_k`, the coexact/coexact contraction,
is even. A reflected nonlinear metric with a coexact source sends its vector
amplitude to its negative. If covariance of the complete assembled action is
derived, a vector left reader therefore retains terms with an odd number of
source-vector factors (including the mixed quadratic channel and scalar-scalar-
vector/vector-vector-vector cubic channels). Full nonlinear covariance and
these surviving channels remain separate obligations; they are not assumed.

The finished `ThetaCuspHawkingBMSpatialReflectionCurrent` leaf also identifies
the original inverse-metric/coexact contraction as `exp(k)*W`, proves its finite
slice admission and cancellation, and handles paired slices with a symmetric
inner gap. Its full scratch check and isolated cached exact-leaf audit passed
(127 seconds, 2 jobs); it is wired into `RHTower`. Source SHA256:
`5a979ddbd123a01b07b7f3c35fae721df0e9e97c3c61e0b50b9c8313ed0943b3`.
No heartbeat, depth or transparency override was added. The index refresh
completed (7 changed, 0 removed). Formal lint reported the existing unrelated
unwired module `GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionCoprime`;
no generated-file error was reported. Scoped whitespace checks passed.

The new deep/method query covered all 57,440 indexed files (`partial=false`),
with compiler metadata predominantly pending and semantic coverage reported
unavailable. Its suggested modular tensor pullbacks use SL(2,Z), which is
orientation preserving; they do not supply the orientation-reversing nonlinear
reflection needed here. The Fokas-Lenells origin-compatibility results suggested
a separate regularity mechanism. I checked their actual local integrability
proof and compared it with the HB boundary expansion in items 42–44.

The sharp analytic implication is: if `epsilon^(-gamma)*B(epsilon) -> c`,
`Re gamma <= -1`, and the unsubtracted B is locally absolutely integrable at
zero, then c=0. For c nonzero, convergence gives
`|B(epsilon)| >= |c|*epsilon^(Re gamma)/2` on a positive interval, contradicting
the real-power integrability threshold. Applying the same argument to
`B-c0*epsilon^gamma` forces c=c0, not c=0. Thus a subtraction prescription
determines a residue rather than deleting it. For HB this mechanism requires
both identification of the complete cokernel in an actual boundary coefficient
and source-produced integrability of the unsubtracted full physical expression.
Neither follows from the admitted scalar response, the singular left reader's
interior smoothness, or the subtracted cap estimate already proved here.
The survivor is this precise distinction between residue identification and
residue vanishing; no new HB regularity premise has been introduced.

The associated [July 2026 paper](https://arxiv.org/html/2607.19649v1) asserts
fifth-order origin decay in Proposition 3.8 and obtains weighted L2 admission
from it in Proposition 3.9. The corpus's `FokasLenellsOriginIntegrability` and
`FokasLenellsOriginCompatibility` instead expose an exact compatibility moment
and a unique pole subtraction. These are independently read corpus results,
not new proofs from this HB attack. They cannot supply HB boundary admission.
Likewise [Xu–Chu, September 2026](https://arxiv.org/html/2609.10637v1), equation
168 and its surrounding discussion, require puncture-contact matching and a
common continuation with coordinate poles; those properties are not a theorem
about the present theta source. Neither paper is a premise of the Lean work.

## Complete mixed quadratic residual and moving weights, 13 September 2026

The complete cubic coefficient is
`W0*(L K3 + E2(H,K2) + E3(H,H,H)/6) + W1(H)*(L K2 + E2(H,H)/2)`,
summed over all sixteen tensor entries. `W1` includes determinant and inverse-metric
derivatives. This is the existing `BMWeightedCorrectionDiscrepancy.coefficient_eq`.
The concrete attack is to discharge the second bracket from the actual source
correction, beginning with its scalar/vector coefficient.

The verified mixed source tensor includes the linear image of an ingoing contact
jet, whose only nonzero metric entries are
`Kcontact[0,A]=Kcontact[A,0]=s(s+1)/2 * B^2 * (r^2-1)/r^3 * S (*dS)[A]`.
The proposed complete mixed particular correction is this actual field plus
`BMModularCore.forcedMetricField`. The latter solves the negative of the
contact-corrected mixed tensor. The contact field's actual two-jet must first
be matched to its verified table, including the scalar's third derivatives.
Then linearity gives `L Ksv + E2(Hs,Hv)=0` in every component. Every moving
weight consequently contracts this mixed residual to zero pointwise.

This is an unswitched particular correction at one Xi occurrence and branch.
It does not identify the complete causal correction or solve the independent
scalar/scalar and vector/vector channels. Source-onset and boundary terms must
still be included before this cancellation applies to the complete causal action.

The new deep/method search covered 57,445 inventoried files (`partial=false`);
compiler metadata remained mostly pending, semantic coverage unmeasured. Its
candidate cubic coefficient and contact-amplitude lemmas were checked in source.
A broad recent Noether search led to [Baker, arXiv:2609.09170](https://arxiv.org/html/2609.09170v1).
Equations 389 and 551–555 retain second-derivative surface terms and use boundary
conditions for the integrated Bianchi identity. They do not establish this
problem's physical left-QNM boundary conditions. No paper claim is a Lean premise.

The endpoint calculation must include the contact. Set `u=1/r`,
`J=S(*dS)`, `A=fullAngularCovector`, `c=s(s-1)/4`, `d=s(s+1)/2`,
and `E=a^2 exp(2s(v+log(1+u)))`. The actual ingoing/inverse-radius
coordinate differentials give contact entries `K[v,A]=d E u(1-u^2) J_A`
and `K[u,A]=d E u J_A`, with their symmetric counterparts. Hence the
contact contributes zero at the conformal boundary `u=0`, but at `u=1`
its radial-angular entry is `d E J_A`. Adding the existing forced metric
gives horizon entries
`Ksv[v,A]=2s E(A_A-c J_A)` and
`Ksv[u,A]=E(-s A_A+s^2(s+3)J_A/4)`.
At `u=0`, the complete unrescaled radial-angular entry is
`-2s a^2 exp(2s v) A_A`. These are value identities, not differentiated
left-QNM flux identities. No universal nonzero value is asserted.

A second broad deep/method query covered 57,446 inventoried files with no
partial stages. The checked `ReflectionTateAnomaly` result supplies an
admissible reflection primitive only when the displacement already belongs
to the admissible subspace; `NormedInterventionTwoField` retains the current
of the residual in its filling identity. Neither supplies the missing HB
boundary admission or converts the even scalar/vector action to an odd one.

The contact-field realization and all sixteen mixed residual equations are now
closed in `BMMixedQuadraticClosure`: `contactField_jet`,
`contactField_einstein`, `mixedField_einstein`, and
`mixedField_secondVariation`. `independentField_secondVariation` proves the
corresponding identity for independently scaled original pure-mode directions;
`movingWeight_mixed_residual_zero` removes the full moving-weight contraction
of this residual. The complete 365-line scratch file passed without warnings
or raised limits. The isolated cached exact-leaf audit passed (2 jobs, leaf
7.6 seconds), and the umbrella import is wired. Source SHA256:
`ab60fa875d286d8835a02fc54aa44f3b0e781e9d4abaa9b4f338f19809be871d`.
The endpoint value calculation above remains paper-only.
No complete causal ++/+- correction identification or extinction is claimed.

## Contact-inclusive mixed Green current, 13 September 2026

The next source-level test is the actual mixed particular correction against
the original independent left QNM metric. Put `f=r²-1`, `E=B²`,
`A=fullAngularCovector`, `J=S(*dS)`, and `s=physicalRate`. Directly adding
the forced stream and its contact predicts
`T=E*(2s*A/r + s²*(1-(s+1)/(2r²))*J/r)` and
`R=2s*E*(A-s*(s-1)*J/(4r²))/f`.
The source-derived curl `∂time R-∂r T` should therefore be
`E/r²*(2s*(2s+1)*A + s²*(1-(s+1)*(2s+3)/(2r²))*J)`.
These formulas include the differentiated contact, not only its endpoint value.

For the original left radial mode `g`, its tortoise derivative `g'`, and
angular eigenvalue `λ`, its blocks at time zero are
`U=(f*g+r*g')*V`, `Vrad=-w*r*g*V/f`.
Its radial curl is `(λ*g/r-2*r*g-2*g')*V`, using the actual radial equation.
Consequently the volume-weighted radial Einstein current is
`sum_A (T_A*(λ*g/r-2*r*g-2*g')-Uscalar*curl_A)*V_A`.
The proposed proof identifies every value and derivative with actual metric
fields; it must not use the older toy minus-mode radial envelope in place of
the continued original left mode. All other current components remain in the
complete mixed-current formula and cannot be discarded by this radial identity.

A broad residue search found [Klyuev, arXiv:2608.01379](https://arxiv.org/html/2608.01379v1).
Section 4 proves a twisted trace using algebraic pole conditions, zeros of the
trace weight, its imaginary-shift law, and exponential decay. These conditions
are not identified with the HB nonlinear source algebra or physical clock.
The useful test is whether the complete HB integrand has a source-produced
pole/weight cancellation under translation; a formal trace analogy supplies
none of those facts.

The contact's radial action coefficient is
`s*(s+1)*E/(2*r^4) * (f*(λ-3*r^2+2*s+3)*g + r*(2*s+5-3*r^2)*g')`,
times the actual overlap `sum_A J_A V_A`. The sign follows from
`Tcontact*curl(left)-Tleft*curl(contact)`; both terms are required.

There is a source-derived angular identity. Let `H=fullAngularField`,
`S=literal source`, `R=literal scalar of the independent physical reader`,
`μ=parameter(q,branch)`, `λ=physical reader eigenvalue`, and `V=*dR`.
The established actual equations are
`ΔH=μ(H+S²/2)` and `ΔR=λR`, in the original hyperbolic metric.
Define the flat coordinate current
`G_j=λ R ∂j H-μ(H+S²/2)∂j R`.
Product differentiation cancels the two Laplacian terms exactly and gives
`div G=(λ-μ) sum_A A_A V_A-μ sum_A J_A V_A`.
Thus no scalar/reader boundary condition is needed for this local identity.
Integrating it retains the normal flux of this explicitly constructed current;
there is no justification here for setting that flux to zero.

Let `C` and `D` be the radial-current coefficients of `sum A V` and `sum J V`
respectively, obtained from the contact-inclusive blocks and curls above.
The exact consequence for the actual mixed radial Einstein action `I_r` is
`(λ-μ) I_r = C div G + ((λ-μ)D+μC) sum J V`.
This polynomial identity remains valid at `λ=μ`. It exposes the precise
remaining square/reader overlap and angular boundary flux; it does not give
their vanishing. The complete-current theorem must retain the other three
Einstein flux components. Causal onset selection, independent scalar/scalar
and vector/vector corrections, and the full cubic assembly remain outside
this mixed-particular identity.

The old odd-sector formulas use a test with time rate `-3-s`. The original
left metric instead has time rate `-physicalFundamentalFrequency(reader,side)`.
The Xi open-strip theorem and the actual frequency formulas give
`2 < Re(-physicalFundamentalFrequency-(-3-s)) < 4`, even for independent
source and reader occurrences. Therefore the old damped test's endpoint law
cannot be transferred to the actual left metric by identifying their rates.
The positive replacement is the actual continued left-mode current above,
with its independently derived radial equation.

These identities are now closed in the 533-line `BMMixedQuadraticCurrent`
leaf: `mixedField_orbit`, `radial_current`, `complete_current`,
`contact_radial_current`, `original_left_source_rate_gap`,
`original_left_ne_damped_source`, `angular_overlap_divergence`, and
`radial_current_angular_decomposition`. The full scratch check passed without
warnings or raised limits. The isolated cached `lake build` of this exact
leaf passed (2 jobs; leaf 44 seconds), and its umbrella import is wired.
Source SHA256: `d1cb09e411acd1951df0eb51c2ef6d061d82b5969c42f62e07fbc0fa75008464`.
The proof uses the original time-zero action slice and both continued radial
branches; no physical-clock translation or extinction is inferred from it.


## Original reader against the complete native cusp response, 13 September 2026

The current attack tests the actual boundary current from the preceding section,
not a substitute clock or damped test. Write H=P+N above height three, where P is
the literal particular cusp response and N is the native global response. The
native contribution is lambda R N_y-mu N R_y. Separate each cell product into
its mean product and its covariance; no Fourier mode is discarded.

Paper mechanism for the nonconstant part: differentiate Cov(N_y,R), use the
actual forced equation for N, and cancel the horizontal side flux by original
periodicity. Its derivative is
Cov(N_y,R_y)+Cov(N_x,R_x)+mu/y^2 Cov(N,R)+1/y^2 Cov(f,R),
where f is the complete original cutoff-subtracted forcing. The actual reader
and its first jets have polynomial bounds. Scaled Young inequalities bound both
the current and its derivative by constants times y^4 times the complete native
nonconstant energy plus y^(-2); the forcing term has its independently proved
arbitrary weighted bound. Both quantities are integrable, so the original
current has zero upper trace. Cov(N,R_y) tends to zero separately from the
rapid native nonconstant mass bound. This uses the ordered native current;
it is not an antisymmetric-current argument.

For the mean part, native energy kills the growing homogeneous coefficient.
The remaining root alpha has Re alpha<0. The physical reader has only the
constant power t=1-rho_reader/2 with 1/2<Re t<1. Their boundary product has
exponent alpha+t-1 with strictly negative real part. Every forcing-tail
remainder decays with arbitrary fixed complex height weight. Thus the native
Green-flux theorem has no imposed cusp boundary condition.

The particular P and the square S^2/2 remain. For a squared-source power k and
reader power t, their explicit contribution has coefficient
(mu/2)*sourceCoefficient*readerCoefficient*k*t*(t-k)/(k*(k-1)-mu)
and height exponent k+t-1. The following section now proves its exact
identification with the actual particular field and the integrated remainder.
No complete causal action, finite clock invariance or extinction follows from
native-flux decay alone.


The 1,039-line `BMMixedNativeReaderFlux` leaf now closes this mechanism for the
actual angular native response and independent original reader. The proof also
restores the real angular coordinates and the original centered cusp cell:

`sourceGreenFlux(q,r,b,Y)=particularGreenFlux(q,r,b,Y)+nativeGreenFlux(q,r,b,Y)`

for Y>3. Here the left side is the integral of the preceding leaf's actual
`angularGreenCurrent`, and the particular term is exactly
`integral [lambda R P_y-mu(P+S^2/2)R_y]`. The full source square, physical reader,
and their Fourier tails remain inside this expression. Both exact field values
and differentiated values are derived from the global cutoff assembly. The
native term tends to zero, including the source-selected stable coefficient.

Consequently the native angular response cannot provide a nonzero upper trace
to cancel the remaining particular/square cusp flux. For the complete HB chain,
the next boundary question is the value of this explicit survivor and its
cancellation with the remaining mixed overlap and other physical action faces
and channels. Neither a fixed-clock translation identity nor extinction is
obtained by deleting the native term. The causal switched corrections remain
separate from this unswitched particular mixed-current identity.

Validation: complete `lake env lean /tmp/hb-mixed-native-reader-flux.lean` passed
without warnings or raised limits. Isolated cached `lake build
GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedNativeReaderFlux` passed
(2 jobs; leaf 56 seconds), and the exact leaf's umbrella import is wired.
Source SHA256: `4a3fb68e028547a27c2f9ea86d7a4d9419fe1a134f5644b328d16be156c97a27`.

Final source/index check refreshed six changed modules. Global formal lint
reported two unrelated unwired modules: `Sieve.KloostermanGlobalCollisionCoprime`
and `ThetaCuspHawkingBMEvenSectorSkewLowBand`. The new leaf has no lint diagnostic;
its source, scratch, published artifacts and unique import were checked. The
isolated audit directory was removed, and no owned Lean/Lake process remains.


## Forced particular cusp flux and branch comparison, 13 September 2026

The preceding exact sourceGreenFlux decomposition now has an explicit evaluation
of its surviving particular term. Write rho for the source occurrence, sigma for
the independent physical reader, and keep either original source branch b:

- k_i=(2 rho,1,2-2 rho), c_i=(A^2,2 A D,D^2).
- mu=parameter(q,b), d_i=k_i(k_i-1)-mu.
- C=Lambda(sigma-1), t=1-sigma/2, lambda=t(t-1).

A,D are the literal principal Weyl coefficients. The original Xi equations prove
every d_i nonzero. The actual particular response and its derivative are
P(y)=sum_i (mu/2)c_i/d_i y^k_i and the termwise differentiated expression.

The exact identity is

    particularGreenFlux(q,r,b,y)
      = sum_i F_i y^(k_i-sigma/2) - (mu/2) T(q,r,y),
    F_i = (mu/2)c_i C k_i t(t-k_i)/d_i,
    T(q,r,y) = integral_cell (S^2-S_principal^2) R_y.

The full physical reader R and full square S^2 remain. Its proof first takes the
actual reader mean and derivative mean, then expands the particular response.
The coefficient identity uses lambda=t(t-1) and the exact resolvent denominator;
the contact S^2/2 is necessary for the factor k_i t(t-k_i).

For every fixed complex w, y^w T(q,r,y) tends to zero. The source's uniform bound
on y^(w+1)(S^2-S_principal^2), multiplied by the independently bounded full R_y,
gives an integrated bound C_w/y. The centered cell has length one. This proves
rapid decay after integration, without replacing R_y by its principal part.

Together with the complete native-flux theorem, this gives

    sourceGreenFlux(q,r,b,y) - sum_i F_i y^(k_i-sigma/2) -> 0.

The source-derived native response therefore has no missing upper trace capable
of changing these three explicit powers. This identifies the actual angular
cusp face of the unswitched mixed correction, not only a formal cap model.

At the cross power k=1 the exact coefficient is -A D C lambda, independent of b.
Thus subtracting the two unweighted source-branch fluxes leaves only the two
squared-Weyl powers, up to a vanishing remainder. This is a positive branch law;
its transfer to the complete action is not proved. The actual radial current
uses branch-dependent C_b=radialPairCoefficient(s_b,r,E_b,lambda,g,g',1,0),
D_b=radialPairCoefficient(s_b,r,E_b,lambda,g,g',0,1), and

    (lambda-mu_b) I_b = C_b div G_b
                         + ((lambda-mu_b) D_b + mu_b C_b) J dot V.

Consequently the unweighted branch difference is not yet a cancellation of
that radial pairing. The remaining overlap and all other causal faces/channels
must be assembled with these original coefficients.

A height exponent is zero exactly when i=0 and sigma=4 rho, or i=2 and
sigma=4-4 rho. Xi imaginary-part nonvanishing excludes the cross power and both
diagonal resonances. Hence the identified finite expansion has diagonal
constant coefficient zero without RH. This is a statement about its constant
coefficient; a raw flux limit or complete radiative extinction is not derived.

Corpus applicability audit: the deep all-view search for finite-power uniqueness
completed across 57,483 indexed files (47,808 Lean files), with source/compiler
freshness reported separately. It found HurwitzExp.expLin_linearIndependent and
its finite-type extension. Their checked source statements concern an exact
identity of entire functions of a complex variable. They do not directly supply
an asymptotic coefficient-extraction theorem for this physical flux. No
unverified search recipe was used as a proof. Broad arXiv searches returned
reciprocity and commutator literature, but no source-level fixed-clock identity
was extracted from those papers.

The hard HB obligation remains source-produced cancellation of the complete
nonlinear physical action at the original Hawking clock. The new result makes
one surviving boundary contribution explicit; it does not close that obligation.

Validation: complete `lake env lean /tmp/hb-mixed-particular-cusp-flux.lean`
passed without warnings. Isolated cached `lake build
GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedParticularCuspFlux` passed
(2 jobs; leaf 30 seconds), published the exact checked artifacts and removed its
temporary directory. The new leaf is wired into the RHTower umbrella without
building that umbrella. No proof-limit override or clock change was added.
Source SHA256: `4382c2828fe406b3bbda6c1c32e06005215394e4024f0cccfab541ea40e258f8`.

Final index refresh: three changed modules, zero removed. Global lint remains
blocked by the two unrelated unwired modules `Sieve.KloostermanGlobalCollisionCoprime`
and `ThetaCuspHawkingBMEvenSectorSkewLowBand`; no diagnostic names this leaf.
Exact source/scratch identity, artifact presence, unique import, whitespace and
scoped diff checks passed. No owned Lean/Lake process remains.

## Whole-orbit extinction test and complete-action estimate, 13 September 2026

The standing target remains source-produced extinction of the complete physical
left-QNM action, followed by the established clock-defect transduction. The
following tests use current corpus statements; they are not new Lean proofs.
No new primary conjecture is frozen and no physical-action identification is
assumed.

**Conjecture tested: positive averaging over the full FE--Schwarz orbit removes
the obstruction, even if the individual reader changes under reflection.**
The existing `BMFESchwarzOrbitPeierlsTrace` resolves this test in the canonical
packet Peierls model. For its four-sector trace, including repeated labels
with their prescribed multiplicities, it proves

```
Trace_n(q) = -4*(8*n+5)*normSq(mixing(q)),
Trace_n(FE(q)) = Trace_n(q),
Trace_n(conj(q)) = Trace_n(q).
```

For real weights `a,b` on the two conjugate reflection pairs, the exact
classification is

```
Trace_n(q;a,b) = -2*(a+b)*(8*n+5)*normSq(mixing(q)),
Trace_n(q;a,b)=0  iff  a+b=0 or Re(rho)=1/2.
```

Thus the orbit's FE and Schwarz invariance are already proved independently
of its zero value. Positive-total-weight averaging preserves the detector;
the identically cancelling signed character has zero total weight. This is
the positive survivor of the averaging failure, already formalized by
`hbXiPeierlsFESchwarzWeightedOrbitCubicTrace_eq_zero_iff` and its positive and
signed specializations. It does not assert an off-line Xi occurrence exists.
The canonical trace has not thereby been identified with the full original
SS/SV/VV physical action and its causal faces. Whole-route consequence:
replacing the local receiver by its symmetric orbit sum does not supply an
independent extinction law.

This does **not** exclude a separately proved odd reflection law for the
complete physical action. The current team card `hb-core-bridge-viability.md`
distinguishes that possibility from symmetry of the canonical packet model.
The abstract cyclic/skew cut has such a law when reflection exchanges its
two source probes. Applying it to the original marked left QNM still needs
the common physical pairing and all boundary contributions. In particular,
the physical test `E*(.,rho/2)` cannot silently become the old minus source
`E*(.,rho)`. The next orbit test must calculate the even reflection part of
the actual completed action, rather than declaring it equal to either model.

**Pivot tested: perhaps a source-derived positive conserved metric supplies
the missing orientation.** `BMRadiativeSourceFEPositiveHermitianMetricNoGo`
already constructs such a metric for its Green-dressed finite packet
transport `T`. It uses the actual conjugate-linear involution to set

```
H_T(x,y) = H_0(x,y) + H_0(Ty,Tx),
E_T(x) = E_0(x) + E_0(Tx),
E_T(Tx)=E_T(x),
E_T(x)=0 iff x=0.
```

The same corpus certificate retains the coherent cancellation of two
nonzero reflected raw channels *if* an off-line copy is present. This is a
universal implication, not a claimed witness to an off-line zero. The
positive survivor is the explicit positive antiunitary packet geometry and
its source-cocycle gain balance. Conservation of that energy does not
identify it with the complete clock-defect energy or orient the actual
left-QNM action nonnegatively. No clock was changed. Whole-route consequence:
constructing another invariant positive packet form would repeat a solved
problem; the missing physical inequality must concern the prescribed action.

**Actual source work still requiring compensation.** In the original incoming
SV--SV sector, `BMQuarticResponseWork` proves

```
W = c0*alpha*Q*A + c1*beta*Q*B + kappa*Q^2,
kappa = p*(s-t)*(p^3+25*p^2-28*p+20)/6 != 0,
p=s*t, s+t=-3.
```

Here `A,B` are the complete constructed angular responses,
`Delta A=alpha*(A+Q)` and `Delta B=beta*(B+Q)`. The nonzero coefficient
theorem applies to every actual Xi occurrence; it is not a claim that the
entire `W` or its physical integral is nonzero. The tested finite-cusp
identity retains `grad(test) dot current` as well as `test*W/y^2`.
Consequently a zero divergence integral or a zero local residual cannot
replace cancellation of these response and source-contact terms. The
independent SS and VV contributions and all other physical faces remain
part of the total task.

**Precise remaining estimate at the physical-action interface.** For a fixed
actual `q,n`, let `P_c(q,n)` denote the complete physical causal/left-QNM
orbit projection with the same normalization and multiplicities as `K`, at
an admissible common cutoff `c`, including its *original*
source-prescribed counterterms. This notation specifies a required
interface; no new definition of that completed physical action is supplied
here. It must retain both quadratic corrections, all scalar/vector
polarizations, spin two, varying metric weights, and every horizon, cusp,
characteristic and source-contact contribution. The clock stays fixed.

One sufficient quantitative interface is

```
|P_c-K| <= e_c,       Re(P_c) >= -eta_c,
e_c >= 0, eta_c >= 0, e_c -> 0, eta_c -> 0,           (PI)
K = -Sigma*normSq(D), Sigma>0.
```

Indeed `Re(K) >= Re(P_c)-|P_c-K| >= -eta_c-e_c`, so
`0 <= Sigma*normSq(D) <= eta_c+e_c`. Passing through the specified common
cutoff gives `D=0`. The independently proved source formula
`normSq(D)=(Re(rho)-1/2)^2*normSq(sourceCocycle(q))`, with the latter norm
strictly positive, then gives `Re(rho)=1/2`. This is a proof of the
implication from (PI), not a proof of (PI) or RH. No conditional Lean wrapper
was added for it.

The source already supplies the nonzero cocycle, positive susceptibility,
local action/correction exchanges and the separately admitted boundary
pieces recorded above. Neither the complete approximation bound nor the
opposite-sign estimate in (PI) has been proved here for the assembled
physical action. The existing invariant packet energy is not that estimate.
The next RH-bearing calculation is the sign or exact cancellation of the
complete source work after all of those pieces are assembled; more orbit
averaging, packet positivity or isolated boundary subtraction cannot
discharge it.

Search record: four all-view deep searches on complete clock translation,
Chern--Weil/transgression, theta heat/nonlinear action, and FE orbit traces
finished with `partial=false`, no reported errors, and 57,501--57,502 indexed
files. Most compiler metadata remained pending/source-only. The orbit
search proposed a cyclic-trace structure and `commutator_one`; neither
identifies the physical action with a trace of a commutator. Exact file
inspection supplied the orbit classification above. A Bottcher lexical
search returned 411 matches; the inspected Jacobi heat theorem concerns
theta derivatives, and no transfer of that evolution to the complete
Einstein action was established. Broad arXiv Noether, reciprocity, virial
and transgression searches did not supply such a transfer. The inspected
[nonlinear higher-spin Noether construction](https://arxiv.org/html/2410.15219v2)
distinguishes radiative evolution from the symmetry algebra at an already
non-radiative cut; it does not produce the required HB endpoint. The Baker
Noether paper was already recorded above and is not a new result of this
iteration.

Validation scope: documentation/source audit only; no new Lean declaration,
kernel audit, build, computation or proof-limit change in this iteration.

## Uncleared source-period and thermal-screening tests, 13 September 2026

The standing target remains literal theta source -> Xi occurrence -> retained
spin two -> complete physical causal/left-QNM action -> original fixed-clock
extinction -> RH. No replacement primary conjecture was frozen. The question
tested here is whether an independently proved source-zero mechanism controls
the uncleared physical radiative coefficient, including its nonlinear terms.

**Period-ideal test.** `BMNativePeriodPhysicalValue` gives, with `rho=q`,

    J(rho/2) = Lambda(5rho/2-1) Lambda(rho/2)^2 Lambda(1-3rho/2)/2
      + Lambda(rho-1) M(-rho/2).

The original Xi zero removes the forward correction only.
`nativePhysicalPeriod_eq_diagonal_iff` retains precisely `M(-rho/2)=0`, since
`Lambda(rho-1)` is source-proved nonzero. `BMNativePhysicalPairing` identifies
this with the actual quotient integral under its explicit `Re(rho)>1/2`
condition. This condition was not dropped or continued across discrete Xi data.
The proposed inheritance of the original vanishing period therefore has not
been proved. Its unresolved task is cancellation of the displayed survivors
against the other complete source terms, not omission of the cutoff moment.

The canonical completed vertex also has a proved factorization `XiC^2 * U`
with `U` an analytic unit on the physical strip (`BMCanonicalSpinTwoAmputation`).
Its first live multiplicity-matched jet is nonzero. The vanishing unamputated
vertex cannot be substituted for the normalized physical source. These are
existing corpus results, not new proofs from this turn.

**Cyclic-tree test.** `CubicPeierlsPolarization` already proves that symmetry,
cyclicity and a common skew propagator remove the mixed self-pairing but leave
`2 pairing(Delta Qpp, Qmm)`. It does not assert zero cross-pairing. For the
literal Einstein fields, `BMOnShellCyclicSource` keeps the differentiated
boundary divergence in cyclic exchange. For the actual independent left metric,
`BMLeftQNMCorrectionExchange.complete_mixed_exchange` keeps linear cubic work,
both exchanged correction/source works and both boundary defects. Thus this
test does not provide the missing complete-action cancellation. No duplicate
cyclicity wrapper was added.

**Exact-solution-family test.** The retrieved self-dual plane-wave model has
zero diagonal vertex, but its Hawking dilation continuum has the source-derived
variance coefficient `A^2 (1+rho/2) (rho/2)^2`, nonzero for nonzero amplitude
at every Xi occurrence (`SelfDualEinsteinDilationCarrier`). That module concerns
a principal self-dual germ and explicitly leaves the full non-self-dual
projection separate. No identification of the literal complete metric with an
exact Kerr-Schild, Kundt or other integrable nonlinear family was found or proved.
The generic plane-wave cancellation is not transferred to the full source.

**New primary-paper test.**
[Kubota, Manita, Motohashi and Watarai, submitted 7 September 2026](https://arxiv.org/html/2609.07326v1),
equations (8), (13)--(16), (24)--(27), cancels source-induced Matsubara poles in
a Kerr near-horizon expansion. Ordinary QNM poles remain in a separate factor;
the paper explicitly discusses coincident QNM/Matsubara frequencies as an
exception. Its power expansion produces simple source poles. This is neither
a complete nonlinear Einstein theorem nor a finite-time extinction statement.
No numerical part of the paper was used as proof.

The following comparison is our calculation, not a claimed result of that paper.
In the original BM rate variable, the horizon parameter is `c=1+w`. The marked
left reader has `w=-1-rho/2` or `w=-2+rho/2`; hence its imaginary part is
`-Im(rho)/2` or `Im(rho)/2`, respectively. Both are source-proved nonzero.
Consequently this reader does not meet an integral `c`-lattice zero of reciprocal
Gamma. By contrast, `BMCausalChannelEvaluation` puts the local mixed `+-`
source at `c=-(2n+2k+2)`. These are distinct spectral tests at the same physical
clock. A source-dependent frequency shift would change the problem.

There is a second nonlinear admission issue. The source-selected mixed BM
logarithmic companion has nonzero monodromy at every Xi copy, proved by
`d4BMXiMixedHorizonComplexMonodromyJump_ne_zero`. Its endpoint-sewn response
has a rank-one sheet jump times an explicit source projection
(`BMMixedHorizonLogarithmicCompanionGreen`). That projection has not been
identified with the complete nonlinear Einstein optical reader. In particular,
nonzero companion monodromy does not prove nonzero total radiative action.

Here is the exact additional test required if thermal pole screening is to be
extended through nonlinear logarithmic terms. Write `x=z-lambda`, and suppose
the source-identified local numerator has finite principal part

    H(z) = sum_{r=0}^R a_r x^(-r-1) + h(z),
    Pi(z) = sum_{k>=nu} p_k x^k,      nu>=1, p_nu != 0,

with `h` analytic. Multiplication of these local series gives

    coeff_{x^(-j)}(Pi H)
      = sum_{r>=0, r+1-j>=nu} a_r p_{r+1-j},       j>=1.       (TS)

For `a_R!=0` and `R+1>nu`, the most singular remaining coefficient is
`a_R p_nu`, at order `x^(nu-R-1)`. Thus pole removal needs at least `R+1`
zeros, or cancellation of the actual top source coefficient before screening.
For a simple zero, the residue is `sum_{r=1}^R a_r p_r`; in the first
logarithmic case it is exactly `a_1 Pi'(lambda)`. The elementary Mellin
identity `integral_0^1 y^(s-1) log(y) dy = -1/s^2` for `Re(s)>0` explains why
a logarithmic source term is a different cancellation test from a pure power.
Formula (TS) is a paper coefficient calculation, not a formalized identification
of the complete HB response. No nonzero projected logarithmic coefficient is
asserted for that response.

For a simple original QNM denominator `D`, the corresponding physical interface
is still `residue(N_total/D,w_q)=N_total(w_q)/D'(w_q)`, where analyticity of
`N_total` at `w_q` and `D'(w_q)!=0` must be established for the actual response.
`N_total` must retain both solved corrections, independent SS/SV/VV channels,
spin two, changing weights, and every horizon/cusp/characteristic/contact term.
If a derived thermal factor is nonzero there, factorization by it does not
produce `N_total(w_q)=0`. If numerator poles or logarithms remain, the full
coefficient equations (TS), with the denominator included, replace this simple
formula. Neither numerator vanishing nor its required full regularity is assumed.

**Whole-route consequence.** The new screening mechanism is worth testing at
the exact physical response, but the inspected source formulas do not supply its
spectral alignment or its nonlinear logarithmic cancellation. The fixed onset
also cannot erase every marked frequency: `BMFixedOnsetOvertoneSurvival` proves
nonzero cleared and continued onset factors at all sufficiently high original
overtones. This is a temporal-factor statement, not nonzero total action. The
decisive outstanding work remains a source derivation of the complete tested
coefficient, followed by a cancellation law for that coefficient. Neither more
radial normalization nor an assumed analytic quotient by Xi supplies that law.

**Search and method record.** Six all-view deep requests completed with
`partial=false`, no reported errors, and snapshots of 57,498--57,500 files:
uncleared period factor, nonlinear period kernel, cyclic causal trees, exact
nonlinear metric families, Matsubara response and logarithmic screening.
The broad Mellin/convolution hybrid request returned useful results but reported
interrupted text/source retrieval. Generated ingredient sets remained unverified;
several matched generic homotopy or symmetry terms without the required physical
identification. Those matches were not accepted as proofs. A June 15 primary
[semigroup sewing paper](https://arxiv.org/html/2606.16164v1), sections 5--7,
constructs quotient classes modulo cocycles and needs a separate representative
selection rule. No source-derived rule identifying its representative with the
original causal HB solution was found. No new Lean module or build was warranted
by these unclosed transfers; no owned Lean/Lake process was started.

## Whole-corpus transfer audit and relative-reader horizon test, 13 September 2026

Eight completed hybrid/deep requests searched all retrieval views over
57,487–57,489 indexed files, with no reported partial result or retrieval error.
Compiler coverage remains incomplete; a retrieved statement is not a checked
new theorem. Queries covered positivity, genuine finite-time extinction,
nonlinear Ward identities, flux correctors, gauge curvature, half-parameter
transforms, metaplectic mechanisms and relative-reader horizon admission.

The following transfer tests have definite outcomes from the inspected sources.

* `NonMarkovianLangevinKernel` supplies positive-definite Fourier kernels by an
  exact sum of nonnegative squared moduli. `HBFullCokernelKMSPassivityPolarityNoGo`
  realizes the existing negative complete cokernel by a passive two-level
  response. Thus this positivity mechanism supplies the already-known sign;
  its opposite sign has not been obtained from the literal source.
* `InverseResponseWardMechanics` gives
  `trace(Theta1 Theta2)=trace(M D1 D2 E)-beta(Theta2)`. Its zero conclusion
  requires both mixed affinity and annihilation of the derivative reporter.
  Neither has been established for the complete Einstein source and its
  physical boundary action. The boundary reporter must remain in the identity.
* `FokasLenellsCausalCauchySemigroup` gives a genuine nonzero finite-time kernel
  in the completed lower Hardy space, even though the encoded finite core has
  invertible evolution. This defeats an argument against extinction based only
  on invertibility on a finite core. Its positive replacement is exact upper
  Hardy membership of the evolved source. No identification of the complete HB
  causal cut with that kernel condition has been obtained. The separate
  `RadialAngularRecurrenceCompletionLaw` only yields asymptotic decay after an
  additional damping factor; it does not yield the requested original-clock
  finite-time statement.
* [Wang, arXiv:2606.05098, submitted 3 June 2026](https://arxiv.org/abs/2606.05098)
  constructs a skew flux potential for the periodic Lamé–Stokes flux after
  subtracting its effective mean. Its divergence calculation uses the cell
  equations and interface traction continuity. Mean subtraction and the
  interface terms cannot be omitted when testing transfer to HB. The possible
  survivor is a source-owned mean-plus-skew-potential-plus-contact identity;
  no such complete HB identity was derived by this audit.
* `SelbergThetaEisensteinProbes` supplies finite probe separation, not the
  required physical half-parameter action intertwiner. `BornSectorExchange`
  concerns half-integral level cosets, not this spectral half shift. The
  inspected metaplectic results likewise do not supply that intertwiner.

The next conjecture was that two original horizon-normalized radial modes at
one unchanged physical frequency have a sufficiently small difference to
remove the reflected-reader boundary term. The actual definitions refine this
conjecture as follows. Put `rho=q`, `q*=1-q`, `u=(rho-1)/2`,
`w=physicalFundamentalFrequency q side`, and
`F_r(z)=gaussFactor w (physicalRadialFrequency r) false z`. Both `F_r(0)=1`.
The original Gauss equation at zero gives

    (1+w) F_r'(0) = [w(w+1)+scalarQ(u_r)]/4,
    F_q'(0)-F_q*'(0) = (rho-1/2)/[8(1+w)].

This coefficient is nonzero at every actual Xi occurrence, independently of RH.
The radial leading terms cancel, but the full angular fields do not disappear:

    F_q* V_q* - F_q V_q
      = F_q (V_q* - V_q) + (F_q* - F_q) V_q*.

Here `V_r` is the original full coexact reader, including all Fourier terms.
The limit is `V_q*-V_q`, not zero by radial normalization alone. The coexact
reader equations and the nonzero original scalar Weyl mean are the proposed
source-level route to proving that this angular difference is nonzero somewhere.

There is also a direct radial boundary test. With actual horizon modes `g_r`
and their tortoise derivatives, set `W=g_q* g_q' - g_q g_q*'`. At the horizon,
the predicted normalized limit is

    W / [z * (z^(w/2))^2] -> (rho-1/2)/[4(1+w)],

since `dz/dt=2 z radialUnit(t)` and `radialUnit(t)->1`. Thus equality of the
zeroth Gauss coefficients does not annul the original Green boundary current.
The physical frequencies obey `-2<Re(w)<-1`, so a zero raw Wronskian limit
cannot be inferred from the first-order radial gain either.

These are source-specific boundary tests, not a construction of the complete
nonlinear action or an extinction proof. A nonlocal spatial transmutation
would still have to carry this boundary term and its nonlinear product defect.
[Sitnik's transmutation survey](https://arxiv.org/abs/1012.3741) confirms that a
Volterra intertwiner requires a kernel equation, a diagonal condition, and a
lower-endpoint Wronskian condition; no such actual HB kernel was constructed.
Formal status: the complete scratch file passed `lake env lean` without warnings.
The source-specific radial coefficient, raw no-finite-limit theorem, unique
subtraction and decaying remainder, actual derivative identification, and full
coexact stream trace are in `ThetaCuspHawkingBMRelativeReaderHorizon.lean`.
The proposed nonzero-coexact-difference argument was not formalized by this
leaf; the proved full-stream limit retains that difference explicitly. The
isolated cached `lake build
GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRelativeReaderHorizon` passed
(2 jobs; leaf 247 seconds). Artifacts were published under the source hash
`b93e554dd5330b2a91296bbbfe48dd8e22e623fedf8b33233bacc924e7f36c3e`,
the temporary audit directory was removed, and the unique umbrella import was
wired without an umbrella build. No owned Lean/Lake process remains.

Final index refresh completed (three changed files). Global lint reports three
unrelated unwired modules: `Sieve.KloostermanGlobalCollisionCoprime`,
`ThetaCuspHawkingBMEvenSectorSkewPlateauOdd`, and
`ThetaCuspHawkingBMOriginalGreenBoundary`; no diagnostic names this leaf.
Scratch/source identity, published artifacts, unique import, whitespace and
scoped diff checks passed. Other agents' unfinished modules were not modified.

The second pass extracts a stronger positive survivor from the radial no-go.
Write `a_q=(rho-1/2)/(4(1+w))` and

    H(z)=2(1-z)^(1/2)[F_q*(z) F_q'(z)-F_q(z) F_q*'(z)].

The actual dressing and the original tortoise derivative give the exact identity
`W=z^(w+1)H(z)`, with `H(0)=a_q`. The continued Gauss derivatives prove `H`
differentiable at zero, so `(H(z)-H(0))/z` has a finite limit. Because
`Re(w+2)>0`, the source-derived subtraction satisfies

    W-a_q z^(w+1) = z^(w+2) [(H(z)-H(0))/z] -> 0.

This subtraction is unique among constant multiples of the leading power:
if `W-c z^(w+1)` has any finite limit, multiplication by `z^(-w-1)->0`
forces `c=a_q`. In particular the unsubtracted current has no finite limit.
No frequency has been moved. This identifies an actual boundary prescription
and its zero remainder, not an assumption of a zero raw boundary current.
Transfer to extinction still requires identifying the complete physical action
with this prescription, and controlling the remaining angular, causal, contact,
metric-weight and independent polarization contributions. The calculation does
not provide those identifications.

Whole-chain action check: `BMPhysicalRadialNorm` identifies the actual radial
residue with a source/angular factor times
`Gamma(w) Gamma(3/2)/(2 Gamma(w+3/2))`; its existing theorem proves this norm
factor nonzero at every original Xi fundamental frequency. Thus zero of the
new renormalized boundary remainder cannot be substituted for zero of the
physical residue. The latter still requires the actual remaining factor to
vanish or to cancel in the complete sum of channels.

A ninth complete deep all-view search covered 57,492 indexed files. Its
unverified ingredient set retained an unresolved energy-sign obligation.
`DeningerCalderonWittCotangentNoether` supplies a fixed cotangent action which
annihilates boundaries of its own square-zero differential; its source and
reporter have not been identified with this physical HB action. No universal
fixed-clock extinction theorem was obtained from this search.

## Method-directed whole-route reassessment, 13 September 2026

Applied `docs/meta/stroke-of-genius-method.md` and
`docs/meta/scientific-method.md`. The current radial subtraction is a `[BRIDGE]`,
not the primary extinction conjecture. It is useful only as an identified
boundary contribution of the physical action; extending its special cases does
not itself attack the missing source law.

Written interrogation:

* **Where does this proof know that Xi vanishes?** The relative radial proof
  uses the existing physical parameter definitions, reflection, the open-strip
  bounds and nonrealness. Its decisive algebra does not use a vanishing theta
  Mellin period. Therefore its zero remainder cannot be the RH-bearing step.
* **What is being removed?** A source-derived horizon coefficient. Keeping it
  exposed a unique subtraction, not invariance of the complete action. The
  subtraction must remain part of any subsequent variation or gluing identity.
* **Which correspondence is still informal?** The physical causal/left action
  and the reduced complete cokernel remain different until their complete
  independent-channel comparison is proved. Boundary-current identities also
  remain different from vanishing of the nonzero-norm physical residue.
* **What changed in the current team corpus?** `BMOriginalModularGreen` now
  proves zero diagonal/reflected modular finite part for the original causal
  potential at fixed null coordinates. `BMOriginalAngularCurrent` expresses
  the actual Einstein angular current as three Green transfers of spacetime
  derivatives, retaining the source factor `R`. Passing from the former to the
  latter needs the differentiated prescription, including its parameter tails;
  it is not an immediate substitution.
* **Am I working on the right problem?** Completing the isolated radial audit
  records a finished bridge. The next priority is an identity that uses the
  literal vanishing Xi/theta period in the complete nonlinear source, or a
  decisive falsification of such an identity. Further radial refinements are
  deferred unless they discharge a named obligation of that identity.

Three new full-corpus deep requests test period-annihilator preservation under
nonlinear assembly, cyclic homotopy transfer of source equations, and complete
finite-clock action laws with independent polarizations and contacts. A possible
exact factorization of the physical action by the original theta period is a
proof target, not an established law: dividing by Xi and assuming the quotient
regular at its zeros would merely restate the missing result. A legitimate
factorization must construct its coefficient from the original source assembly
and prove its regularity independently. This has not been frozen as a new
primary conjecture; the novelty/distance and source-evidence gates remain open.

The three requests finished over 57,498 indexed files. Cyclic transfer returned
without partial coverage; its proposed ingredients still assumed zero action
and preserved gauge symmetry. Period-ideal and complete-clock searches returned
usable hits but reported partial results from malformed local-model output;
period-ideal decomposition also timed out. Their missing synthesis is not
evidence that a source law does not exist. Candidate applicability was checked
against source files rather than accepted from the generated ingredient lists.

The most relevant new tests are:

| Candidate mechanism | Actual source evidence | Whole-route consequence |
| --- | --- | --- |
| A closed Ward annihilator forces the radiative coefficient to vanish | `VortexWardOperator` proves the exact uncleared residual is the degree-zero boundary minus a resonance series. Multiplying by the denominator kills the resonance series; Euler differentiation then kills the constant. | The cleared equation can erase precisely the resonant quantity the left-QNM action must detect. The actual uncleared resonance/contact coefficient must be calculated; a cleared source equation is insufficient. |
| Solved lower-order corrections force the next obstruction to vanish | `TateFractureObstructionBianchiAmplitudeLaw.exists_firstObstruction_zero_higherObstruction_ne_zero` gives a closed counterexample. `MinimalLawLeadingJet` preserves the first surviving operation under an equivalence satisfying the full triangular morphism equations. | Solved `++` and `+-` equations and invertible changes of variables do not supply extinction. The source-specific next obstruction, with its physical boundary domain, remains decisive. |
| A general higher Noether theorem already supplies the missing identity | `CyclicMaurerCartanLaw` requires Bianchi and cyclicity as fields; its gauge-annihilation theorem applies to `twisted alpha epsilon`. | One must derive the actual boundary-corrected pairing and identify the physical clock variation as that direction. Instantiating the structure with those unproved fields would assume the missing content. |

The vortex example is tied to an independently checked primary paper,
[Brunner–Cheng–Jockers, submitted 8 September 2026](https://arxiv.org/abs/2609.09298),
which studies difference-operator Ward identities for supersymmetric vortex
partition functions. The inspected Lean recurrence preserves its boundary and
singular-denominator correction. No identification of its degree-rescaling
variable with the original HB physical clock has been established.

A broad annihilator search also found
[Asgharzadeh, revised 3 September 2026](https://arxiv.org/abs/2601.20596).
Its ideal/Ext annihilator containments concern the appropriate grade in a
Noetherian local setting; extra closure statements have explicit structural
hypotheses and counterexamples. No such module or graded source identification
has been constructed for the complete nonlinear HB action. The paper therefore
does not justify automatic propagation of the theta-period ideal through the
higher source assembly.

An additional live-team update changes the proposed integration strategy:
`BMOriginalGreenBoundary.original_current_boundary` has already transferred the
three spacetime-derivative Green terms to explicit radial and temporal endpoint
currents minus `readerRemainder`. That remainder retains the radius-weight
derivative and both ordered mixed reader derivatives. Thus the next use of the
modular finite-part theorem should start from this finite-cut identity, not by
assuming that differentiation commutes with an infinite-cutoff limit. No
vanishing of its endpoints or remainder was inferred here.

## Original radial weights and the surviving triple-source overlap, 13 September 2026

The next attack combines the identified cusp face with the remaining mixed
angular overlap. With K=(S^2/2) grad R, the literal reader equation gives
`div K=J dot V+lambda*S^2*R/(2*y^2)`. Thus, with the original coefficients
C,D and Omega=(lambda-mu)D+mu C,

    (lambda-mu) I_r = div(C G+Omega K)-Omega*lambda*S^2*R/(2*y^2).

This retains a full triple-source density and its boundary current. The
conjecture that original radial weights kill Omega must be tested, not imposed.

The current corpus's FundamentalRadialModes supplies the original mode
`g=z^(w/2)/r` at either fundamental frequency, with both radial normalizations
agreeing. Since r'=r^2-1 and z'/z=2/r, its derivative is
`g'=(w+1-r^2)g/r`. Together with lambda=(w+1)(w+2), the actual left blocks
reduce to `Tleft=w*g`, `curl(left)=w*(w+1)*g/r`.

The now-checked contact-inclusive radial coefficients are

    C = (w E g/r^2) * 2s(w-2s),
    D = (w E g/r^2) * s^2*(w+(s+1)*(2s+2-w)/(2r^2)).

The original eigenvalue difference factors as
`lambda-mu=(w-2s)(w+2s+3)`. Xi open-strip bounds prove
`Re(w-2s)>0` and `Re(w+2s+3)<0` even for independent source and reader.
This permits the actual resolvent division without imposing nonresonance.
It does not make the surviving square/contact coefficient vanish. The exact
original-field identities and the resulting no-go are checked below.

The original-field calculation and no-go now pass the complete Lean scratch
check. Define

    P0 = s*(w+2s+3)*w + 2*(2s+1)*(2s+2),
    P1 = s*(w+2s+3)*(s+1)*(2s+2-w)/2.

The actual coefficient is

    Omega = (w E g/r^2)*(w-2s)*s*(P0+P1/r^2).

For unit source amplitude, every factor outside the last bracket is nonzero
at every interior radius. Both original continued radial normalizations give
the same nonzero g. The source strip proves s, s+1, s+2 and 4s+1 nonzero;
the independent frequency gaps prove w-2s and w+2s+3 nonzero.

Conjecture that Omega vanishes everywhere: rejected. Its positive survivor is
an exact zero-locus law. P0 and P1 cannot vanish together. Indeed P1=0 would
force w=2s+2; after this substitution P0=(2s+2)(4s+1)(s+2), whose factors are
source-proved nonzero. Therefore Omega=0 exactly when P0*r^2+P1=0, and this
can hold at at most one interior radius. The general amplitude law is
Omega(a)=a^2 Omega(1); its zero criterion is a=0 or the same radial equation.

The second Green identity is also checked on the actual literal fields:

    (lambda-mu) I_r + Omega*lambda*S^2*R/(2*y^2)
      = C div G + Omega div K,       K=(S^2/2) grad R.

This is the exact local boundary/bulk comparison required before integration.
No source or reader Fourier term, differentiated source contact, or radial
normalization was removed. It does not set either boundary flux to zero,
establish the causal switched correction, or prove a nonzero integrated
coupling. For the complete HB chain, extinction must now be tested through the
full admitted boundary/triple-source balance and the other nonlinear channels;
pointwise vanishing of these radial weights cannot supply it.

Search audit: three deep all-view requests completed over 57,485 files. The
fundamental-profile search recovered the terminating Gauss-series mechanism and
original horizon/normalizable normalization equality used here. Generic
polynomial/secular-root results were unnecessary after the source-specific
linear equation was derived. Broad single-word arXiv queries did not return a
new June–September 2026 identity applicable to this source. The primary abstract
of [Popkov et al., arXiv:2408.09302](https://arxiv.org/abs/2408.09302) concerns an
XXZ steady state with boundary dissipation and a modified dispersion relation;
no unchanged-Hawking-clock theorem was transferred from it.

Validation: complete `lake env lean /tmp/hb-mixed-radial-overlap.lean` passed
without warnings after reducing imports to the required mixed current and original
left-horizon factor. Isolated cached `lake build
GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedRadialOverlap` passed
(2 jobs; leaf 34 seconds); artifacts published under a source-hash guard,
temporary directory removed, and exact leaf wired without an umbrella build.
Source SHA256: `2b8fef587ca670b1bcbf329e2731ef978bf760e98b956a7937e8fc29c3bfaea4`.

Final index refresh: three changed files. Global lint reports the same two
unrelated unwired modules, `Sieve.KloostermanGlobalCollisionCoprime` and
`ThetaCuspHawkingBMEvenSectorSkewLowBand`; no diagnostic names this leaf.
Exact source/scratch identity, artifact presence, unique import, whitespace and
scoped diff checks passed. No owned Lean/Lake process remains.

## Combined pairing and causal phase tests, 13 September 2026

Target remains literal theta → Xi occurrence → retained spin two → complete
physical causal/left-QNM action → original fixed-clock extinction → RH.
This pass tested whether the newly available scalar pairing closes the
actual even reflection part, then whether a causal spectral sum rule supplies
the missing sign or phase constraint. Neither test produced extinction.
These are source audits and applicability results, not new Lean proofs.

**First test: use the zero diagonal modular finite part as zero physical
projection.** The new `BMOriginalScalarPairing` instead proves, for the actual
source `F=D4BMOriginalAngularGreen.source q branch amp p v`,

```
C_Y(F,r) + mu_r*S_Y(F,r) = Phi_Y(F,r),
mu_r = physicalAngularParameter(r)^2 - 1/4,
C_Y = integral_D(Y) coexact(F) dot coexact(S_r),
S_Y = integral_D(Y) F*S_r/y^2.
```

Its proof derives the divergence of `F*grad(S_r)` from the literal reader
equation and modular covariance. It retains the actual curved domain,
causal source, and Fourier tails. For `r=q` or `r=FE(q)`, its limit is

```
lim_{k→∞} [C_exp(k) + mu_r*S_exp(k) - Phi_nonconstant(k)] = 0,
```

at fixed `p,v>=0`. The theorem neither assigns separate limits to `C_Y,S_Y`
nor sets either to zero. Thus the attempted extinction inference does not
follow. The positive survivor is the exact original-source derivative
transfer and its prescribed subtraction, already formalized in that module.
It can eliminate a derivative pairing only while retaining its scalar work
and the same boundary subtraction. It supplies no joint time/cusp/horizon
limit interchange.

The actual left metric equation also does not complete the cancellation:
`BMLeftQNMCorrectionExchange.complete_mixed_exchange` removes the test's
Einstein residual but retains cubic linear work, both correction/source
pairings and both differentiated boundary defects, with independent scalar
and vector amplitudes. No complete SS/SV/VV action was replaced by `C_Y`.
Whole-route consequence: the even reflected physical action is still
unevaluated, and estimate PI above still needs both physical identification
and the source-produced opposite-sign bound.

**Second test: obtain that bound from a causal scattering sum rule.**
[Han et al., submitted 11 August 2026](https://arxiv.org/abs/2608.10427)
derive logarithmic-modulus bounds after a reference-domain delay correction,
with explicit analyticity, passivity, transparency and angular-derivative
conditions. A coherent projection must lie in one common-delay eigenspace.
Their separate lossless phase bound requires a spectral-counting condition;
additional resonant phase can exceed that count. These statements do not
derive a nonlinear Einstein action or its fixed-clock extinction.

The current corpus gives a direct test of the missing phase information.
`CausalHardyIndexEndpoint` attaches a single inner factor to each upper XiC
resonance. Its multiplier is isometric, but its outgoing range is precisely
the orthogonal complement of a nonzero source-selected Szego kernel line.
The defect dimension and winding charge both equal one. Universal removal
of that defect is an explicitly marked RH-equivalent open producer. These
are statements conditional on an upper resonance, not an asserted witness.
The positive survivor is this exact phase-sensitive index, already proved
in Lean. A new modulus/passivity lemma would not remove it. Transfer of any
spectral sum rule to the complete HB action, with all contacts and the
original common clock, remains unproved.

**Repetition check.** The retarded variational-elimination idea revisits
fact 17: a symmetric effective action requires a common variational domain;
transposing a retarded inverse retains advanced and boundary data. The broad
reciprocity search also recovered
[Vu et al., revised 6 September 2026](https://arxiv.org/abs/2609.04169),
whose inverse-symmetry constraint concerns the shared drive/read block.
This paper was already used by the team. Its symmetric-operator hypothesis
does not identify the original marked reader or admit the causal boundaries.
Neither is a new extinction mechanism.

The same check applies to `BMOriginalGreenBoundary`: its actual finite
rectangle identity is already known. Substituting the elementary eigen-reader
into the paper derivation in `hb-physical-mode-action-contact.md`, section
“Moving the spacetime derivatives to retained boundaries”, leaves

```
J_angular = partial_R(a*K) + partial_p(b*K) + c*K,
a=w*ell/R^3, b=ell_R/R^2, c=(mu-2)*ell/R^4.
```

The leftover is not automatically zero; the four oriented edges remain.
That specialization is recorded there as analytical, not a freshly checked
Lean theorem here. It does not settle the complete nonlinear action.

Search coverage: four new deep all-view searches covered 57,505–57,509 files.
The retarded-variation query reported partial retrieval (worker cancellation
and malformed decomposition/filter output); the other three reported no
retrieval errors. Candidate statements, source arguments and proposed
ingredient sets were inspected. Compiler coverage remained predominantly
pending; search results were not treated as fresh kernel checks. Broad
arXiv searches included doubling, variation, winding, transgression and
reciprocity, with recent-paper queries broadened when empty. No numerical
experiment, proof-limit override, axiom audit, Lean module or build was added.
All owned search commands completed; no owned Lean process was started.

The unresolved task is unchanged: derive cancellation or an opposite-sign
estimate for the complete, source-selected marked action from the original
equations, retaining every correction and boundary. These tests provide
no justification for promoting covariance, passive losslessness, or a zero
subtracted Green defect to that theorem.

### Independent-reader contact test — 13 September 2026

**Question before formalisation.** Does the zero resonant translation moment
of the literal derivative contact remain zero at an independent physical
reader? The source clock and its finite step remain fixed. Changing the
test weight is not a correction to that clock.

Write chi for `Real.smoothTransition`, v for the original source rate,
w for the independent reader exponent, z=v-w, and h>=0. For the actual
source/contact shape f(u)=(A chi(u)+B chi'(u)) exp(vu), define

```
M = integral[-h,1] exp(-wu) (f(u+h)-exp(vh)f(u)) du,
J(z,h) = integral[-h,1] exp(zu) (chi(u+h)-chi(u)) du,
H(z) = integral[0,1] exp(zu) chi'(u) du.
```

Paper candidate, with no covariance premise:

```
M = exp(vh) (A-zB) J(z,h),
z J(z,h) = (1-exp(-zh)) H(z).
```

Proof: the compact difference D(u)=chi(u+h)-chi(u) is zero at both
endpoints. Integration by parts gives integral exp(zu) D'(u)=-zJ.
Translation and the support of chi' give the same integral as
(exp(-zh)-1)H. Substitution gives both identities. At z=0 the existing
source theorem gives M=h exp(vh) A; dividing by z and then setting z=0
would lose this resonant mass.

The intended actual-source attachment keeps the full square potential,
gradient channel, angular response and half-square wave image. Its contact
coefficient B is the existing `fullSourceOnsetPulse_transition` coefficient.
For the wave-image difference it predicts exp(vh)(lambda A+zB)J, since
that source identity has contact coefficient -B.

**Whole-route test.** A zero moment at w=v cannot yet be used in the
marked left-QNM action. The new identity must retain the contact and expose
the exact cancellation demanded of the spatial action. It will not by
itself identify the complete SS/SV/VV action or cancel horizon, cusp and
characteristic fluxes. Paper derivation above is pending a Lean check;
no extinction claim follows from it.

## Quartic current from the full shift-two source identity

Let `S` be the literal scalar at an actual Xi copy, `mu=Delta S/S`
(meaning the already proved equation `Delta S=mu S`, with no division by
`S`), and let `U` be the original restored response `(2-Delta)U=S^2`.
All contractions below are complex bilinear in the original hyperbolic metric.
Put `Q=S^2`, `E=<dS,dS>`, and `L=<dS,dU>`. The corpus proves
`[dS tensor dS]^TF + mu HessTF(U)=0` for these actual fields.

The resulting first-derivative quartic current is

`J = mu ((E+mu Q) grad U - 2 L grad S)`.

Its exact local identity is

`div J = E^2 - mu^2 Q^2 + 2 mu^2 Q U`.                  (QS1)

Proof: differentiate the displayed current. The two terms containing
`mu S L` cancel by `Delta S=mu S`. Symmetry of `Hess S` cancels the
two mixed Hessian contractions. What remains is
`mu (E+mu Q)(2U-Q) - 2mu Hess U(grad S,grad S)`.
Contracting the proved tensor identity with `grad S` twice gives
`mu Hess U(grad S,grad S) = -E^2/2 + mu(2U-Q)E/2`.
Substitution proves QS1 without dividing by `mu`, `S`, or an Xi value.

On every finite smooth angular domain, the right side integrates to the
outward flux of this same `J`. At an upper horizontal edge `y=Y`, the
oriented flux density in the original coordinates is exactly
`mu ((E+mu Q) U_y - 2 L S_y) dx`; the factors `Y` from the unit normal
and `1/Y` from arclength cancel. Other edges retain their outward normal.
No infinite-cusp limit or deletion of this flux is asserted here.

The source product rule also gives
`Q Delta Q = (4/3)mu Q^2 + (1/6)Delta(Q^2)`. Thus

`(Delta Q)^2 - (16/3)mu^2 Q^2 + 8mu^2 Q U`
`  = div (4J + (2/3)mu grad(Q^2))`.                    (QS2)

This is a candidate control of the quartic source terms involving the actual
shift-two inverse, not an extinction theorem. A complete-action reduction
must still account for the independent target-shift inverse, both causal
corrections, changing metric weights, the marked left reader and all physical
faces. In particular, QS1/QS2 are bilinear identities, not positivity bounds
for a cusp-subtracted Hermitian spectral measure. Lean verification of QS1
is the next check; no complete-action factorization is claimed.

For any smooth independent scalar reader `R`, the exact projected form retains
the bulk reader work:

`div(R J) = R (E^2-mu^2 Q^2+2mu^2 Q U)`
`  + mu ((E+mu Q)<dR,dU> - 2L<dR,dS>)`.               (QS3)

Therefore a projection of QS1 is a boundary flux **minus** this explicit
reader work. Neither the source equation nor tensor vanishing deletes it.
The actual coexact left mode is built from the derivative of its own scalar
Eisenstein reader, so identifying this term in the complete source action is
necessary before QS1 can be used for extinction. This is an unresolved
coefficient/field identification, not an additional vanishing premise.

## Experiment-led complete-action tests, 13 September 2026

No fixed-clock extinction or impossibility theorem was obtained in this pass.
The target remains the complete original causal/left-QNM action, with the clock
unchanged; neither a local cancellation nor failure of a proposed mechanism
settles this target.

**Theta seam transfer.** The exact finite-shell Fourier theorem gives
`b^2 C_(P_N) -> -P_N'(0)` and `b^2 C_(Phi-P_N) -> P_N'(0)`.
Its mechanism is `Phi'(0)=0` and two integrations by parts. The stronger
proposed transfer to the physical action was not proved: the raw source's
full FE exchange is already established, while the marked left reader
changes parameter and the complete mixed exchange retains both
correction/source contractions and boundary divergences. No commutation of
this Fourier endpoint cancellation with nonlinear assembly was derived.
The tail theorem remains a constraint on approximation, not an extinction
producer or a newly proved failure of HB.

**Source-specific sign test.** The physical spectral-sign search recovered
the complete Peierls polarization and optical-section receivers. Their
displayed source-response and reciprocity premises remain necessary; none
was inserted as a source theorem. The already proved finite-KMS realization
has exactly the canonical cokernel's nonpositive polarity. The January
[matrix passivity paper](https://arxiv.org/html/2601.04796v1), definitions
1 and 6, requires a nonnegative storage function and an admitted supply
inequality. Its interconnection proof cancels supplies under specified
input/output relations. Those relations and the opposite physical HB sign
were not derived. No new no-go or positive form is claimed.

**Arithmetic and retarded-assembly alternatives.** A Hecke/correspondence
search did not yield a literal nonlinear Einstein-action intertwiner. Its
proposed product-preservation obligation was not discharged. The August
[Stratonovich–Weyl/Magnus paper](https://arxiv.org/html/2608.21328v1),
equation (56), explicitly retains the emission/absorption interference
integral in addition to the conservative bracket. Thus representing an
action by nested brackets is not a proof of its radiative matrix element's
vanishing. No map from that asymptotic scattering construction to the
original HB QNM pairing was established.

The live corpus supersedes the older experiment report's local SV frontier:
`MixedQuadraticClosure.independentField_secondVariation` and
`movingWeight_mixed_residual_zero` were already recorded above. They must be
used as inputs, not reported as new progress or left as reconstruction tasks.
The actual complete-action estimate (PI) above is still unproved.

Search artifacts: five new deep requests (theta seam, mixed-current
projection, physical spectral sign, Hecke nonlinear clock, Magnus assembly)
finished with `partial=false`, 57,585 inventoried files and semantic coverage
`not_measured`; candidate statements, source arguments and ingredient sets
were inspected. A lexical full-cokernel search retrieved the existing KMS
polarity theorem. The files are in `formal/.lake/hb-extinction-scratch/` under
the corresponding `extinction-` names. No numerical experiment, Lean build,
new Lean declaration, proof-limit change or axiom-print audit was performed.
All six owned search handles terminated.

## Fixed-step covariance and variational-energy test, 13 September 2026

**Outcome:** no extinction or impossibility theorem. The original Hawking clock,
literal source, independent polarizations and complete-action target remain fixed.

The attempted finite-step proof would commute source FE through the complete
nonlinear evolution, then use the finite-clock classification. The corpus already
proves that such covariance differentiates at vacuum to covariance of the
prescribed linear clock, even using only real amplitude rays. Thus this remains
an RH-strength source obligation; higher-order correction terms cannot repair an
off-wall first variation. This does not exclude deriving the covariance from
the actual equations. The physical nonlinear evolution and its FE intertwining
have not been supplied by the packet equivalence.

The alternate energy proof would require a source-produced nonnegative quantity
whose first surviving amplitude coefficient is a positive multiple of the real
complete radiative action. If `E(eps)>=0` and
`E(eps)=eps^4*c*Re(K)+o(eps^4)`, with `c>0`, dividing by `eps^4` and taking the
limit gives `Re(K)>=0`; the established negative clock-defect factorization would
then force extinction. This is a receiver, not a derived HB energy law. An
unremoved quadratic coefficient prevents this inference, and subtracting that
coefficient does not preserve nonnegativity automatically. No new conditional
Lean wrapper was written.

The exact factor `XiC(z)^2` in canonical spin-two amputation is spectral. It
does not establish the needed vanishing of lower coefficients in metric amplitude.
These are distinct variables in the inspected definitions. The contemporary
boundary-completed Noether-charge paper likewise leaves global positivity and
orthogonality as inputs; its compact spherical local result has not been
transported to the original cusp geometry or the marked complex left reader.
See own facts 101–102 for exact sources.

An exact nonlinear-family alternative was also checked against recent
Kerr–Schild and optical-seed constructions. The inspected Kerr–Schild ansatz
requires a null rank-one metric deformation; the Birkhoff seed construction
requires spherical vacuum geometry. No identification of the literal independent
scalar/vector metric with either family was established. Their existence is not
a full HB reconstruction or a radiation-annihilation result. Sources:
[Kerr–Schild equations (19)–(20)](https://arxiv.org/html/2602.16905v1),
[optical-seed setup](https://arxiv.org/html/2604.09830v2).

Four all-view deep searches completed: finite translation/source Ward action,
boundary-completed canonical energy, leading variational coefficient, and exact
Einstein families. Cached artifacts are `extinction-finite-translation-source-ward-deep`,
`extinction-completed-canonical-energy-deep`,
`extinction-leading-variational-coefficient-deep`, and
`extinction-exact-einstein-family-deep` under `formal/.lake/hb-extinction-scratch/`.
All report `partial=false`; semantic coverage is `not_measured`, and retrieved
source statements are not fresh compiler verification. Candidate statements,
source arguments and ingredient suggestions were inspected; no generated
ingredient suggestion was accepted as a proof. All four owned searches ended.
No numerical experiment or Lean process was started.

## Literal-source logarithmic translation and the complete-action phase test

**Question.** The even cosine deformations preserve the seam cancellation (own
fact 103), but need not preserve the literal source's complex logarithmic phase
law. Can that stronger law force the complete radiative cut to vanish?

**Complete-action test.** The existing
`d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut_smul_conj` gives
`C(A*p,conj(A)*m)=normSq(A)^2*C(p,m)`. In particular, the target cut is invariant
under every unit phase, including the theta atom's sign monodromy. There is no
odd-character selection of this four-leg quantity. This uses the actual
abstract cut definition, including both quadratic response terms, rather than
discarding the mixed term. Its identification with the complete original HB
action remains an independent obligation. No vanishing follows from this
phase invariance; it cannot be promoted to a physical-clock Ward identity.

**Source contour test: exact classification.** For the literal complex atom,

`a_z(n)=(A_z*n^4+B_z*n^2)*exp(-q_z*n^2)`,

where `A_z=4*pi^2*exp(z/2)*exp(z)^4 != 0`,
`B_z=-6*pi*exp(z/2)*exp(z)^2`, and `q_z=pi*exp(z)^2`.
The original labelled series is summable if and only if
`Re(exp(z)^2)>0`, equivalently `cos(2*Im(z))>0`.
For positive real part, a polynomial times a decaying geometric sequence is a
summable majorant. For nonpositive real part, the exponential has norm at least
one and the nonzero quartic leading coefficient gives a term norm at least
`n^2` eventually. Summability is impossible there.

Every continuous curve from `x` to `x+2*pi*i`, for any real `x`, has a point with
imaginary part `pi/4`. At that point the series is not summable. Hence no full
logarithmic turn stays in the admission set of the original series, including
curved paths. Nevertheless, the exact discrete law survives:

`sum_n a_(z+2*pi*i)(n) = -sum_n a_z(n)`.

On the admitted domain this relates convergent sums in different components.
These results are the positive classification exposed by failure of the raw
contour-shift mechanism. They do not assert a natural boundary for every
possible analytic continuation.

**Meaning for the whole route.** Logarithmic scale is not identified here with
physical Hawking time. The original source's phase law neither supplies a
nontrivial character for the complete cut nor permits an unrestricted raw-source
contour shift. The outstanding theorem is still a source-derived identity for
the continued complete causal/left-QNM action, retaining all correction and
boundary terms. No source term has been discarded and no clock changed.
Neither fixed-clock extinction nor its impossibility is proved.

**Primary-paper applicability.** The September monodromy papers
[Xie–Yu–Zheng](https://arxiv.org/html/2609.06416v1) and
[Diao–Moon–Yao](https://arxiv.org/html/2609.11106v1) were checked. The first obtains
vanishing using a positive self-intersection divisor on a compact Kähler
surface and the Hodge-index form; the second requires a de Rham p-adic local
system and constructs finite covers giving semistability. Neither structure
has been derived for the complete HB causal action. These are not available
extinction premises. Two whole-corpus deep/method searches completed; their
generated ingredient suggestions did not supply the missing source identity.

**Formal status.** The complete scratch file passed `lake env lean` without
warnings. The exact admission classification, no-admitted-turn theorem, and
summed phase law are in `ThetaCuspComplexClockSector`, wired into `RHTower`.
The final isolated cached `lake build
GaloisForLFunctions.RHTower.ThetaCuspComplexClockSector` passed without warnings
(one leaf compilation, 22 seconds). Source hash:
`bb7b4a237e2af9a950a1a3c9c6fa1efe7656d89566e5005e8b750bf3b107a08a`.
The audit directory was removed and the checked leaf artifacts published.
No full or umbrella build, numerical experiment, or raised proof limit was used.
Index refresh completed. Global lint still reports the three unrelated unwired
modules `Sieve.KloostermanGlobalCollisionCoprime`,
`HTGeometry.NavierStokesFiniteTorusInverse`, and `HTGeometry.NavierStokesStressCone`;
none belongs to this change. All owned search, Lean, audit and index processes
have terminated.

**New physical admission result checked.** The concurrently added
`BMOriginalCausalAdmission.original_scalar_ingoing_horizon_trace` now supplies
horizon limits of the original scalar with its coefficient and onset lift.
It makes the second null derivative tend to zero while retaining an unrestricted
first/ingoing trace `Hp`. This is useful admission data for the real-clock
boundary identity. It does not make that temporal trace zero or complete the
metric-current/moving-corner comparison. The next fixed-clock attack must retain
this trace rather than equate transverse derivative decay with extinction.

## Source-reader cusp residue and its exact subtraction

**Derived source identity; complete fixed-clock extinction remains open.**
Write Lambda for the meromorphic completed zeta and fix an actual Xi source
rho. Probe readers `eta_+=(2-rho+e+d)/2` and `eta_-=(2-rho+e-d)/2`.
The completed triple-Eisenstein meromorphic coefficient from
[Huang--Li, Lemma4.2](https://arxiv.org/html/2510.12322#S4.SS1) is

`T(e,d)=Lambda(1+e)*Lambda(rho-d)*Lambda(rho+d)*Lambda(2*rho-1-e)`.

Its transverse residue is
`R(d)=Lambda(2*rho-1)*Lambda(rho-d)*Lambda(rho+d)`.
The three lower-Weyl powers of the literal cusp expansion multiply to
`Y^(1-e)`, with coefficient
`C(e,d)=Lambda(2*rho-1)*Lambda(1-rho+e+d)*Lambda(1-rho+e-d)`.
For H>=1 and Re(e)>0 this term's integral over Y>H, with measure dY/Y^2,
is `C(e,d)*H^(-e)/e`. The completed functional equation gives
`C(0,d)=R(d)` near the original reader.

For Re(rho)<=1/2, reflection to `2-2*rho` makes Lambda(2*rho-1) nonzero.
Punctured zero isolation then makes R(d) nonzero for every sufficiently
small nonzero d. At least one of rho and its FE partner meets this condition.
For that member, boundedness of T in a product neighborhood would bound each
nearby d-slice. Multiplying a bounded slice by e would give limit zero,
contradicting its nonzero residue. Hence T has no finite joint limit,
although `T(e,0)=0` identically.

The positive survivor is an exact subtraction, not an impossibility claim.
Let `B(e)=Lambda(2*rho-1-e)`,
`A(e)=Lambda_0(1+e)-1/(1+e)`, and
`H_rho(e)=A(e)*B(e)+dslope B 0 e`. Then, for e!=0,

`T(e,d)-R(d)/e=Lambda(rho-d)*Lambda(rho+d)*H_rho(e)`.

B is analytic near zero, so its divided difference has the derivative as
continuous value at zero. The displayed remainder is jointly continuous,
zero at every equal reader d=0, and has joint limit zero. This uses no
simple-zero assumption. The exact residue, literal cusp coefficient germ,
unboundedness, no-joint-limit theorem, subtraction identity and continuous
zero remainder are Lean-proved in
[ThetaCuspHawkingBMXiReaderSplitResidue](../../../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMXiReaderSplitResidue.lean).
The elementary tail integral above is a paper calculation; this leaf does
not assert a new truncated-Poincare-integral identification.

**Whole-route consequence.** These are one-source/two-reader coefficients.
The forward ++ forcing has two-source/one-reader coefficients, and cyclicity
does not change that multiplicity. Any application to extinction must derive
the same principal subtraction and every finite boundary/correction term
from the actual causal SS/SV/VV assembly and its original marked left reader.
Neither an arbitrary choice of finite part nor changing the physical clock
supplies that theorem. This analysis excludes a bare continuity shortcut
while preserving a concrete source cancellation to test against the full
action. No complete fixed-clock extinction or impossibility is established.

Scratch and exact cached leaf audit passed without warnings or raised proof
limits; RHTower imports the new leaf. Global lint reports the unrelated
unwired Sieve.KloostermanGlobalCollisionCoprime module. Only this leaf was
compiled in the final audit.

## Seven reframings of fixed-clock extinction, 13 September 2026

**Status:** application of all seven operations and the interrogation in
[the requested guide](../../../../../meta/stroke-of-genius-method.md), to the current
source and experimental records. No new extinction theorem, impossibility
theorem, or Lean module is claimed. The earlier residue subtraction remains
an auxiliary source result. The target remains theta -> Xi -> retained spin
two -> complete causal/left-QNM action -> original-clock extinction -> RH.

### Irritant and the seven operations

The recurring irritant is a zero obtained after changing the quantity:
combining angular pairings, discarding a face, identifying two readers,
changing source subtraction, or replacing the action by a positive model.
The question is which operation preserves the complete physical projection.

| Operation | Application to the actual extinction question | Result of the attack |
|---|---|---|
| 1. Change the arena | Keep finite time, radial and cusp cutoffs together; retain the actual source, marked reader and all faces as arguments of the pairing. | The proved angular limit holds at fixed null coordinates. It does not establish the common spacetime limit. A quotient by boundary work cannot be taken before the physical reader is proved to annihilate that work. |
| 2. Swap primitive and derived | Work backward from zero using the exact negative clock-defect transduction; separately test taking nonlinear clock symmetry as primitive. | The sufficient interface is (PI) above. The corpus's vacuum-differentiable nonlinear covariance theorem makes the proposed primitive RH-equivalent at a nonzero fixed time. It cannot be supplied as an assumption. |
| 3. Re-assign the dictionary | Read the zero angular finite part as a relation between two physical pairings, rather than as zero radiation. | The exact relation is `C_Y + mu*S_Y = N_Y`, derived below. This keeps a generally unevaluated scalar pairing; it is not `C_Y=0`. |
| 4. Vary one structural input | Compare principal versus full constant-Fourier subtraction, literal versus randomized Fourier phases, and the Poisson controls with each moment condition removed separately. Keep the Hawking clock unchanged. | The experiments separate different sources and different constraints. Favorable scalar ratios do not identify the complete action. Period-41 singleton-moment infeasibility is only for the frozen box and prescribed targets. |
| 5. Prove the correspondence | Test arithmetic symmetry -> nonlinear source symmetry, and modular Green zero -> radiative extinction. | Averaging has a product covariance term. The actual modular correspondence retains `N_Y` and the factor `-mu`; neither correspondence supplies complete action invariance. |
| 6. Represent maps instead of individual components | Treat the two radial readers as a map on the two source branches, and treat the full physical projection as a composition of reconstruction and observation. | The reported rank defect prevents inferring radial injectivity from nonzero entries. The columns have different clock rates, so this is not a kernel of the full time-dependent reconstruction. The generic clock-descent composition identity still requires each actual intertwining map. |
| 7. Promote the nuisance | Keep cusp height, onset displacement and reader separation as coordinates; retain their exact defects. | The original onset has nonzero compact translation mass. The split-reader pole has a source-derived subtraction. Neither can be erased by declaring a convenient normalization; their incidence in the complete action remains to be proved. |

### Three concrete proof attempts and their surviving statements

**Angular cancellation attempt.** Let `F` be the original causal angular
source at fixed nonnegative null coordinates, `V` the original physical
reader, `mu=(physicalAngularParameter r)^2-1/4`, and define, on the actual
finite modular domain,

```
C_Y = integral coexactPair(F,V),
S_Y = integral F*V/y^2,
N_Y = original normal flux.
```

`D4BMOriginalScalarPairing.original_physical_pairing` proves
`C_Y+mu*S_Y=N_Y`. The diagonal/reflected theorem proves
`C_Y+mu*S_Y-N_Y^nonconstant -> 0`, at fixed null coordinates.
It does not separately assert that either period has a limit or is zero.
Thus the proposed deduction from this zero to extinction stops at an exact
quantity mismatch, not at an estimate that needs tightening.

The positive replacement, before any limit, is

```
a*C_Y+b*S_Y = (b-a*mu)*S_Y+a*N_Y.
```

This follows by substituting `C_Y=N_Y-mu*S_Y`. If a piece of the physical
action has these weights, this formula identifies both the remaining
scalar coefficient and its boundary term. Establishing the actual weights
and cancellation with the other pieces is still necessary. In particular,
the reader-remainder calculation already recorded above retains a
`(mu-2)` bulk coefficient; the modular zero does not dispose of it.
The displayed substitution is a consequence of the existing Lean theorem,
not a newly formalized complete-action identity.

**Arithmetic symmetry attempt.** For a normalized finite average
`T(F)=sum_i F_i/N`, direct expansion gives

```
T(F*G)-T(F)*T(G)
  = (1/(2*N^2))*sum_(i,j) (F_i-F_j)*(G_i-G_j).
```

The four expanded terms give twice `N*sum_i F_i*G_i` minus twice the
product of sums. For real `G=F`, the defect is nonnegative and vanishes
exactly when all sampled values agree. The corpus already has this finite
covariance identity in `SquareBlockSqrtClockMoment` and the corresponding
probability-measure formula in `Mathlib.Probability.Moments.Covariance`.
This rejects automatic product preservation by averaging, not a particular
unconstructed HB Hecke identity. A Hecke-based extinction proof must derive
the actual correlated products, their action on derivatives and metric
weights, and their causal boundary terms. Replacing the all-plus bilinear
pairing by a Hermitian variance would change the requested quantity.

**Time-symmetry attempt.** Re-derivation from the original onset gives,
for `f(u)=(A*chi(u)+B*chi'(u))*exp(v*u)` and a fixed `h>=0`,

```
integral[-h,1] exp(-v*u)*(f(u+h)-exp(v*h)*f(u)) du
  = h*exp(v*h)*A.
```

After cancelling exponentials, the translated `chi` integrals differ by
`h`; the two complete `chi'` integrals cancel. This is exactly the existing
`D4BMSourceClockTranslation.sourceAndContact_clockMoment`, not a new result.
It fails to give raw source covariance even at critical-line rates. The
positive survivor is an exact work term that a full invariant action must
balance. It is not yet the actual left-QNM functional. At an independent
reader rate `w`, the already recorded formula retains `(A-(v-w)*B)`;
the contact cannot be dropped using the resonant test.

### Written interrogation

| Question from the guide | Answer for this proof chain |
|---|---|
| Where is literal theta used? | In the actual Fourier coefficients, modular gluing, source equations, Xi occurrence and source-prescribed subtractions. The final cancellation must use these through an explicit identity; positivity or inversion alone is shared by broader controls. |
| What group acts, and what is invariant? | Modular pullback, source FE, and physical time translation are different operations. Their established identities have different domains and readers. No proved complete nonlinear action law identifies all three. |
| On what space is this canonical? | On data retaining the marked reader, causal prescription and original cutoffs/subtractions. Reader or subtraction independence is a theorem to derive, not a definition. |
| What is the moduli count? | The period-41 report gives an 11-dimensional real DFT-fixed even space. Fixing the residue and a prescribed complex double zero imposes at most five real affine equations; adding the two moments imposes at most seven. Rank alone therefore does not explain the reported infeasibility inside the coefficient box. The positivity/bound constraints and actual coefficients matter. This is not a count of HB solutions. |
| What is being removed? | Onset mass, nonconstant cusp powers, reader remainders and mixed products. Keeping them yields the explicit identities above and facts111-112, not their vanishing. |
| Which mature theory has these primitives? | Boundary variational identities, covariance of finite averages, and intertwining of reconstruction/observation. The missing transfers are listed below. |
| What are the dual, base and total space? | The physical left reader is the observation; source parameters and fixed-clock data form the base; causal fields together with face data are the data to reconstruct. A Hermitian dual or a reader with a new frequency has not been identified with this observation. |
| Can the theorem be stated without project terminology? | For every zero of the entire completion, prove that a specifically defined, fully corrected causal response has zero pairing with the specified resonant adjoint mode at the original clock. |
| What if the answer is assumed? | Under physical identification, `K=-Sigma*normSq(D)` makes zero equivalent to `D=0`. The source-derived estimate (PI) is sufficient. Assuming zero, covariance or the needed positive sign supplies the missing conclusion rather than proving it. |

Three notations expose the same gap: the spectral equation
`K=-Sigma*normSq(D)`; the finite-domain balance
`P_c=P_bulk,c+sum_faces P_face,c+P_corrections,c`; and the deliberately
misleading shorthand `E_rad=-Re(P)`. The last name does not prove energy
positivity, and nonnegativity of that sign would agree with, not oppose,
the reduced transduction. All terms include independent SS/SV/VV channels,
both solved quadratic corrections, spin two and changing metric weights.

The adjacent-field translation was a self-review, not an external expert
consultation:

| Proposed dictionary | Exact correspondence still missing |
|---|---|
| Conserved variational current -> zero QNM pairing | Admitted adjoint pairing and the evaluated sum of every face and correction. Conservation alone is a balance. |
| Arithmetic linear symmetry -> nonlinear symmetry | The correlated-product law, derivative/metric compatibility and causal prescription. |
| Angular finite part -> spacetime action | Actual coefficients, prescribed subtraction and common time/horizon/cusp/corner limits. |
| Nonzero radial entries -> faithful observation | Injectivity on the actual source space with its time dependence retained. |

The June primary paper [Dang, Karur and Sen](https://arxiv.org/html/2606.05305),
equations(4)-(5), explicitly distinguishes a nonzero boundary current
divergence from its compensating radial inflow. Cancellation between
chiralities uses their specific charge relation. Its flow prescription also
adds a stable-local-minimum condition. These are concrete missing dictionary
rows for an HB transfer, not an extinction theorem for gravity.

### Experimental facts that change the interpretation

The period-41 baseline is itself
`X_base(t)=2*41^(1/4)*cos(t*log(41)/2)*Xi(t)`, already stated in the
experiment's protocol. It follows by splitting the baseline Dirichlet
series into all integers and multiples of41. Consequently, the fixed
center moments are those of this product, not those of undeformed Xi.
For `c=log(41)/2`, normalization by `2*41^(1/4)` gives center value `Xi(0)`
and second derivative `Xi''(0)-c^2*Xi(0)`. The literal source is not recovered
by describing these as two unchanged zeta moments.

The four nonreal double-zero candidates remain numerical, independently
checked to about145 digits at worst, without interval existence certificates.
No full modular HB source or physical action was constructed for them.
They supply discriminating controls, not impossibility of fixed-clock
extinction. No further numerical experiment was run here.

Two new deep searches used all indexed views and completed with
`partial=false`, 57,704 inventoried files and semantic coverage explicitly
`not_measured`; most compiler metadata remained pending. Candidate lemmas,
source arguments and generated ingredient sets were inspected. The proposed
Lie-equivalence composition recipes do not provide the missing physical
maps. Lexical extinction search recovered the exact existing transduction,
not an unconditional extinction producer. Relevant source statements above
were read directly. No fresh primary universal law passed the scientific
method's evidence gate; these bridges were not promoted into one.

**Whole route:** all seven reframings leave the same substantive obligation:
derive the full source work's cancellation or the opposite-sign estimate
(PI) for the actual marked left-QNM action at the original clock. The tests
above prevent replacing that obligation by a component zero, an arithmetic
average, or an RH-equivalent covariance premise. They do not prove its
impossibility. No new Lean compilation or axiom inspection was performed.

## The ordered optical experiment and the actual orbit observable

The [new ordered-kernel report](../../../2-fully-proven/computations/hb-reduced-optical-ordered-kernel-2026-09-13-codex-root/REPORT.md)
tests the scalar coefficient in equations(13)-(14) of
[the two-sided current reduction](../../hb-two-sided-source-current-reduction.md).
Its nonzero values at sampled actual zero heights concern individual ordered
coefficients, before angular, lift, contact and terminal assembly. No experiment
was rerun here.

There is an exact distinction between that nonzero coefficient and the orbit
whose extinction is required. Put

```
s=rho-2, t=-rho-1, delta=s-t,
Gamma(rho;L,d)=L^delta*[K_st]-L^(-delta)*[K_ts].
```

Here the brackets are differences at the same original geometric endpoints,
and `K_st` includes the earlier onset contribution. Replacing rho by1-rho
exchanges s,t and sends delta to-delta. Therefore

```
Gamma(1-rho;L,d)=-Gamma(rho;L,d).
```

This identity is direct substitution into the supplied formula, independent
of numerical roots. The original half-square is FE-invariant by
`D4BMSourceReflectionTransport.square_reflect`. Its native circle mean and
`-Delta(Delta-2)` image preserve that equality: their definitions apply the
same fixed circle averaging and angular derivatives to equal fields. Thus
the unweighted reduced bulk integrand, including that angular image, is
FE-odd. Its reflected sum is zero on common finite domains before any limit.
This is a paper consequence of the inspected definitions; it is not a newly
audited Lean theorem or a complete physical-action identification.

The required canonical unit-carrier orbit is the sum of its two marked
single-copy cuts, and its value is the negative even clock-defect square.
The original physical reader itself has the already proved half-unit
parameter change under source reflection. Consequently the experiment's
unweighted antisymmetrization cannot silently be substituted for this marked
projection. Nor does a nonzero single-copy sample falsify orbit extinction.

For any correctly identified decomposition `P=B+R` on common finite domains
with this FE-odd subtotal B, elementary addition gives
`P(q)+P(FE q)=R(q)+R(FE q)`. This is only a conditional accounting identity:
the actual normalization and marked-reader attachment must establish that B
is a subtotal of P. Defining R by subtraction does not prove its vanishing.
The unresolved source calculation is precisely the FE-even remainder after
that attachment, including other channels and all boundary/correction work.

The current metric source separately supplies
`C(W)=(mu-2)W` and the exact forced contact
`C(U)=(Delta-2)U+R^3*F_original/(R^2-1)`; their finite-domain period identity
retains both terms. Their disappearance was not derived. The source-FE
reader mismatch and the combined modular zero were already facts1 and85;
re-reading them supplied no new extinction theorem.

Two additional deep searches completed over57,718 and57,720 indexed files;
candidate/source/method ingredients were inspected. The generic symmetry and
common-zero recipes did not supply the marked physical identification.
**Goal status:** no proof of fixed-clock extinction or of its impossibility.
The optical report changes the next diagnostic to the correctly normalized
FE-even physical remainder, not another pointwise optical-zero search.

## Reflected reader boundary data at the unchanged clock

**[BRIDGE] [PAPER-PROVED] [LEAN-PROVED].** Test: carry source reflection
through the marked reader by a spatial transform preserving the physical
frequency and endpoint conditions. This tests the prescribed reflected
normalizable mode, not all integral transforms or extinction itself.

For `rho=q`, `q*=1-q`, `chi*=physicalRadialFrequency(q*)`, the original
frequencies and reflected angular parameter give

```
w_false=-2+rho/2,  w_true=-1-rho/2,  i*chi*=-rho/2.
C(w,chi)=Gamma(1+w)*Gamma(1/2)
  / [Gamma(3/4+w/2-i*chi/2)*Gamma(3/4+w/2+i*chi/2)].

C(w_false,chi*)=Gamma(-1+rho/2)*Gamma(1/2)
  / [Gamma(-1/4+rho/2)*Gamma(-1/4)],
C(w_true,chi*)=Gamma(-rho/2)*Gamma(1/2)
  / [Gamma(1/4)*Gamma(1/4-rho/2)].
```

Both quotients are nonzero at every actual Xi occurrence. Every variable
Gamma argument is nonreal; the remaining arguments are `1/2`, `1/4`, and
`-1/4`, none a Gamma pole. Only established Xi strip/nonreal facts enter.
The original continued-domain theorems identify the opposite-horizon
coefficient of the actual normalizable solution `N(w,chi)` as `C(w,chi)/(2*w)`
and give `OriginalHorizonC2(w,N(w,chi)) iff C(w,chi)=0` for nonreal w with
`-2<Re w`. Both conditions hold at the original fundamental frequencies.

Consequently `N(w_side(q),chi*)` has a nonzero opposite-horizon coefficient
and fails the original horizon condition. The unreflected mode is admitted
there by the existing fundamental connection-zero theorem. This is actual
boundary data, not merely unequal algebraic frequency labels or a failed
first-order Darboux ansatz. A local or nonlocal map ending at this prescribed
reflected mode cannot preserve that domain. Finite real clock translation
multiplies its separated time factor by a nonzero exponential, so it cannot
remove the coefficient. This observation concerns the reader, not the full
nonlinear action.

**Whole route.** This reader replacement cannot identify the optical FE-odd
subtotal with the marked orbit. Its defect is nonzero even on the critical
line, so it cannot itself be the source-FE clock-defect energy. The coefficient
has not been identified as a term of the original action. Consequently its
nonvanishing does not impose a compensation obligation on a proof that avoids
this replacement. Full Peierls branch exchange does not require individual
reader equality; the source-to-functional incidence must be proved instead.
Neither extinction nor its impossibility follows. No complete
spectral-disjointness claim is made.

**Seven moves applied to this test:** (1) retain the solution and both endpoint
data; (2) work backward from the exact admission criterion; (3) read the
connection as boundary data rather than a pole label; (4) remove the
first-order restriction and test the required target; (5) apply the proved
continued connection/domain correspondence at negative physical frequencies;
(6) test transport on the prescribed modes; (7) retain the Gamma quotient
as the positive mathematical residue of failure. The interrogation and
three-notation comparison above remain the working framework.

Two whole-corpus deep searches covered57,736 and57,738 inventoried files
without partial retrieval. Candidate/source/method ingredients were inspected.
The suggested disjoint-spectrum theorem requires self-adjoint operators;
it supplies no QNM-domain theorem. The June2026
[Jin–Ma–Zuazua paper](https://arxiv.org/html/2601.03616) uses auxiliary-time
averaging. The2026 [D=3 intertwiner paper](https://arxiv.org/html/2601.18490)
assumes a boundaryless surface in its holomorphic construction and neglects
boundary terms in the displayed gravity integration by parts. Neither
supplies the required HB boundary cancellation.

**Formal status.** `ThetaCuspHawkingBMReflectedReaderBoundary` proves the exact
quotient, nonvanishing, horizon non-admission and nonzero opposite coordinate.
Scratch `lake env lean` and isolated cached final
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMReflectedReaderBoundary`
passed without warnings; one leaf compiled in53seconds. The119-line module
is wired into `RHTower`; no umbrella build, numerical experiment, added axiom
or raised proof limit. Source SHA256:
`92d9d8d70f0f59feaa3ae199ccf0295bb51e526295f0c702be091ebc732cdffa`.
Index refresh and targeted whitespace checks completed. Global lint reports
the unrelated unreachable module `RHTower.Sieve.KloostermanGlobalCollisionCoprime`;
that module was not modified. All owned search, Lean, audit and index/lint
processes terminated; the isolated audit directory was removed.

## Return to source-restricted variational incidence

**Correction of the research direction.** The new reader-boundary theorem is
valid, but its coefficient belongs to a proposed reflected-reader replacement.
It is not proved to occur in the original radiative action. Searching for a
source term to cancel it would introduce an obligation of our own making.
The earlier source/Peierls table already distinguished this from the needed
functional correspondence. No new Lean wrapper or extinction claim is added.

The exact existing algebra gives a more relevant test. Write `p,m` for the
two input fields, `Qpm,Qpp` for their complete quadratic residuals,
`Delta_pm,Delta_pp` for the two retarded-minus-advanced response jumps, and
`ell` for the marked left functional. For a candidate common propagator
`Delta` and an action pairing `P`, set

```
R = B(p,Delta Qpm)+B(m,Delta Qpp),
E = B(p,(Delta_pm-Delta)Qpm)+B(m,(Delta_pp-Delta)Qpp),
W(f) = ell(f)-P(m,f).
```

Linearity and the corpus's complete cubic causal-cut formula give exactly

```
markedCut = PeierlsCut(P,B,Delta;p,m) + W(R) + ell(E).
```

Here the identical direct cubic terms have canceled between the two response
prescriptions, as in `TotalThirdOrderCausalCut`; no physical boundary has been
deleted. This is an algebraic interface decomposition. Interpreting its
arguments physically requires the original augmented residual, including
metric weights, all channels and every boundary contribution.

With symmetric B, full cyclicity and causal skewness, the existing theorem
`d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut_swap` makes the Peierls
term odd under `p<->m`. Literal source FE performs exactly that exchange with
the four amplitude slots exchanged. For those matched raw amplitude slots,
the two Peierls terms cancel. What remains is the sum of `W(R)+ell(E)` over
the two copies. This does not require `W=0` on arbitrary fields, equality of
reader profiles, or an invertible reader transmutation. It does require the
same physical pairing/propagator and the correct amplitude incidence.
The unit-carrier normalization cannot be inserted without proving its
transport; canonical packet FE is a different, cocycle-weighted operation.

**Independent source evidence checked:** full literal field/source exchange;
local bulk-plus-boundary cyclic Einstein variation; actual left-metric
equation; the complete mixed correction exchange. The latter still contains
cubic linear work, two correction/source works and two boundary defects.
The scalar `BMCausalSourceAdjoint` transfers an angular operator to radial
weights; it is not the full retarded/advanced transpose theorem. Advanced
scalar integral admission likewise does not identify the full Einstein
propagator. These sources establish neither vanishing of the displayed
functional error nor cancellation of the complete physical orbit.

The tested general Noether and exact-Einstein-family proposals supplied no
new source law: the former requires an identified gauge direction and
boundary pairing; no exact family with the actual metric and causal data was
constructed. These repeat existing obstacles and are not counted as new
mathematical results. Three deep/method searches completed with nonpartial
inventories of57,763,57,763 and57,773 files; their proposed ingredients did
not supply the missing physical incidence. No computations or Lean builds
were run in this continuation. Fixed-clock extinction and its impossibility
remain unproved.

## Fixed-onset Peierls test: rejected source identification

**Target unchanged:** literal theta -> Xi -> retained spin two -> complete
causal/left-QNM action -> original-clock extinction -> RH. This test produced
no new extinction or impossibility theorem. Its source integration-by-parts
survivor is already fact15, not a new result.

**Tested inference [BRIDGE attempt]:** a fixed onset can be represented by
right multiplication in the common Peierls response, and its commutator
then decides whether the complete reflected cut cancels. This cannot be
applied to the original source as stated. `BMMixedCurrentCutoff` defines
the source by differentiating the switched current. In static coordinates,
with `f=r^2-1` and `C` the original two-component mixed current,

```
T_A = f/r^2 * partial_r(chi*C_A),
R_A = 1/(r^2*f) * partial_t(chi*C_A).
```

Thus the source is `D(chi*C)=chi*D(C)+N`, with exactly the onset tensor
in `switchedCurrentSource_eq`. Its physical left-field contraction is
`-2*chi'/r^2 * sum C_A*(partial_r-partial_t/f)Psi_A`, by
`BMCurrentSourceAction.physical_left_onset_action`. The contact's null
self-pairing does not erase this contraction.

There are two distinct operator questions. If `Delta` is skew for a
symmetric pairing and multiplication by `chi` is symmetric, direct
transposition gives

```
P(Delta(chi*f),g)+P(Delta(chi*g),f)
  = P((Delta*chi-chi*Delta)f,g).
```

But applying the same complete source map `S` to both arguments gives
`P(Delta(S*f),S*g)=-P(Delta(S*g),S*f)` for any linear `S`; no commutation
with `Delta` is needed. Neither expression has been identified here with
the actual complete marked cut. In particular, nonzero bare commutator
would not prove failure of the second expression or of extinction.

**Attempt to close the actual contact:** substituting the original stream
metric and integrating its source work by parts recovers identity(G):
temporal/radial flux plus `2/r^4 * sum (chi*C_A)*(Master(Psi)_A-A(Psi)_A)`.
The homogeneous left equation removes the master term, leaving the angular
overlap. Transferring that angular operator retains its cusp/core/side
fluxes. This repeats fact15. It does not close the original marked action,
and no duplicate Lean leaf was created.

**Whole-route consequence:** retain the exact source map and its transpose
at both vertices before invoking Peierls skewness. The solved mixed
quadratic residual kills its changing-weight residual, but the existing
`BMLeftQNMCorrectionExchange.complete_mixed_exchange` still retains source
work and boundary defects. No source equation checked in this test sets
their sum with the independent SS/VV and original left-QNM terms to zero.
The previously stated absolute-error/sign interface and source-restricted
Peierls incidence remain unproved; they have not become assumptions.

The seven reframings and written interrogation above remain the method
record. This continuation tests the correspondence (move5), compares
placing the source map on one or both arguments (move4), and keeps onset
dependence as part of the operator (moves6–7). It does not replace the
fixed Hawking clock or redefine the target after the failed inference.

Broad primary-paper checks also supplied no closing identity. The
[2026 flux-law paper](https://arxiv.org/html/2601.07091v2), sectionII,
retains boundary charges and radiative flux. The
[coadjoint-averaging paper](https://arxiv.org/html/2607.17943v1), lemma5.1,
obtains zero by integration over a compact orbit with invariant Liouville
measure. No such identification of the marked HB observable was derived.
The [photoacoustic adjoint paper](https://arxiv.org/html/2604.04022v1),
section3.3, keeps the source operator in the composite adjoint; its wave
domain and source differ from HB. These are checked transfer attempts,
not imported HB premises. Four deep/method searches returned nonpartial
inventories of57,778,57,782,57,787 and57,789 files; semantic coverage was
unmeasured and candidate compiler metadata predominantly source-only.
No numerical experiment or Lean build was run.

## Positive-source, overtone and chiral tests of the same extinction target

No complete-action vanishing, opposite-sign estimate, or impossibility
theorem resulted. The positive-source current still has the gradient
contact of fact4. The overtone estimate returns to fact91: the growing
canonical susceptibility belongs to varying parent overtones, whereas
the available Rodrigues estimates vary the reader of a fixed source.
No estimate was transferred between these families.

The chiral test exposes a precise normalization issue to resolve, not a
proved error in a physical helicity reconstruction. The literal displaced
cut has deformation `s*e*(aS*H/2+aV*JH)`. The proved independent-field
pairing has coefficients

```
aS*cS/4+aV*cV,       (aS*cV-aV*cS)/2.
```

Both vanish at `aV=i*aS/2`, `cV=i*cS/2`. At the ratio `i` rather than
`i/2`, the first is `-3*aS*cS/4`. Meanwhile
`d4GravitationalHelicityPlus/Minus` are the abstract coordinates
`scalar +/- i*vector`, and the stationary chiral-kernel discussion uses
`aV=+/-i*aS`. The latter coordinates have not been identified here with
the displaced-cut spin-two coefficients. A null deformation contraction
also does not prove self-duality of the full perturbed Weyl tensor or
vanishing of the nonlinear action.

The actual quadratic source further specifies what the null-deformation
attempt would have to cancel. Write `F=squareSource(q)`,
`U=coordinateResponse(q)`, `lambda=eigenvalue(q)`,
`s=physicalRate(q,branch)`, and
`Hminus(f)=collisionHelicityMinus(hessianComponents(f))`.
Substitution of `aS=a`, `aV=i*a/2` in
`BMPhysicalAngularPotential.potentialSource`, using the rotation in
`PolyatomicAngularHelicity.collisionHelicity_rotate`, gives

```
collisionHelicityMinus(source) = a^2*B^2*s^2/(8*r^4) * (
  ((s+1)^2-2*r*(s+1)-4*r^2)*Hminus(F)
  +lambda*(4*s^2+14*s+12-4*r^2)*Hminus(U)).
```

This is a paper substitution in the existing full angular second-source
formula, not a new Lean audit. It retains the SS, SV and VV coefficients
and the original angular response. It supplies neither nonzero integrated
radiation nor cancellation after the solved full quadratic corrections.
In particular, the null first-deformation pairing is not a proof that
this subsequent source vanishes. No source term was deleted to obtain
an extinction claim.

**Whole route:** the chiral option must derive its actual nonlinear Weyl
or action identity, including the source displayed here and every
correction/boundary term. The exact conserved or nonnegative quantity
needed by the original marked action is still missing. These tests do
not replace that target with a polarization classification.

## Original metric-period test against fixed-clock extinction

The current `OriginalReaderEquation.original_metric_scalar_integral`
supplies the precise finite-domain identity recorded in own fact117.
Its reader coefficients are `mu*(mu-2)` and `mu`, and its right side
retains the difference of two original angular transfer fluxes. The
attempt to use the earlier combined modular zero stops unless these
actual coefficients, forced contact and boundary difference are matched.
No vanishing or opposite-sign estimate for the complete action follows
from the inspected statement alone. This sharpens the interface being
tested; it is another agent's existing source theorem, not a new proof here.

The fixed-translation test again returns the already recorded onset
moment in fact26 and the weighted correction work in facts27–33; no new
invariance was obtained. An exact-metric completion was also tested
against the literal scalar angular block. No completion satisfying the
original source and boundary data was constructed. Neither failed
attempt establishes impossibility of fixed-clock extinction.

The broad reciprocity search led to
[Unifying Physical Backpropagation](https://arxiv.org/html/2608.11585v1).
Its equation(110) retains independent initial and terminal contributions
in the full adjoint variation; section6.2 separately requires reciprocity
along the nonlinear trajectory and its reversal construction. No HB
identification discharging those requirements was derived. Three deep
searches completed over57,800,57,801 and57,803 indexed files with
`partial=false`; semantic coverage remains unmeasured and retrieved
compiler metadata predominantly source-only. No experiment or Lean
build was run, and no new unconditional extinction law was found.

## Reframing the retained history and the new horizon experiment

The target remains complete fixed-clock extinction or its actual impossibility.
Neither is proved here. The following tests apply the seven operations in the
requested guide to new evidence; they do not promote an auxiliary result into
an extinction theorem.

| Operation | Concrete test and outcome |
|---|---|
| Change the arena | Keep the causal field together with its initial-history strip. The existing exact retarded translation law retains that strip even when the translated forcing vanishes; zero forcing is not zero response. |
| Swap primitive and derived | Work backward from `K=-Sigma*normSq(D)`. A source-derived nonnegative complete action would suffice under physical identification. Taking nonlinear canonical clock covariance as primitive instead retains the existing RH-equivalent premise. |
| Reassign the dictionary | Interpret the reported negative phase mean as a coefficient of horizon density, not as the value or sign of the family-regularized complete action. Integration changes the height exponent and retains a lower endpoint. |
| Vary one structural input | Compare specialization before/after finite-part extraction while holding clock, field and reader fixed. The general collision counterexample does not apply automatically: the actual diagonal triple cap flux has no exponent collision, as recorded in fact118. |
| Prove the correspondence | Trace the report's `angularPair` to `PhysicalLiftHorizonCurrent.angular_pair_original`, then compare with `CapAngularFluxCusp.angularFlux`. The former is quartic in one source; the latter includes the independent physical reader. They cannot share a zero theorem without an actual identification. |
| Represent one level inside another | Retain affine exponent labels and the physical specialization map explicitly. At the integrated principal level the exponent is `1+2*k*u`, rather than the density exponent `2*k*u`. The data needed by the finite part depend on which object is being regularized. |
| Promote the nuisance | Keep the lower modular boundary `l(x)=sqrt(1-x^2)` and the causal onset as data. They expose finite endpoint work and retained history that a proposed all-face conservation law must cancel. |

### Horizon density versus its integrated finite part

This is a paper-level interface derivation, not an admitted formula for the
complete physical action. Let the principal source be

`S_0(y)=a*y^(1/2+u)+b*y^(1/2-u)`,

with `alpha=1/2+u`, `beta=1/2-u`, `mu=u^2-1/4=-alpha*beta`.
The literal definitions of `squareCovector` and `gradientCovector`, with
horizontal derivatives zero, give

```
J_0 = a^2*alpha*y^(2u) + a*b + b^2*beta*y^(-2u),
K_0 = a^2*alpha^3*y^(2u) + a*b*alpha*beta + b^2*beta^3*y^(-2u).
```

The report's surviving angular density is
`A_0=(2mu-2)*J_0^2+2*J_0*K_0`.
In its expansion `sum_(k=-2)^2 c_k*y^(2ku)`, the coefficient with exponent
identically zero is

```
c_0 = a^2*b^2*((2mu-2)*(1-2mu)-4mu*(1+mu))
    = a^2*b^2*(-8u^4+6u^2-3).
```

For the normalized critical-line source, `u=i*gamma` and `a*b=1`, this
recovers the report's `-(8gamma^4+6gamma^2+3)`. The term is already neutral
in the one-parameter density family; it is not an accidental spectral
collision. This observation alone does not determine a finite part.

The experiment integrates that density with `dx dy`, as confirmed by
reading `horizon_pair.py`; it is not a logarithmic-height integral. At
critical-line parameters, every `1+2ku` is nonzero. Thus the principal
antiderivative is

`B_0(y)=sum_(k=-2)^2 c_k*y^(1+2ku)/(1+2ku)`.

For a finite modular truncation `D_Y`, direct integration gives

```
integral_(D_Y) A_full - B_0(Y)
  = integral_(D_Y) (A_full-A_0)
    - integral_(-1/2)^(1/2) B_0(l(x)) dx.
```

Every upper exponent `1+2ku` is a nonzero affine family, including the
neutral-density contribution `c_0*Y`. If the prescribed action subtracts
this upper primitive and the remainder is admitted, its finite value is
the pointwise-subtracted remainder **minus the lower-boundary primitive**.
The experiment omits that latter term by subtracting the principal density
throughout the cell. Proving that this primitive, normalization and family
are precisely those of the original complete action is still required;
neither its value nor the sum of the other physical faces is obtained here.
No new Lean theorem or sign claim is attached to this unclosed interface.

### Written interrogation and failed transfers

- Literal theta enters the full covectors and Fourier amplitudes; the principal
  calculation alone uses no zero-selecting arithmetic identity.
- Modular pullback, raw source FE and physical-clock translation remain different
  operations. None of the inspected identities identifies their complete actions.
- The canonical data must retain reader, causal history, original family and
  subtraction. A moduli/dimension argument is unavailable: no finite-dimensional
  model of all full causal corrections with these boundaries was established.
- The pieces being removed are precisely initial history and the lower primitive;
  their explicit formulas expose required work rather than justify its deletion.
- The dual is the prescribed left-QNM functional. The phase-averaged quartic
  source density is not that functional. This is the failed dictionary row.
- Without project names, the task is to prove zero pairing of a fully forced
  causal solution with its specified resonant adjoint after all boundary work.
- Assuming the answer leads back to `D=0` through strict susceptibility, leaving
  the same source-production gap rather than a proof.

Three notations isolate the distinction: `A_0=sum c_k*y^(2ku)` for the
density; `I_Y=B_0(Y)+C+o(1)` for the integrated family; and the deliberately
bad shorthand `negative mean = negative action`. The last equality has no
mathematical justification. The adjacent-field comparison is a self-review,
not an external consultation.

The original August paper [Ivanov, arXiv:2608.23069](https://arxiv.org/html/2608.23069v1)
requires boundary counterterms and a renormalized boundary Gaussian weight
to glue its quartic Euclidean model (Theorems1–2). It supplies a concrete
warning that bulk renormalization does not determine gluing; it supplies
neither HB's Lorentzian action nor permission to change its source-fixed
counterterms. No extinction law transfers from that paper.

The previous modular-entropy and closed-time-path tests likewise supplied no
source law. Entropy exchange needs an identified invariant state/evolution;
equal-source closed-time-path normalization does not set its physical response
derivative to zero. The exact HB marked cut retains both response jumps.

Three new deep/method searches completed with `partial=false`, over57,832,
57,833 and57,833 files; semantic coverage was unmeasured and retrieved compiler
metadata source-only. Their proposed ingredient sets were unverified and did
not close any physical-action obligation. No numerical computation or Lean
build was run. The new verified corpus fact is fact118, not extinction.

## Rebuilding HB as a relational clock readout — arXiv:2608.27650

**Target unchanged:** original theta → Xi → retained spin two → original complete
causal/left-QNM action → fixed-Hawking-clock extinction → RH. This reconstruction
changes the observable used to study the missing law. It does not prove that law.

The [paper](https://arxiv.org/html/2608.27650v1), §§2–4 and Appendices A–D,
separates clock reading, spatial lattice translation and an externally controlled
cycle. Its cycle factorization is adiabatic and retains periodic geometric and
dynamical factors. Its photonic free clock–system constraint omits the pair-creation
interaction at leading order. The useful imported idea is comparison of two
operations through their relative complex amplitude, with a relational reference.
Neither an exact finite-time Hawking period nor a full nonlinear Einstein
constraint follows from the photonic construction.

### The actual HB dictionary

Let `q` be an actual Xi multiplicity copy, `R q` its FE reflection,
`delta=Re(rho)-1/2`, `gamma=Im(rho)`, and `kappa_q` the literal nonzero source
cocycle. On the existing finite source-packet space `E`, put

```
H_n e_q = h_q e_q,       h_q = (gamma-i*delta)/2,
J(c e_q) = kappa_q*conj(c) e_(Rq),
U_t = exp(-i*t*H_n).
```

Here `H_n` removes only the already fixed overtone/redshift offset. It is not a
new source-dependent clock. The source equations independently supply
`h_(Rq)=-h_q`, `kappa_(Rq)*conj(kappa_q)=1`, and
`conj(h_q)+h_(Rq)=i*delta`. They do not supply `delta=0`.

Restoring the uncentered frequency changes both path coefficients by the same
positive factor `exp(t*(1/4-decay_n))`: the offset is purely imaginary and
anti-linearity gives the same factor in both orders. Their intensity ratio
and visibility are therefore unchanged. Removing this common attenuation in
the readout does not imply that the centered evolution is contractive.

| Paper primitive | Source-faithful HB object | Transfer boundary |
|---|---|---|
| Clock reading | Original Hawking `t`, acting through `U_t` | Neither cusp height nor control-loop parameter replaces `t`. |
| Clock–system pair | `J` represented as a linear map from the conjugate space `conj(E)` to `E` | A physical quantum Hilbert space/POVM has not been constructed from Einstein evolution. |
| Energy anticorrelation | Two-sided constraint `H_n L + L conj(H_n)` on that map | Its coefficient is `i*delta*kappa_q`; setting it to zero is the missing law. |
| Two paths | `J U_t` and `U_t J`, both ending at the reflected source copy | These are existing source operations; no retarded/advanced exchange is assumed. |
| Relative holonomy | Ratio of the two nonzero path coefficients | It is positive real, so its modulus must be retained. |
| Readout | Two-arm intensity contrast and dark-output intensity | Phase-only normalization discards the target defect. |
| Nonlinear interaction | Complete Einstein jets, solved quadratic responses and boundary work | Cannot be discarded as post-preparation dynamics. |
| Topological protection | Would require an independently constructed source family and protected physical transport | No gapped HB band or compact parameter torus is supplied by the dictionary. |

The honest arena is `Hom_C(conj(E),E)`. For a finite set of copies, let `L_F`
send `bar(e_q)` to `kappa_q e_(Rq)` on that set and to zero elsewhere.
Write `E_(r,q)` for the map sending `bar(e_q)` to `e_r`, zero on other basis
vectors. The free relational constraint is exactly

```
H_n L_F + L_F conj(H_n)
  = sum_(q in F) i*delta_q*kappa_q * E_(Rq,q).
```

This is a finite algebraic representation of the existing anticommutator;
normalizability of a global quantum state is not asserted. Vectorization needs
the appropriate dual space; no tensor-product quantum state is silently
identified with this map. Replacing `conj(H_n)` by `H_n` makes the reflected
pair coefficients vanish automatically. That would erase the anti-linearity of
the actual source. The corpus's linear/anti-linear coherence theorem already
identifies the resulting change: linearized reflection is clock-odd but loses
involutivity off the critical wall. Thus the free anticorrelation obtained from
linear reflection is not a solution of HB's constraint.

### Exact source interference, with the common clock retained

Let `A_t=(J U_t e_q)(Rq)` and `B_t=(U_t J e_q)(Rq)`. The existing finite-step
formulas give

```
A_t = kappa_q * exp(i*gamma*t/2) * exp(-delta*t/2),
B_t = kappa_q * exp(i*gamma*t/2) * exp( delta*t/2).
```

Consequently

```
A_t*conj(B_t) = |kappa_q|^2 > 0,
|A_t|^2 = |kappa_q|^2 * exp(-delta*t),
|B_t|^2 = |kappa_q|^2 * exp( delta*t),
|A_t-B_t|^2 = 2*|kappa_q|^2 * (cosh(delta*t)-1),
log(|A_t|^2/|B_t|^2) = -2*t*delta.
```

All differential phase information has canceled before any assumption about
Xi placement. The lost amplitude information is exactly what is needed. With
a variable reference phase `theta`, direct expansion gives

`|A_t-exp(i*theta)*B_t|^2=2*|kappa_q|^2*(cosh(delta*t)-cos(theta))`.

The visibility of this algebraic readout is `1/cosh(delta*t)`. At `t=1`, the
already established complete reduced cokernel transduction becomes

```
K_n(q) = -Sigma_n(q)*|kappa_q|^2
           * (log(|A_1|^2/|B_1|^2)/2)^2.
```

This identity uses the complete reduced target-independent causal cut, not an
isolated quadratic channel. The variable-phase/visibility formulas above are
paper consequences of the cross-amplitude and intensity identities; the
separate physical interferometer realization remains unconstructed. The
source readout formulas are being checked in an isolated Lean leaf.

Equivalently, the finite source loop `J U_t J U_(-t)` acts on `e_q` by
`exp(t*delta)`. This is a dilation component of complex transport. A phase-only
quotient makes it invisible. The loop is defined on finite source packets;
its action on the original causal boundary domain has not been established.

### Keep the complete interaction in the relational constraint

If an interacting history formulation is constructed, it must satisfy a full
constraint `C_total=C_clock+V_Einstein`, not the free constraint alone. Even
`C_total Psi=0` would give `C_clock Psi=-V_Einstein Psi`, which is not zero.
No Hilbert-space operator `V_Einstein` is claimed to have been constructed here.
Its required perturbative content is already concrete. With
`E(g+h)=Lh+B(h,h)/2+C(h,h,h)/6+...`, the exact `++-` source is

```
B(p,h_pm) + B(m,h_pp)
  + (C(p,p,m)+C(p,m,p)+C(m,p,p))/6.
```

Here `h_pm` and `h_pp` must be the solved original corrections. Each source
retains its SS, SV and VV contributions and spin-two component. The actual
metric weights are fixed by the local action identity

```
delta L = -sum_ij (g^-1 M (g^-1)^transpose)_ij * source_ij
          + sum_a partial_a(localVolume * current_a).
```

`BMActionBoundary.literal_action_boundary_near_zero` proves this for the literal
fields and independent amplitudes in a nondegenerate neighborhood. The current
has all four directions. Integration therefore retains horizon, cusp,
characteristic, temporal and corner fluxes; onset and source-contact work must
be counted in the same original action. The already closed SV correction also
annihilates its own moving-weight residual, by
`BMMixedQuadraticClosure.movingWeight_mixed_residual_zero`. This does not cancel
other channels or all boundary work.

An exact sufficient physical interface is the following, with all quantities
defined using the original clock, reader and prescribed counterterms:

1. The fully assembled finite-domain action `P_c(q)` tends to the established
   `K_n(q)` as the original cutoffs are removed, with an admitted error `e_c→0`.
2. A current derived from the complete source gives
   `Re(P_c(q)) >= -eta_c`, where `eta_c≥0` and `eta_c→0`.

Then
`0 <= Sigma_n*|kappa_q|^2*(log(|A_1|^2/|B_1|^2)/2)^2 <= e_c+eta_c`,
so the logarithmic gain vanishes, both amplitudes match, and `K_n(q)=0`.
This proves the receiver mechanism on paper, but neither interface item is
proved here. In particular, an intensity norm is nonnegative by construction;
identifying it, with the required sign, with the original left-QNM action is
not supplied by that elementary positivity.

A second possible physical producer is contraction of the actual finite loop
in a fixed positive source-derived norm on both members of every FE orbit.
Its two eigen-gains `exp(t*delta)` and `exp(-t*delta)` then force `delta=0` for
any fixed `t>0`. This too remains a proposed interface, not an independently
proved property. The existing source-specific Bogoliubov completion preserves
a signed Hermitian form while retaining off-wall partner production; that
conservation cannot substitute for the required positive contraction.

### Seven operations and the written interrogation

| Operation | Test made here; whole-route consequence |
|---|---|
| Change arena | Use the conjugate clock/source graph and the two-path square. Anti-linearity is now visible in the constraint itself. |
| Swap primitive/derived | Take actual source transport as primitive and derive its clock readout; importing a free stationary state would assume the missing zero. |
| Reassign dictionary | Read the clock defect as logarithmic gain, not an unwrapped phase. The exact cokernel is gain energy. |
| Vary one input | Retain modulus when passing from unit-circle to nonzero-complex transport. Phase-only readout loses the defect identically. |
| Prove correspondence | Trace both arms to existing packet operations and derive their exact intensities; do not substitute a synthetic two-level model. |
| Represent one level inside another | Encode anti-linear FE as a linear graph on the conjugate space. Dropping conjugation produces the wrong automatic anticorrelation. |
| Promote nuisance | Keep gain, nonlinear interaction and causal boundary history as coordinates of the proposed physical realization. None is a removable common phase. |

- **Where is literal theta used?** In `kappa_q`, its nonvanishing/involution,
  the Xi-labeled generator and the complete-cut transduction. Topological
  vocabulary alone supplies none of the missing source cancellations.
- **What acts and what is invariant?** The real-time group and anti-linear FE
  involution act on finite packets. Their loop has positive gain. Its phase is
  invariant but insufficient; no complete-action invariance was derived.
- **Canonical space?** Actual multiplicity copies, conjugate source graph,
  original Hawking time and physical boundary data. No arbitrary clock split,
  new frequency, or choice of positive norm is silently fixed.
- **Moduli count?** A winding number does not determine a positive gain. Here
  the actual gain already varies with the source spectral coordinate; no
  finite-dimensional rigidity theorem selecting unit gain was found.
- **What was being removed?** Modulus, pump/source interaction and boundary
  memory. Restoring them exposes the exact outstanding constraint.
- **Mature theory and failed row?** Relational clocks and interference provide
  the graph/readout description. Positive physical transport on that graph
  has not crossed from the photonic model to the nonlinear causal action.
- **Dual/base/total space?** Base: source copies and original clock readings;
  total data: fields, corrections and boundary traces; dual: the prescribed
  left-QNM functional. No independent quantum detector may replace that dual.
- **Without invented names?** Prove that the two orders of applying the actual
  source reflection and the same finite evolution have equal amplitudes,
  through the complete original physical action.
- **With the answer assumed?** The source gain is one and the dark intensity
  vanishes. Showing only equal phases has already happened unconditionally,
  so it cannot be counted as progress toward the missing amplitude equality.

Three notations: the operator defect `[J,U_t]e_q`; the two-sided source-map
constraint `H L_F+L_F conj(H)`; and the deliberately lossy notation
`phase(A_t/B_t)=0`. The last records a true but insufficient observation.

The attempted transfers were: topological winding → fixed-time extinction
(does not transfer: it loses the gain); free relational stationarity → source
stationarity (does not transfer: it changes conjugation/omits interaction);
conservative completion → dark output (does not transfer: signed conservation
retains partner production). Their positive residue is the exact amplitude
readout above. None disproves actual fixed-clock extinction.

Broad recent searches also found
[relational memory](https://arxiv.org/html/2606.08595v1) and
[canonical clock sectors](https://arxiv.org/html/2607.23852v1). They provide
additional transfer checks, not HB theorems: retain memory after conditioning,
and preserve the clock momentum as well as its label. No altered clock or
coarse-grained evolution is used here.

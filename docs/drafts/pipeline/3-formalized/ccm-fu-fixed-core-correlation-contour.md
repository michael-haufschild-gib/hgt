# CCM-FU: the literal paired Mellin contour has an exact residue limit

- **Stage:** 3-formalized; four exact-file checks, new-declaration axiom audits and global formal lint passed. Lake packaging audit remains pending.
- **Parent:** [physical signed-head average](../1-in-progress/ccm-fu-fixed-core-correlation-contour.md).
- **Closed:** Entire literal source; filled finite-prime Mellin numerator; exact paired residue; integrable boundary; quadratic decay throughout the closed strip; weighted contour shift; inverse Mellin contour limit.
- **Physical landing:** [The physical average W_P equals this contour](ccm-fu-fixed-core-physical-dilation-mean.md), with its source domains discharged.
- **Orientation:** [Strict source positivity and eventual physical parity](ccm-fu-divisor-source-residue-sign.md) are proved.
- **Discrete identification:** [Exact discrete-to-physical release and its distant-prime sign](ccm-fu-discrete-physical-prime-release.md) are proved.
- **Open:** Quantitative control as P and the cutoff change, reserve renewal, exhaustive selection, uniform signed Abel bound, RH.

## Exact theorem

For the literal coefficients b(n)=log(n)-tau(n)+2gamma, the entire source B
agrees with their absolute L-series on Re(w)>1 and with the corpus's
conditional divisor Dirichlet source on Re(w)>1/2. Away from w=1,

`B(w)=-zeta'(w)-zeta(w)^2+2*gamma*zeta(w)`.

For a nonempty finite prime core P, put

`E_P(s)=product_(p in P)(1-exp((1/2-s)*log(p)))`,

`N_P(s)=B(s-1/2)*dslope(E_P,1/2,s)/2`,

`F_P(s)=N_P(s)/s`, and `K_P(s)=F_P(s)*F_P(2-s)`.

Both E_P and N_P are entire. Since E_P(1/2)=0, away from s=1/2 the
literal formula is F_P(s)=B(s-1/2)*E_P(s)/(2*s*(s-1/2)). Its numerator
value at zero is -B(-1/2)*E_P(0). The companion F_P(2) equals the actual
signed moment J_P=integral G_P(x)/x^3 dx. Thus

`Res_P=-B(-1/2)*E_P(0)*J_P`,

where E_P(0)=product(1-sqrt(p)) and J_P has the previously proved strictly
positive lower bound independent of P. The full punctured complex limit
s*K_P(s)->Res_P is proved. The companion orientation theorem proves
B(-1/2)>1/(272*pi)>0 and fixes the residue's sign as (-1)^(card(P)+1).

Define Q_P(s)=N_P(s)*N_P(2-s) and

`T_P(s)=-dslope(dslope(Q_P,0),2,s)`.

T_P is entire, and off s=0,2,

`T_P(s)=K_P(s)-2*Res_P/(s*(2-s))`.

There is a finite C_P>=0 such that on the whole closed strip
0<=Re(s)<=2,

`norm(T_P(s)) <= C_P/(1+Im(s)^2)`.

For every real logarithmic dilation a, every exponentially weighted
vertical trace exp(a*s)*T_P(s) in this strip is absolutely integrable.
Its integral equals the integral on Re(s)=0.

The literal inverse Mellin contour

`M_P(a)=(1/(2*pi))*integral_R exp(a*(1+i*t))*K_P(1+i*t) dt`

is absolutely convergent. For a>=0 its exact decomposition is

`M_P(a)=Res_P+(1/(2*pi))*integral_R exp(i*a*t)*T_P(i*t) dt`.

Consequently **M_P(a)->Res_P as a->infinity**. The companion physical
theorem proves equality with W_P(exp(a)); that equality is not a definition.

## Dependency-closed paper proof

Let h be the existing entire regularized zeta function, with h(1)=gamma.
Expanding zeta=1/(w-1)+h(w) cancels both Laurent poles and gives the entire
expression B=-h'-h^2-2*dslope(h,1)+2*gamma*h. Absolute L-series identities
for log(n), tau(n) and the constant coefficient identify B on Re(w)>1.
Analytic identity on the connected half-plane extends equality to the
existing conditional divisor source on Re(w)>1/2.

The absolute coefficient series uniformly bounds B for Re(w)>=3/2.
On Re(w)=-1/2, the existing sharp chi-factor bound and reflected absolute
zeta bound give linear growth of zeta; the corpus's derivative bound is
quadratic. Hence B has quadratic growth there. Each finite prime
multiplier is bounded on Re(s)>=0 by product(1+sqrt(p)). The paired
Mellin denominators then give K_P(i*t)=O_P(1/t^2). A divided difference
removes the local pole at zero; compactness handles the finite segment,
and the remote estimate gives absolute integrability of that whole
pole-subtracted boundary. Its residue is identified with the actual
moment by F_P(2)=J_P, rather than assumed from a formal expression.

Symmetry gives Q_P(0)=Q_P(2)=2*Res_P. The two divided differences
therefore fill both endpoint singularities and give the exact formula
for T_P. The combined rational subtraction is O_P(1/t^2), so the same
quadratic boundary decay holds for T_P on Re(s)=0 and, by reflection,
on Re(s)=2. Existing polynomial bounds for zeta and zeta' give polynomial
growth of T_P throughout the strip above a fixed height. Compactness
fills the remaining bounded-height part.

Apply Phragmen-Lindelof to the entire weighted function (s+1)^2*T_P(s).
Its two boundary lines are bounded, and its strip growth is polynomial.
It is therefore bounded throughout the strip. Since
norm(s+1)^2>=1+Im(s)^2 on that strip, the asserted uniform quadratic
decay follows. For fixed real a, norm(exp(a*s))<=exp(2*abs(a)) there.
This preserves vertical absolute integrability and forces both horizontal
edge integrals to zero. The corpus's rectangle contour theorem moves the
weighted T_P integral to Re(s)=0, including this boundary.

At s=1+i*t the rational contribution is 2*Res_P/(1+t^2). The proved
Cauchy Fourier identity integrates exp(i*a*t)/(1+t^2) to pi*exp(-abs(a)).
For a>=0 the extra exp(a) cancels it, giving the normalized contribution
Res_P. The remaining boundary is L1, so Riemann-Lebesgue makes its
oscillating integral tend to zero. All source estimates and the complete
contour shift are discharged; no contour hypothesis is retained.

## Lean implementation and validation

- `DivisorSourceEntire.lean`: entire literal source, both series identifications, right-half-plane and negative-half-line bounds; six theorems and one public definition.
- `DivisorCoreMellinBoundary.lean`: processed continuation, exact pole coefficient and positive-moment companion, full pole-subtracted boundary integrability; fourteen theorems and six public definitions.
- `DivisorCoreMellinStrip.lean`: entire two-pole subtraction, uniform closed-strip decay, vertical integrability and weighted contour shift; six theorems and one public definition.
- `DivisorCoreMellinMean.lean`: absolute convergence, exact residue-plus-boundary identity and contour limit; four theorems and one public definition.

All four leaves passed foreground scratch and exact-file checks using
`lake env lean`; the four leaf oleans were emitted. All are wired into
`RHTower.lean`, without an umbrella build. Global formal lint passes.
The first 27 new public declarations passed one external axiom audit;
the remaining 12 passed their separate audit. All 39 use only propext,
Classical.choice and Quot.sound. No old declaration is re-audited.
The declaration index is refreshed. The known Lake
packaging audit remains pending to avoid its broad stale prerequisite
rebuild. No numerical experiment, computed premise, added axiom, or
unfinished proof is used.

## Physical landing and remaining arithmetic obstacle

The physical target is

`W_P(Y)=integral_1^infinity G_P(Y*x)*G_P(x)/x^3 dx`.

The [physical dilation theorem](ccm-fu-fixed-core-physical-dilation-mean.md)
proves F_P(s)=mellin(G_P)(-s) throughout Re(s)>1/2 and logarithmic L1/L2
membership for every positive dilation. Polarized Mellin-Plancherel,
with the scaled real head in its conjugated slot, identifies the complete
W_P(exp(a)) with M_P(a). Thus the residue limit applies to the actual head.

The scalar sign and discrete correlation integral are closed. Renewal
remains open: the core and cutoff dependence of
the asymptotic must be controlled along the actual changing selection.
No fixed-core contour estimate here is claimed to settle that uniform
arithmetic obstacle or RH.

# TH: nonlocal C5 compensation from the complete source defect

- **ID:** TH-C5-nonlocal-defect-transport
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** theta-c5-curvature-defect-growth.md; route TH in docs/reports/rh-current-frontier-map.md
- **Statement:** The literal completed compensation margin is positive throughout 0<t<u.

## Goal
Close the finite-displacement C5 producer. Global seventh-order source growth and exact completed seam orientation are proved; neither implies this nonlocal statement without a new argument. Arbitrary-packet/all-degree positivity and RH remain separate.

## Gates
- [x] 0 → 1: precise literal source statement and transport attack
- [ ] 1 → 2: dependency-closed paper proof
- [ ] 2 → 3: final leaf audit with lake --old env lean and standard axiom audit
- [ ] 3 → 4: publication-ready exposition

## Certified source inputs
Write L=log(theta source), c=-L2, v=c', b=c''-4c, H=L5-4L3=-b'. On x>0, c>18, v>0, b>0, H>0, v<2c, H'>f1 H, H''<beta H, and 18c+4+6f1-beta>0. The exact C5 seam orientation is a sum of positive terms under these inequalities; GrowthSeamOrientation supplies that theorem and a local positive direct-J chamber at every positive center. Its normalized sixth invariant is strictly increasing. Global sixth source curvature positivity already exists in ThetaCuspFullReflectionSixthGlobal.

## Exact nonlocal target
For fixed u and displacement t, put Q=thetaCuspReflectedLogAction u t, a=Q_t, v=t*a, s=Q_u, K=t*a*s_t-(a+t*a_t)*s, P=K+t*K_t, F=-K>0. The existing complete gate is

    M=5P-(14+10v+8v/(exp Q-1))*K
     =(W-30)*F-5*(t*F_t-5F).

Conjecture N1 (stronger, retaining coupled cancellation):

    R=5*Q*P-(14*Q+6*v*Q+8*v)*K > 0.

The Padé/Bose inequality 1/(exp Q-1)>=1/Q-1/2 for Q>0 would give M>=R/Q because K<0. This is a proposed sufficient producer, not proved.

R is exactly the second-order expression

    5*Q*t^2*a*s_tt - t*a*(9*Q+6*v*Q+8*v)*s_t
      + ((14*Q+6*v*Q+8*v)*(a+t*a_t)
         -5*Q*(a+3*t*a_t+t^2*a_tt))*s.

Equivalently, K=(t*a)^2 * d_t(s/(t*a)). The missing sign is a bound on the growth of this negative derivative; positivity of -K alone loses that information.

## Active proof attack
Preserve the complete reflected source while transporting the defect inequalities. The exact wave relation is Q_tt-Q_uu=2*c(u). The reflected fourth-order relations on 0<t<u are

    Q_tttt-4Q_tt = b(u+t)+b(u-t)>0,
    s_tttt-4s_tt = -H(u+t)-H(u-t)<0.

These are identities derived from c''=4c+b and c'''=4c'-H, not a solution of the compensation inequality. Seek a positive integral/Green representation of R with coupled H' and H'' remainders. A blanket local-to-global implication from seam orientation has not been proved. A separated high-jet absolute-value estimate discards the zero-displacement cancellation.

## Prior-search checks
Corpus searches returned partial source-only snapshots1189738,1189756,1189781,1189830. Existing C5CompletedGateReduction gives the exact excess form and weaker sufficient absolute-growth bound. C5FixedActionDescentLemmas supplies only center negativity by two ratio descents. Fixed Bose shifted facewise cone is falsified (theta-c5-fixed-bose-shifted-cone.md); N1 retains the whole coupled gate and does not assume those faces. No claim of exhaustive novelty follows from partial search.

## Log
- 2026-10-02: created after global growth and all-center seam closure. N1 and its operator form are paper conjectures, not Lean producers. Finite-displacement transport remains the hard open problem.

### N2: actual weighted defect transport
The newly proved H''<beta H, with F''=beta F and H'>F'H/F,
forces Z=F H'-F'H to be positive and strictly decreasing. For 0<=a<b,
this should give strict finite-interval comparisons

    Z(b) * integral_a^b F(x)^(-2) dx
      < H(b)/F(b)-H(a)/F(a)
      < Z(a) * integral_a^b F(x)^(-2) dx.

This is the proposed source-specific nonlocal comparison for the Green
representation, not an N1 proof. Its proof retains the actual factor F and
complete source H. Corpus snapshot1189888 was partial; returned the new
pointwise comparisons and existing spectral Wronskians, no checked N2
producer. Formal audit of the finite-interval transport is next.

### Exact signed Green remainder to investigate
Let S=beta*H-H''>0. Since F''=beta*F, the flux obeys
Z'=-F*S. For a<x, integrating twice formally gives

    H(x)/F(x) = H(a)/F(a)+Z(a)*integral_a^x F(t)^(-2) dt
      - integral_a^x F(t)^(-2)*(integral_a^t F(s)*S(s) ds) dt.

Thus any nonlocal proof must preserve the negative Green remainder together
with its occurrence in the other factors of R. Replacing H and H' by
independent endpoint bounds may again discard the needed compensation.
This identity's iterated-integral transport has not yet been Lean-audited;
N2 is its strict endpoint consequence currently under audit.

### Two-stage integral descent retains a local positive kernel
The existing center-negativity proof descends the ratio
r3=o'/(2e+t e') twice, where e=(c(u+t)+c(u-t))/2 and
o=(c(u+t)-c(u-t))/2. Its positive derivative numerator is

    J3 = o'*(3e'+t e'')-o''*(2e+t e')
       = [3*(v_plus^2-v_minus^2)
          -2*(B_plus-B_minus)*(c_plus+c_minus)
          +2*t*(v_plus*B_minus+B_plus*v_minus)]/4,

with B=c''. The corpus proves J3>0. It has a simple zero in t at zero;
the two integral descents produce the order-five zero of -K. This
identifies a concrete transport target: control the growth of J3 while
retaining the varying denominators of both descents. The sign J3>0
alone does not bound that growth. No monotonicity of J3/t or of the
normalized r3 derivative is assumed. Such stronger signs may be false
and are not needed unless derived from the complete source.

N2 certified: ThetaCuspCurvatureDefectSturmTransport scratch5107 exit0, standard3 on flux monotonicity/positivity and normalizedSourceDefect_strict_clock_bounds. Final41396 exit0 empty log, umbrella wired. N1 remains conjectural.

### New positive representation of the local kernel (paper, unaudited)
For y=u-t, x=u+t, use b=c''-4c and H=-b'. The exact energy
(v^2-4c^2)'=2v*b rewrites the two-point curvature gain as

    Qgain(y,x)=integral_y^x (8*c*v+6*b*v)
                 +2*(c(x)+c(y))*integral_y^x H.

Therefore

    J3(u,t)=integral_(u-t)^(u+t) [v(r)*(8*c(r)+6*b(r))]/4
      +(c(u+t)+c(u-t))*integral_(u-t)^(u+t) H(r)/2
      +t*(v(u+t)*B(u-t)+B(u+t)*v(u-t))/2.

Every term is positive on 0<t<u. Unlike the previous two-point-gain
estimate, this retains an explicit H contribution to the kernel whose
growth must be controlled. This identity is paper-derived from the
literal sources; it is NOT yet Lean-audited and positivity of J3 itself
was already known. Do not mistake it for the remaining growth sign.

For A=v*(8c+6b), exact differentiation gives

    A''=v*(128c+48b)-H*(56c+18b)-6v*H'.

The new source inequalities control the adverse H' term together with
H'' in the H part of J3. Next task: retain the endpoint dependence of
c(u+t)+c(u-t) and both ratio-descent denominators when transporting
these inequalities into R>0. Dropping those dependencies would be a
new unproved comparison, not a valid proof.

For the local coupled density A+k*c*H the exact second derivative is

    (A+k*c*H)'' = v*(128c+48b)
      + H*((-56+4k)*c+(-18+k)*b)
      + (-6+2k)*v*H' + k*c*H''.

At k=3 the H' term cancels. Since beta<18c (the proved reserve and
f1<-4 imply this), c>18 and b,v,H>0 give the paper inequality

    (A+3cH)'' < 18c*(A+3cH).

This is an actual source subsolution candidate, not yet Lean-audited.
It does not immediately control J3: its H coefficient is the varying
endpoint sum, not 3c at the integration point. That mismatch must be
resolved before claiming progress on the full compensation producer.

### N3: positive single-integral descent, exact paper proof
Set D1=tE, D2=E+t e, D3=2e+t e', N=O, r=o'/D3,
and w=-r'=J3/D3^2. Unlike D1,D2, D3 is strictly positive at zero.
For 0<=s<=t define

    K(t,s)=D2(t)*D1(s)+D2(s)*((t-s)*D2(t)-D1(t)).

Then K(t,0)=K(t,t)=0, K_s=D3(s)*((t-s)*D2(t)-D1(t)),
and K_t=D3(t)*(D1(s)+(t-s)*D2(s)). Moreover

    K(t,s)=D1(s)*(D2(t)-D2(s))
      +D2(s)*(D1(s)-D1(t)+(t-s)*D2(t))>0 for 0<s<t,

by strict increase of D2. The explicit primitive

    o(s)*((t-s)*D2(t)-D1(t))+O(s)*D2(t)-r(s)*K(t,s)

has derivative w(s)*K(t,s), is zero at zero, and equals
O(t)*D2(t)-o(t)*D1(t) at t. Consequently

    -completedCenterNumerator(u,t)=4*integral_0^t w(s)*K(t,s) ds.

This avoids both intermediate singular denominators and retains the
complete positive source density. Formal audit is the next construction.
The full compensation sign becomes a signed integral involving
((W-5)/(5t))*K-K_t; its integrand is not pointwise positive near s=t.
Controlling the actual density w across that sign change remains essential.

N3 scratch55377 exit0: positive kernel, actual positive density, and exact
single-integral representation all have only standard Lean axioms.
The earlier failures were `id s` normalization and FTC integrability
argument order, now repaired. Final leaf packaging awaits the companion
outer-derivative identity needed by the compensation integral.

### N4: source-density shape, conjectural
Test strict decrease of w(u,s)/s, not merely w>0. The zero-displacement
fourth coefficient of r=o'/D3 has numerator

    T=c^2*c'''''-12*c*c''*c'''+24*c'*(c'')^2-3*c*c'*c''''.

At u=0, T=0 and T'=c^2*c''''''-15*c*c''*c''''+24*(c'')^3.
The corpus's exact modular even jets permit a symbolic sign audit of
this necessary local condition before any global density-shape claim.
N4 remains unproved; the full C5 gate does not follow from N3 alone.

Additional kernel identity on paper: K(t,s) equals
integral_(a=0)^s integral_(b=s)^t (b-a)*D3(a)*D3(b) db da.
The square [0,s]^2 cancels by antisymmetry. This representation may
transport coupled growth without separating the two denominator factors.

N3 companion scratch62594 exit0, standard3: exact positive integral
for -K_t and strict K_t<0 on 0<t<=u. The full compensation is exactly
4*integral w*((W-5)*Green-5*t*Green_t); this assembly is now under audit.

### Retain the coupled density curvature
The N4 local numerator is the derivative of a source invariant:

    T=c^5 * d_x[(c*c''''-6*(c'')^2)/c^4].

Let J=2*c'*c''-c*c''' >0. Direct algebra relates it to the already
proved exact seam orientation S:

    S=T+(18*c^2-10*c'')*J.

Thus S>0 alone does not imply T>0; replacing the coupled condition by
bare density monotonicity strengthens the problem. For w/s, the local
squared-displacement coefficient after multiplying by exp(-k*Q) has
sign opposite T+6*k*c^2*J. This identifies the normalization that the
finite-displacement transport must retain. No global N4/N1 claim.

The new kernel also has an exact positive Wronskian:

    (Green_t)_s*Green-Green_t*Green_s
      =D3(t)*D3(s)*D1(t)*D1(s)>0.

Consequently Green_t/Green strictly increases with s on (0,t), and the
compensation kernel divided by Green strictly decreases. The signed
kernel has at most one zero; its value at s=t is strictly negative.
The remaining task is actual source-density control across that single
sign change, not a pointwise-positive integrand proof.

### N5: Euler transport keeps the endpoint cancellation
Paper identity, not yet Lean-audited. Write F=-K=4*integral w*G.
Since G vanishes at both endpoints, integration by parts gives

    t*F'-5F = 4*integral_0^t
      [(s*w'-w)*G+w*(t*G_t+s*G_s-3*G)] ds.

The Euler combination G_t and G_s cancels the adverse diagonal term.
It is incorrect to bound G_t alone by a positive multiple of G there.
For fixed center let B=c'', J=2*c'*B-c*c''', and T as above. The
zero-displacement expansions derived from the literal jets are

    w(s)/s = J/(2*c^2)-T*s^2/(12*c^3)+higher order,
    G(t,s) = 2*c^2*t*s*(t-s)*
      [1+(B/(2*c))*(t^2+t*s/3+s^2)+higher order].

The leading measure w*G has shape s^2*(t-s), whose normalized first
and second moments in s/t are 3/5 and 2/5. Keeping these moments
recovers exactly T+(18*c^2-10*B)*J=S as the seam condition.
Replacing that average by a pointwise bound imposes a stronger,
unproved condition. Next attack: retain this weighted cancellation
at finite displacement using the actual source Sturm inequalities.
This is an analytic derivation, not a formal full-gate proof.

N4 necessary source test is now certified: sourceCenter_densityShape_pos
in ThetaCuspC5DescentDensitySeam proves the exact unconditional
c(0)^2*c''''''(0)-15*c(0)*c''(0)*c''''(0)+24*c''(0)^3>0.
Scratch51046 and final81072 both exit0; standard3 axiom audit; wired.
This does not prove global decrease of w/s. Earlier bound-free shifted
polynomial positivity was too strong as a method: its nonconstant
coefficients have negative sign. The already-proved actual modular
interval (191/10,96/5) closes this literal source test with a symbolic
polynomial certificate, without a new numerical approximation.

### N6: linear source-forced form for the missing comparison (paper)
Keep u,t fixed, write j=c'(u), and H_e(s)=(H(u+s)+H(u-s))/2.
The actual odd primitive satisfies O''''-4O''=-H_e, with
O(0)=O'(0)=O'''(0)=0 and O''(0)=j. Exact Duhamel integration gives

    O(t)=j*(cosh(2t)-1)/4
      - integral_0^t H_e(s)*(sinh(2(t-s))-2(t-s))/8 ds,
    o(t)=j*sinh(2t)/2
      - integral_0^t H_e(s)*(cosh(2(t-s))-1)/4 ds,
    n(t)=j*cosh(2t)
      - integral_0^t H_e(s)*sinh(2(t-s))/2 ds,

where n=o'. Put A=(W-5)*D2(t)-5*t*D3(t), B=-(W-5)*D1(t),
C=5*t*D1(t)>0, and

    Gamma(l)=A*(sinh(2l)-2l)/8+B*(cosh(2l)-1)/4+C*sinh(2l)/2.

Then the exact missing gate has the paper representation

    M/4 = j*Gamma'(t)-integral_0^t H_e(s)*Gamma(t-s) ds.

Gamma(0)=0, Gamma'(0)=C, and Gamma''-4Gamma=A*l+B. This keeps
H linear and may permit direct use of H''<beta*H and the signed Sturm
remainder. The hard task is to construct the actual adjoint weight
with the needed sign and control its boundary terms, not to assume
Gamma has a favorable sign. N6 is paper-derived and unaudited;
it is not a claimed inequality or a replacement hypothesis for RH.

### Closed subattempt: pointwise-positive Green compensation
**FAIL:** compensationGreenKernel(u,t,t)<0 for every u and t>0.
A pointwise-nonnegative integrand proof cannot supply this gate.
**Positive survivor:** compensationGreenRatio_strictAntiOn proves that
the compensation kernel divided by the strictly positive Green kernel
strictly decreases on (0,t). Hence there is at most one sign crossing,
and it can only run from positive to negative. The exact same actual
density represents both -K and -K_t, retaining the weighted comparison.
**Lean status:** scratch59522 exit0; all nine principal endpoints have
only propext, Classical.choice, Quot.sound. PositiveDescentIntegral
final leaf audit remains pending at this log entry. N1/RH not proved.

Final validation: PositiveDescentIntegral final69274 exit0 empty log,
wired; DensitySeam final81072 exit0, wired. Principal axiom audits
standard3. Formal lint15487 still reports11 unrelated unreachable
modules; neither new leaf has a lint error. N1/full C5 and RH remain open.

### N7: curvature of the positive source drive (paper proof)
The corpus's projective potential 3(c')^2-2c*c'' has derivative 2J,
where J=2c'c''-c*c'''>0. This is the leading coefficient source for
-K and its second derivative has an exact cancellation:

    J'=2(c'')^2+c'*c'''-c*c'''',
    J''=5*c''*c'''-c*c'''''.

Using c''=4c+b and c'''=4c'-H,

    J=c'*(4c+2b)+c*H,
    J''=c'*(64c+20b)-(16c+5b)*H+c*H''.

Thus the already-proved H''<beta*H yields a new exact signed reserve

    16J+c*(beta-32)*H-J''
      =12*c'*b+5*b*H+c*(beta*H-H'')>0.

The source seam reserve then gives the strict actual subsolution
J''<18c*J: its positive remainder is

    c'*[(18c-16)*(4c+2b)+12b]
      +H*[c*(18c+16-beta)+5b]+c*(beta*H-H'').

This removes the troublesome H' term before finite-displacement
transport. Formalization is next. It does not itself imply the full
gate: the Green density and its two varying denominator factors must
still be transported together. Search75566 partial1190778 recovered
the older private projective potential, but no checked curvature result.

### N8: finite source-drive transport (dependency-closed paper proof)
Let P=3(c')^2/2-c*c'', so P'=J>0. For a fixed physical endpoint
0<T<u, set k=18c(u+T), Y(s)=P(u+s)-P(u-s). Then Y(0)=0,
Y(s)>0 for s>0, Y'=J(u+s)+J(u-s), and
Y''=J'(u+s)-J'(u-s). N7 and increase of c imply that
J'-kP strictly decreases on [u-T,u+T]; hence Y''<kY on (0,T].
For psi(s)=s*exp(k*s^2/6), psi''>=k psi and psi>0.
The Wronskian Y'*psi-Y*psi' strictly decreases from zero. Therefore

    T*(J(u+T)+J(u-T))
      < (1+6*c(u+T)*T^2)*(P(u+T)-P(u-T)).

This is an actual finite-interval growth comparison for the projective
potential contribution in the positive local Green density. It has no
assumed source sign and uses no numerical approximation. It still does
not transport the other coupled terms/denominators in J3 or prove M>0.
Formalization follows N7's derivative audit.

### N9: retain the density denominator in the next Sturm operator
A raw J3''<18*c(u)*J3 conjecture is not supplied by seam positivity.
The exact local limit instead satisfies

    lim_(t->0+) J3''(u,t)/J3(u,t)
      =18*c(u)+2*c''(u)/c(u)-S(u)/(c(u)*J(u)).

Because D3'/D3 ~ 2*c''(u)*t/c(u), the natural candidate is

    J3''-(D3'/D3)*J3' < 18*e*J3.

Its zero-displacement orientation is exactly the proved S>0. This
finite-displacement inequality remains conjectural. It must not be
replaced by the stronger unproved raw-curvature cap.
For n=o', d=D3 and g=d''-4d=8e+4b_e-t H_o, exact differentiation gives

    J3'=n*g+H_e*d,
    J3''-(d'/d)*J3'=-(g/d)*J3+n*g'+d*H_e'.

Here g'=8e'-5H_o-t H'_e. This form removes a varying-denominator
term before applying the actual H'/H'' comparisons. A proof of its
sign and its transport through both Green descents remain required.

Clearing the positive denominator in N9 gives the precise next source
inequality, not a conditional Lean receiver:

    (18*e*d+g)*J3-n*d*g'-d^2*H_e' > 0.

The highest source terms occur as a coupled H' endpoint difference;
retain it as an integral of H'' before invoking the proved source
reserve. Independent estimates on both endpoints would lose that
cancellation. N8 controls the projective-potential contribution of
J3, but does not establish this full coupled numerator.

### Positive affine adjoint for N9 (paper, not yet audited)
Set a=u-t, b=u+t and let p=e'. With the already-defined n,d, put

    weight(r)=d*(d-n*(r-u))/2  on [a,b].

This weight is strictly positive. Indeed convexity of c gives
2t*c'(a)<=c(b)-c(a), so

    d-t*n=c(b)+c(a)-t*c'(a)>=(c(b)+3c(a))/2>0.

Since n>0 in the physical chamber, this is the minimum weight endpoint.
An exact integration by parts converts the full N9 numerator to

    (18*e*d+g)*J3-8*n*d*p+6*n*d*H_o
      -integral_a^b weight(r)*H''(r) dr.

The source facts imply H''<(18c+4)H+6H'. This removes the highest
jet, but the remaining signed boundary terms cannot be discarded.
For their treatment, T=2c^2-c*c''+(c')^2/2 obeys

    T'=c*H,   T=((c')^2-4c^2)/2-c*b<0.

Thus both integrals of weight*cH and weight*H have exact lower-jet
primitives (T and -b). Their contributions to this lower bound after integration by parts
have positive signs. The unresolved part is the complete coupled
endpoint remainder; do not infer its positivity from the positivity
of the adjoint weight alone.

N7/N8 validation: scratch73952 exit0 with standard3 on the source
curvature reserve, actual second-derivative subsolution and finite
growth comparison. Saved ThetaCuspC5DescentDriveTransport; final36811
exit0 empty log, umbrella wired. N9 and full C5 remain unproved.

### N10: exact primitive comparison for the curvature defect
The coarse replacement H''<(18c+4)H+6H' loses useful cancellation in
N9's adjoint remainder. Retain the proved factor slope f explicitly.
With q=pi exp(2x)-3/2, F=864(q+3/2)^2(q+3)/q^5 and R=H/F,
the corpus proves R'>0 and b=c''-4c>0, b'=-H. The exact primitive

    G(q)=216(q+3/2)^2/q^4,  d_x G(q(x))=-F(q(x)), G->0

suggests the strict actual comparison

    b>G*R, hence H<(4+12/q)*b, and (b/G)'>0.

Dependency-closed paper proof (no unproved source tail limit): for fixed
x>=0 and r=R(x), y->b(y)-rG(y) is nonincreasing on [x,infinity), since
its derivative is F(y)(r-R(y))<=0. Thus -rG(y)<b(x)-rG(x). Take y to
infinity using only G->0 to get b(x)-G(x)R(x)>=0. The derivative of
C=b-GR is -G R'<0; apply nonnegativity at x+1 to get C(x)>0.
This exact relation, not a numerical bound optimization, may control
N9's adverse endpoint terms while retaining source dependence. It does
not yet prove N9, full compensation or arbitrary-degree positivity.
Search57622 completed0, partial generation1191071/source-only candidates:
curvatureDefect positivity/monotonicity and existing normalized-source
Sturm transport; no checked primitive-comparison endpoint supplied.

### N9 closure candidate: coupled adjoint absorption (paper, audit pending)
N10 is now Lean-certified (scratch22024 standard3; saved leaf final65201
exit0). It supplies a missing sign in the following complete candidate
proof of N9. Every identity below still needs its own Lean audit.
Let a=u-t>=0, b=u+t, c_a=c(a), c_b=c(b), v=c', B=c'', and
I_H=integral_a^b H. Continue n=(v_b+v_a)/2, p=(v_b-v_a)/2,
e=(c_b+c_a)/2, o=(c_b-c_a)/2, d=2e+t p, J3=n d'-n'd.

1. Finite projective endpoint reserve:

    c_b^2-c_a^2 > (b-a)*c_a*v_b.

To prove it, B/c decreases and c increases, so for a<=r<=b,
c_b B(r)>=c_a B(b). Integrate v'=B to get
(b-a)c_a B(b)<=c_b(v_b-v_a). The derivative in b of the displayed
reserve is therefore at least (c_b-c_a)v_b+c_b v_a>0. It starts at0.
Consequently (d+t n)/2 < e^2/c_a. Also n<2e<=2e^2/c_a.

2. The factor combination is decreasing and has the exact expansion

    beta(q)-6f(q)
      =40+240/q+48/(q+3)+270/q^2+90/(q(q+3)) <324

for q>=8/5; clearing denominators after q=8/5+y leaves a polynomial
with positive coefficients. Since c_a>18, for every r in [a,b],

    ((d-n(r-u))/2)*beta(q(r))-3n*f(q(r)) <18e^2.

Here beta>0, f<0, and the endpoint reserve bounds the positive affine
weight. This is the coupled factor estimate; replacing fH by H' too
early would lose it.

3. The coefficient g=8e+4b_e-t H_o is positive. N10 gives
H(b)<(4+12/q(b))*b(b). Since b decreases and v'=4c+b,
2t*b(b)<v_b-v_a<=v_b. Also q(b)>6b>=12t follows from exp(2b)>=1+2b
and pi>3. Thus t H_b/2< v_b+b_b/2 <2c_b+b_b/2, while H_a>=0.
It follows directly that 8e+4b_e-tH_o>0.

4. The lower-jet part A=J3-e I_H satisfies A>np. Indeed

    A=3np-8eo+4t(en-op)+t(n b_e-p b_o),
    np-4eo=(1/2) integral_a^b v*b >0.

Both endpoint terms are positive: en-op=(c_a v_b+c_b v_a)/2 and
n b_e-p b_o=(v_b b_a+v_a b_b)/2.

5. Apply H''<beta H and H'>fH in the positive affine adjoint identity,
keeping both integrals coupled. Step2 gives

    M9 >18ed*(J3-e I_H)+g*J3-8ndp
       >ndp*(18e-8)+g*J3 >0.

All quantities have established source signs in the physical chamber.
This would prove the actual N9 denominator-coupled Sturm inequality,
not just its zero-displacement limit. Formalize steps1--5 next. Full C5
compensation still requires transporting this inequality through the
Green descent; arbitrary-degree positivity is also still open.

Integral-free audit form of N9: freeze u,t,e,n,d and let
w(r)=d*(d-n*(r-u))/2. Define

    T(r)=w(r)*H'(r)-(5/2)*n*d*H(r)+18*e^2*d*b(r).

Then T'=w H''-3nd H'-18e^2d H<0 by step2 and the actual source
comparisons. T(b)<T(a) says directly that

    d^2 H_e'-ntd H'_e-5nd H_o <18e^2d*(b_a-b_b).

Thus no new interval-integral infrastructure is needed. Also
np-4eo>0 follows from strict increase of v^2-4c^2, whose derivative
is 2vb>0. These exact monotonicity statements give the same positive
M9 decomposition while avoiding repeated FTC bookkeeping.

### N11: transport the coupled Sturm sign through the Green descent
N9's finite algebraic reserve is certified in scratch96096 (standard3);
the derivative bridge and saved-leaf audit are still pending. The next
actual source conjecture remains the stronger intrinsic compensation

    (9Q+6QV+8V)*F-5Qt F' >0,
    F=-centerNumerator, Q=reflected action, V=t Q'.

It is equivalent to strict decrease of

    F^5 / (t^9 Q^8 exp(6Q)),

and implies full compensation via the Bose lower comparison already
identified in N1. Keep the V/Q contribution: replacing W-30 by12Q
loses a curvature term even at the seam. Explicitly, with B=c''(u),
W-30=(12c+4B/(3c))*t^2+..., whereas 12Q starts at12c*t^2.
Thus the bare Bose floor cannot by itself transport the exact N9 seam
orientation. No implication N9=>full compensation is yet proved.

An exact inversion of the positive Green representation is useful here.
Writing D1=tE, D2=D1', d=D2', and F=-K gives

    4 D1^2 J3 = d D1 F''-(d' D1+d D2)F'+d^2 F.

This follows by eliminating O from F/4=D2 O-D1 O' and
F'/4=d O-D1 O''. It supplies a concrete way to test the explicit
comparison profile t^(9/5) Q^(8/5) exp(6Q/5): form its inverse image
under this second-order operator, then prove the required coupled Sturm
supersolution and positivity. These signs have not been established;
this is the next hard mathematical task, not a new assumed receiver.

N9 full scratch audit63938 exited0. sourceCurvature_endpoint_reserve,
descentAuxiliary_pos, localDescentSturmReserve_pos and
localDescentNumerator_sturm_subsolution all report exactly standard3.
Thus the actual finite-displacement denominator-coupled Sturm conjecture
is now Lean-proved, including its derivative bridge. Saved
ThetaCuspC5CoupledSturmTransport; final leaf audit is pending. N11,
full C5 compensation and arbitrary-degree positivity remain open.

Final N9 audit45399 exited0 with empty log. Both new leaves are wired
into RHTower.lean; no umbrella build. Global lint74281 exited1 with12
unrelated unreachable modules (see /tmp/th-c5-coupled-sturm-lint-final.log),
none in these two leaves. N9 is fully certified; N11 remains open.
Search36379 completed0, partial generation1191421, source-only Green/Bose
candidates; no checked transport closure was returned.

### N12: retain the exact denominator clock in the Green comparison
N11 remains open. A Gaussian numerator supersolution grows too quickly
under Green integration; near the constant-curvature seam, its Gaussian
mixture has an extra positive variance term. Do not infer the full gate
from that profile. The exact rational-action inverse profile remains a
candidate, with its fourth-order supersolution sign still unproved.

New source-based comparison: fix u>0, c0=c(u), k=sqrt(9/(2c0)),
y(t)=D2(u,t)=E+t e, y'=d. Convexity of c gives e(t)>=c0, and
p=e'>=0 gives d>=2e. Therefore k^2*d^2>=18e. The explicit
psi(t)=sinh(k*y(t)) satisfies

    psi''-(d'/d)psi'=k^2*d^2*psi>=18e*psi.

N9 and positivity of J3,psi imply that

    (J3'*psi-J3*psi')/d

strictly decreases from zero on [0,u]. Thus J3/psi strictly decreases
on (0,u]. This is an actual finite-displacement density order in the
source's denominator clock, not a Gaussian bound in displacement.
Its positive Green pushforward gives a candidate explicit upper
elasticity comparison for F=-K. That comparison still needs to be
combined with the full Bose weight to close N11/full C5.

N12 first scratch audit98975 exit0: the clock Wronskian is negative and
J3/sinh(k D2) strictly decreases on the whole (0,u]; both endpoints
standard3. Green pushforward paper proof: A=J3/d^2, B=psi/d^2, G=Green,
T=Green_t. For a<b, A(a)B(b)-A(b)B(a)>0 and
G(a)T(b)-T(a)G(b)>0. Their product is symmetric and nonnegative on the
closed square, positive off the diagonal in the interior. Its double
integral equals twice

    (integral AG)*(integral BT)-(integral AT)*(integral BG)>0.

Thus if F0=4 integral BG and F0_outer=4 integral BT,

    F' * F0 < F * F0_outer.

No numerical quadrature or assumed covariance sign enters. The current
scratch is auditing this exact positive Green transfer. It compares
actual flux growth against an explicit hyperbolic-sine integral; it does
not yet prove that this comparison flux satisfies the Bose budget.

### N13: the explicit denominator-clock Bose budget (open)
N12's Green growth comparison and full Bose transfer now have standard3
in scratch80655; the scratch exited1 only on a positivity lemma's Pi
normalization. A derivative bridge for the moving-endpoint comparison
integral is being audited next.

The remaining candidate is actual M0=(W-5)F0-5t F0_outer>=0 throughout
0<t<u, where B(s)=sinh(k D2(s))/d(s)^2, k^2=9/(2c(u)). Then N12's
strict transfer, F>0 and F0>0 would prove actual full compensation.
This is a concrete source integral sign, not an assumed gate.

A useful exact scalar form retains both geometry and source weight.
Let I1=integral B(s)D1(s), I2=integral B(s)D2(s),
I3=integral s B(s)D2(s), and A=I1+t I2-I3>0. Then

    F0=4(D2(t)A-D1(t)I2),  F0_outer=4d(t)A,
    M0/4=((W-5)D2(t)-5t d(t))*A-(W-5)D1(t)*I2.

Thus the outstanding sign is a weighted-mean bound for
x(s)=s-D1(s)/D2(s), whose derivative is D1(s)d(s)/D2(s)^2>0:
A/I2=t-(weighted mean of x), weight B(s)D2(s). This form avoids
separately bounding the negative endpoint part of the Green kernel.

Keep k's actual center dependence and t<=u. A growth objection based
on holding k fixed while letting t exceed u does not apply to the
physical chamber. The source identity c''-4c>0 suggests proving
c(u)>c(0)cosh(2u) by its positive hyperbolic Wronskian, if a global
clock-size comparison is needed. That source comparison is not yet
formalized here. N13 has no proof yet; RH and all-degree positivity
remain open.

N13 local diagnostic (paper algebra, NOT Lean-audited): writing
c=c(u), B=c''(u), C=c''''(u), the clock model has
F0=positive_constant*t^5*(1+A t^2+D t^4+...), with

    A=6c/5+2B/(15c),
    D=81c^2/140+59B/140+C/(42c)-31B^2/(1260c^2).

The first nonzero candidate coefficient of
((W-5)F0-5t F0')/F0 is

    (1311c^4-1017c^2 B-122c C+176B^2)/(315c^2) * t^4.

This is a diagnostic for the comparison model, not another proof of
the already-positive actual seam. Verify the formal series algebra and
its literal-source sign before claiming a local N13 chamber. The full
finite-displacement weighted-mean sign remains the primary target.

N12 complete scratch audit4542 exited0. denominatorClockWronskian_neg,
denominatorClockSourceRatio_strictAntiOn, denominatorClockGreen_growth_comparison,
denominatorClockGreenMass_pos, denominatorClock_compensation_transfer and
hasDerivAt_denominatorClockGreenMass all report standard3 only. Saved
ThetaCuspC5DenominatorClockComparison; final94111 and lint14270 pending.
The comparison mass's derivative is exactly its defined outer integral,
including the moving endpoint. The full Bose transfer now reads

    F*M0 < actualCompensation*F0,

with F=-K>0 and F0>0 on the physical chamber. No sign for M0 is assumed
or proved. N13 is therefore the precise remaining comparison-sign task.

Final N12 audit94111 exited0 with empty log. Saved leaf is wired once;
no umbrella build. Global lint14270 exit1 reports13 unrelated unreachable
modules, none in this new leaf. Full error list is retained in
/tmp/th-c5-denominator-clock-lint-final.log. N12 is fully audited; N13's
comparison-compensation sign and arbitrary-degree positivity remain open.
Search71459 completed0, partial1215499; no checked N13 closure returned.

### N14: actual-source orientation of the N13 diagnostic
Target the full source invariant

    P=1311c^4-1017c^2*c''-122c*c''''+176(c'')^2 >0

on x>=0. This removes a source-sign obstruction in the comparison model;
it is not a claim that the diagnostic expansion or full N13 is proved.
Dependency-closed paper proof: exact modular raw jets give
c''(0)<9c(0). Decrease of c''/c propagates this relation globally.
The exact N10 slope comparison and positive defect Sturm flux give
c''''<4c''-f*(4+12/q)*(c''-4c). The explicit factor identity
-f*(4+12/q)=16+120/q+180/q^2<162 on the actual q>=8/5 yields
c''''<846c. Together with c>18, the adverse terms in P are absorbed by
c^2*(1311c^2-9153c-103212); after c=18+z this bracket is
1311z^2+38043z+156798>0. The numerical envelopes are private proof
steps; the research target is the literal full-source invariant P>0,
not an optimized bound. Formalize this sign, then verify its relationship
to the actual comparison germ before using it in a global N13 proof.

N13 canonical-clock formulation (paper, no sign conclusion): fix u,t and
write y(s)=D2(s), d=y', k^2=9/(2c(u)),
A=(W-5)y(t)-5t d(t), C=(W-5)D1(t). The compensation kernel is

    H(s)=A*(D1(s)+(t-s)y(s))-C*y(s).

Its derivatives in the clock coordinate satisfy

    dH/dy=A*(t-s)-C,   d^2H/dy^2=-A/d(s).

The actual comparison integral is 4 integral sinh(k y)*H(y)/d(y)^3 dy.
This retains the essential interaction between kernel curvature and
clock damping. If A>0, H is concave and its signed endpoint cannot be
discarded. Concavity alone does not prove the weighted integral sign.

N14 source invariant certified: scratch57076 exited0; both public positive
endpoints report only propext, Classical.choice, Quot.sound. Saved
ThetaCuspC5ClockSourceOrientation; final leaf55454 exited0 with empty log,
exact umbrella import added once. This proves the literal source invariant
P>0 and the algebraic candidate coefficient P/(315c^2)>0. It does not
identify that coefficient with the analytic clock-model germ, establish
N13, or imply arbitrary-degree positivity/RH.

N13 clock-dilation search50347 exited0: partial generation1215672,
source-only N12 and elementary jet-scaling hits; no checked N13 closure.
Paper test of dropping clock damping fails as a sharp comparison:
using x(y) concavity and replacing d(y)^(-3) by a constant gives
(t*d/y)*[1+z*(z*cosh(z)-sinh(z))/(z*sinh(z)-2*cosh(z)+2)], z=k*y.
Its t^2 coefficient contains 5*c''/(3c), exceeding the needed
4*c''/(15c). This rejects only that relaxed bound, not N13. Retain
weight variation and Green shape together in the next adjoint proof.

### N15: positive inverse-Green source for the intrinsic action profile
Keep the N13 sign as the target. Candidate F*=t^(9/5)*Q^(8/5)*exp(6Q/5)
has logarithmic derivative h=9/(5t)+12E/5+16E/(5Q), E=Q'/2.
Write D1=tE, y=E+t e, d=2e+t p, d'=3p+t r, e=E', p=e', r=e''.
Its inverse Green source is F*R/(4D1^2), where

    R=d D1*(h^2+h')-(d'D1+d y)*h+d^2.

New dependency-closed PAPER sign proof, audit pending: R>0 on0<t<=u.
The full source gives p<2e, r<9e, d>=2e, E>=c(u)t>18t. Hence

    t*d'/d < 1+3tE/8,

using 3t<=1+9t^2/4. Set Z=tE>0, gamma=tE/Q>=1,
alpha=t e/E>0, beta=t^2 p/E>=0, D=2alpha+beta.
Then R=(E^2/t^2)*D times a quantity strictly greater than

    [ (243/2)Z^2+354Z*gamma+(633/8)Z
       +96gamma^2+128gamma-54+5alpha+25beta ]/25 >0.

This is positivity of the actual inverse-source reserve, not a claim
that the profile is a supersolution. That remaining global differential
obligation is explicit: with m=h-2y/D1,

    R''+(2m-d'/d)R'
      +(m'+m^2-(d'/d)m-k^2*d^2)*R >=0.

It is exactly the denominator-clock Sturm operator applied to the
positive inverse source after removing F*/(4D1^2). Near-zero matching
alone cannot prove this sign. It remains the next hard nonlocal task.
Serena find_symbol rejected the new Lean path as ignored; the small
visibility edit exposing the reused projective ceiling uses exact text.

N14 public-helper leaf audit75591 exited0 with empty log. Lint45078 exited1 with12 unrelated unreachable modules, listed in /tmp/th-c5-clock-source-orientation-lint.log; no new-leaf error. The earlier count13 changed because CCMOutgoingQuantileEntropyDebit is now reachable. N15 scratch is auditing the denominator budget, its exact logarithmic-rate derivative, and the positive inverse-source reserve.

N15 comparison endpoint also has a PAPER Bose certificate:
W-5-5t*h=2tE*[4+8/(exp(Q)-1)-8/Q]>=0,
since multiplication by Q*(exp(Q)-1)>0 gives four times the
existing exp_padé_floor. Thus F* meets the full Bose budget.
This is being added to the Lean audit after the positive inverse-source
reserve. Still missing: comparison of the inverse source with psi.
A weaker sufficient target than its full Sturm supersolution is

    psi*R'+(m*psi-psi')*R >=0, m=h-2y/D1,

which is the derivative of the inverse-source/psi ratio after removing
positive factors. The fourth-order supersolution test remains another
route to this same comparison. Neither has been proved. Green recovery
of F* also requires its zero-endpoint behavior, not merely the inverse
operator identity.

Search49636 exited0, partial generation1215779: source-only action-jet
and Green-operator analogues, no checked inverse-profile sign closure.
Scratch29532 and39284 exited1 on Lean normalization/elaboration errors;
no mathematical counterexample. Corrected scratch47551 is pending.

### N16: direct normalized inverse-source order (next hard conjecture)
Prefer the first-order comparison to introducing a stronger fourth-order
requirement. With J*=F*R/(4D1^2)>0 and psi=sinh(k*y), target

    psi*R'+((h-2y/D1)*psi-psi')*R >0 on0<t<=u.

This is exactly strict increase of J*/psi after multiplication by
positive factors. Coupled with zero-endpoint Green recovery of F* and
N15's Bose certificate, it would prove N13. No implication is asserted
without this sign and endpoint recovery.
Useful PAPER differential identities for the actual positive reserve:

    R'=(d'D1+d y)*h^2+dD1*(2h h'+h'')
       -(d''D1+2d'y+d^2)*h+2d d',
    h''=18/(5t^3)+12p/5+16p/(5Q)-96E e/(5Q^2)+128E^3/(5Q^3),
    d''=4r+t e''',
    e'''=4p-(H(u+t)-H(u-t))/2.

The last identity retains the actual N10/Sturm defect transport instead
of replacing the clock weight by a constant. N14 also provides the
private source bound c''''<846c if an integrated remainder comparison
is needed. Effort or missing corpus lemmas are not grounds to retire
this finite-displacement sign problem.

N15 scratch47551 exited0: positive inverse-Green reserve and literal
second-order operator, with derivative bridges, all standard3. Extended
scratch54256 exited0: intrinsicActionInverseSource_pos and
intrinsicActionProfile_bose_budget also standard3. Saved
ThetaCuspC5IntrinsicActionProfile; final leaf63547 pending. The saved
version removes only API-check examples, axiom-print commands and
reported redundant simplification tactics. No heartbeat overrides.
The candidate is an actual positive full-chamber inverse source meeting
the Bose budget, but its ordering relative to psi remains open (N16).
N14's analytic germ identification, N13, full C5, all-degree positivity
and RH are not proved.

N16 PAPER analytic tool candidate (not yet Lean-audited): a rational
hyperbolic envelope retaining the first three nonconstant seam terms,

    z*cosh(z)/sinh(z) < (105+45z^2+z^4)/(105+10z^2), z>0.

Dependency-closed sign proof by a positive derivative chain:

    j=z*cosh(z)-sinh(z),                    j'=z*sinh(z),
    h=(z^2+3)*sinh(z)-3z*cosh(z),            h'=z*j,
    g=(z^3+15z)*cosh(z)-(6z^2+15)*sinh(z),   g'=z*h,
    f=(105+45z^2+z^4)*sinh(z)
      -(105z+10z^3)*cosh(z),                f'=z*g.

All four vanish at zero, hence are positive at z>0. This envelope
preserves the negative quartic correction lost by the Gaussian coth
bound. Multiplying the desired inverse-source/psi comparison by the
positive rational denominator would leave an algebraic source-jet
inequality. Its sign still needs proof; the envelope alone is not N16.
Corpus search for an existing version is pending.

N15 saved leaf final63547 exited0 with empty log. Exact umbrella import
added once; no umbrella build. Scratch54256 axiom audits are standard3
for positive inverse source, literal inverse-Green operator, full Bose
budget, denominator budget and derivative/reserve endpoints. Owned
scratch and extension staging files removed after successful final audit.
N16 remains open; TH/RH goal is not complete.

N16 concrete next algebraic target: put w=9*y^2/(2*c(u)). It suffices to
prove

    (105+10w)*y*(R'+mR)-d*(105+45w+w^2)*R >=0.

The strict rational hyperbolic envelope and R>0 then give the strict
inverse-source/psi order. This preserves the finite clock and removes
hyperbolic quotients from the source-jet sign problem. For the constant
curvature diagnostic, let X=(6c/5)t^2 and P=1+3X/2+X^2/3. Clearing
the positive denominators reduces the normalized comparison to
(385/2)X^2+(415/2)X^3+25X^4>0. This diagnostic identity is PAPER only;
the actual varying-curvature algebraic target remains unproved.

Final lint31544 exited1:13 unrelated unreachable modules, none in the
new owned leaves; /tmp/th-c5-intrinsic-action-profile-lint.log has the
full list. Since lint45078, ThetaTailTransportPrimitiveFloor was added
to the reported unreachable set. No unrelated module was edited.
Search17707 exited0, partial generation1215924; coarse coth/CothInfra
hits, no checked sharp rational envelope. N16 paper derivative chain
and exact algebraic target are recorded above. All owned build/search
jobs are terminal; no temporary Lean/staging files remain from N14/N15.
Frontier TH updated; RN heading preserved. Goal remains active.

### N17: a globally linear hyperbolic comparison for N16
The old envelope grows like z^2/10; this is a potential obstruction to
its global use when the actual clock grows faster than sqrt(action).
No formal counterexample to the source-jet target has been claimed.
Use instead the PAPER bound

    z*coth(z) < (15+3z+6z^2+z^3)/(15+3z+z^2), z>0.

It retains 1+z^2/3-z^4/45 locally and grows linearly globally. Its
cleared error, after multiplication by 2exp(z), is

    F0=exp(2z)*(3z^2-12z+15)-(2z^3+9z^2+18z+15).

Let F1,F2,F3 be its first three literal derivatives. They vanish at0,
and F3'=48z^2 exp(2z)>0 forz>0; successive integration gives F0>0.
This is an exact analytic proof, not a numerical bound optimization.
It replaces N16's sufficient rational source target by

    (15+3z+z^2)*y*(R'+mR)-d*(15+3z+6z^2+z^3)*R >=0,
    z=k*y, m=h-2y/D1.

The actual source-jet sign is still open. The constant-curvature
comparison clears, after a positive z^4 factor, to

    11/90-19z/450+2z^2/135-z^3/1125+2z^4/10125
      =(z-19/10)^2/90+739/9000
        +z^2*(2*(z-9/4)^2/10125+73/27000)>0.

Both identities require Lean audit before reuse. Search29253 terminal0,
partial generation1215957, returns N15's positive inverse source and
N12's opposite source ratio order; no checked N16 comparison closure.

### N18: finite coupled shape cancellation inside N16
Normalize Z=tE, gamma=tE/Q, alpha=te/E, beta=t^2*p/E,
delta=t^3*r/E. The inverse source is exactly F*Rbar/(4t^4),
Rbar=R*t^2/E^2; hence its logarithmic derivative uses H-4+tRbar'/Rbar,
H=(9+12Z+16gamma)/5. The geometric alpha terms cancel exactly.
The first adverse shape block in the N16 comparison is

    S=64(gamma-1)-22(alpha-1)+57beta-55delta.

New exact PAPER decomposition, with w=e''' and
K(t,s)=(170/3)t^2*s-7s^3+16s^4/(3t):

    E*S + integral_0^t K(t,s)*w(s) ds = 64*(tE-Q)^2/(tQ) >=0.

The weight has the manifestly positive form
s*[54t^2+s^2+(8/(3t))*(t+2s)*(t-s)^2]. An explicit primitive is
K*r-K_s*p+K_ss*e-K_sss*E+(64/t)*Q; its derivative is K*w.
Its zero boundary vanishes and its t boundary is
55t^3*r-57t^2*p+22t*e-86E+64Q/t. This avoids Fubini and retains
all finite-displacement cancellation. N14's c''''<846c implies
w(s)<846E(s), and convex E with E(0)=0 gives E(s)<=sE(t)/t.
The positive weight then bounds integral K*w above by
(827*846/45)*t^4*E(t). Thus S>-(827*846/45)*t^4 throughout the
physical chamber. This controls one actual adverse block, not the
whole N16 sign. Every new identity and inequality awaits Lean audit.

2026-10-04: N18 scratch58774 exited0, standard3 on exact variance
identity, actual third-jet/primitive control and complete coupled-block
lower reserve. Saved ThetaCuspC5CoupledShapeQuadrature; final92615
exited0 with empty log. Umbrella wired once; no umbrella build.
N17 scratch45006/final26866 also exited0; all three endpoints standard3.
Source fourth-curvature helper visibility edit audited final39294 exit0.
Owned scratch files removed after successful leaf audits. N16 remains
open, including full comparison and endpoint recovery; RH not proved.

### N19: retain normalized curvature dynamics in the remaining N16 sign
Paper normalization (not yet a Lean theorem): put D=2alpha+beta,
L=3beta+delta, A=9+12Z+16gamma and
P=144Z^2+384Zgamma+96gamma^2+156Z+208gamma-9+5alpha+25beta.
Then Rbar=R*t^2/E^2=D*P/25-L*A/5 and J*=F*Rbar/(4t^4).
Writing dot=t*d/dt gives

    dot Z=Z(1+alpha), dot gamma=gamma(1+alpha-2gamma),
    dot alpha=alpha+beta-alpha^2,
    dot beta=(2-alpha)beta+delta,
    dot delta=(3-alpha)delta+epsilon, epsilon=t^4 e'''/E.

N16's actual remaining sign is therefore

    (15+3z+z^2)*[(A/5-4)*Rbar+dot Rbar]
      -[D/(1+alpha)]*(15+3z+6z^2+z^3)*Rbar >=0,
    z=k*y.

Do not infer it from the constant-curvature diagnostic. N18 controls
its coupled linear shape block; higher mixed terms remain.

Next exact source mechanisms, PAPER proofs/dependencies only:
1. e''>4e and0<=e'<2e give e*e''-(e')^2>0. Thus e'/e
   strictly increases. For alpha=t e/E, freeze t and differentiate
   (e(t)+t e'(t))*E(s)-e(t)*s*e(s); its derivative is
   t e'(t)e(s)-s e(t)e'(s)>0 for0<s<t. This proves dot alpha>0.
2. Freeze t again in (E(t)+t e(t))*Q(s)-2E(t)*s*E(s).
   Its derivative is2[t e(t)E(s)-s E(t)e(s)]>0 by alpha order,
   giving dot gamma>0. No corpus closure was returned by search42698
   (partial1216220, action-velocity identifications only).
3. Integrating e'<2e gives alpha<1+2t. Since e''>2e',
   delta>2t beta, hence dot beta>beta>0.
4. Crucially retain the affine defect relation exposed by N14's proof:
   c''''<4c''+162(c''-4c)=166c''-648c. Integrating across
   reflected displacement yields e'''<166e'-648E, or
   epsilon<166t^2 beta-648t^4. This stronger coupled relation
   is not yet a public Lean theorem. Replacing it by846t^4 discards
   the defect cancellation and obstructs a large-displacement argument.

Conjecture: these coupled dynamics can prove the full N16 polynomial
sign; monotonicity of Rbar is a subsidiary candidate, not an assumed
hypothesis. Keep the full source relation rather than optimizing numeric
constants or abandoning the finite-displacement problem.

N19 formalization now targets actual coupled source dynamics. Refine the
existing source fourth-jet theorem to expose its stronger affine defect
inequality C<166B-648c before using B<9c. Public scalar ceiling follows
as a corollary; its logical content is unchanged. Exact paper mechanism
for beta growth is particularly useful:

    t*beta'-beta = t^2/E^2 *
      [t*(r-2p)*E+p*((1+2t)*E-t e)] >0.

Here r>2p follows from r>4e and p<2e. The other factor
G=(1+2t)E-t e satisfies G'=2E+t(2e-p)>0 and G(0)=0.
This avoids discarding the finite source relation or introducing an
unproved elasticity premise. Alpha/gamma order and the affine reflected
third-jet inequality are also being formalized from the paper arguments
above. Full N16 still requires the mixed polynomial sign.

### N20: strict growth of the actual normalized inverse reserve
N19 scratch7656 exited0, all printed endpoints standard3. Saved leaf final
is in progress. New PAPER argument based on its exact polynomial and the
source/denominator bounds already certified in N14/N15/N18:

Set D=2a+b, L=3b+d, A=9+12Z+16g and P as in N19. Write
x=dot a>0, y=dot b>b>0, v=dot g>0. Then

    25 dot Rbar = (2P+5D)x + (P+25D-15A)y
      +[D(384Z+192g+208)-80L]v
      +[D(288Z+384g+156)-60L]Z(1+a)
      -5A*((3-a)d+epsilon).

Actual source gives a>=1, 1<=g<=a, b<=9t^2, d<=9a t^2,
Z>=18t^2, L<D(1+3Z/8), epsilon<846t^4 AND
 epsilon<166t^2 b-648t^4. Retain the affine bound for the
-60Z epsilon term and the fourth-power bound for the remaining epsilon
term. The key nonnegative coefficient decomposition is

    P+25D-15A+25-144Z^2
      =(384g-24)Z+96(g-1)^2+160(g-1)+55(a-1)+50b.

Dropping only nonnegative terms and paying the two epsilon parts separately
leaves the following sufficient lower expression (all symbols actual):

    [(531/2)D(1+a)-(1228/3)b-60a-(235/18)(9+16g)]Z^2
      +[D(384g+96)(1+a)-(a/2)(115+160g)-25/2]Z.

Both coefficients are strictly positive from a>=1, 1<=g<=a, b>=0:
for the first, use (531/2)b(1+a)>=(531)b and
531a(1+a)>=1062a; for the second, D(1+a)>=4a.
This would prove dot Rbar>0 throughout 0<t<=u without an unproved
shape premise. It is structural inverse-source growth, not a numerical
experiment. Full N16 still requires enough growth to dominate the clock,
plus endpoint recovery. No RH closure is claimed. Search52267 exited0,
partial generation1220656; only source-only/not_checked candidates and
unverified derivative ingredient sets were returned, no checked closure.

### N21: paper endpoint recovery mechanism, awaiting Lean
Search19484 terminal0, partial generation1220788, returned actual Green
kernel/inverse-source identities but no checked endpoint reconstruction.
The exact homogeneous pair of the N15 inverse operator is y=D1' and
H=t*y-D1, with W(y,H)=d*D1. For fixed outer t, the variation primitive

    Pi(t,s)=[Green(t,s)*F*'(s)
      +d(s)*(D1(t)-(t-s)*y(t))*F*(s)]/[d(s)*D1(s)]

has derivative 4*Green(t,s)*J*(s)/d(s)^2, and Pi(t,t)=F*(t).
At s->0+, E/s->c(u)>0, Q/s^2->c(u), y/s->2c(u), d->2c(u).
Consequently F*/s^5->c(u)^(8/5), s*h->5, Green(t,s)/s has a
finite limit, and Pi(t,s)->0. In detail F*/D1 equals
s^3*(Q/s^2)^(8/5)/(E/s)*exp(6Q/5), so the endpoint vanishes
without assuming regularity of an unspecified inverse solution. The source
J*=F*Rbar/(4s^4) is O(s), since the exact N19 polynomial has a finite
limit, and the positive Green integrand therefore extends continuously
by zero at s=0. FTC would then prove literal Green recovery of F*.
This is a complete paper mechanism, not yet a Lean endpoint theorem;
Q/s^2 and all fractional-power limiting identities require audit.
N16's actual clock-ratio sign remains the principal hard open problem.

### N22: actual local inverse-source/clock cancellation (paper audit needed)
Expanding the exact N19 normalized equations at t=0 with c=c(u),
b=c''(u)/c(u), v=c''''(u)/c(u), gives the following candidate Taylor
coefficients, to be independently checked in Lean before use:

    Rbar=24+(216c/5+24b/5)t^2
       +(288c^2/25+904cb/25-377v/225+542b^2/225)t^4+o(t^4).

For q=(2alpha+beta)/(1+alpha) and z=k*y, both
(A/5-4)+dot Rbar/Rbar and q*z*coth(z) have constant 1 and
quadratic coefficient 6c+2b/3. Their difference has proposed quartic
coefficient

    (2/675)*(891c^2-1017cb-122v+176b^2).

This is NOT the existing N14 coefficient with 1311c^2. It must be derived
from the actual normalized inverse profile, not identified by resemblance.
Its positivity follows algebraically from the actual c>18,b<9,v<846:

    891(c-18)^2+22923(c-18)+20718
       +1017c(9-b)+122(846-v)+176b^2 >0.

The symbolic coefficients and their analytic Taylor meaning remain
unaudited. This gives a concrete local attack on the true clock sign,
not a replacement for the global finite-displacement inequality.

N20 scratch53651 reached the proof and exited1 with one elementary
normalization error in E<=t e; its mixed-polynomial algebra and exact
inverse-reserve derivative bridge already printed standard3. The corrected
scratch54341 exited0; derivative bridge, complete source-flow positivity,
actual derivative positivity and strict monotonicity all printed exactly
[propext, Classical.choice, Quot.sound]. Saved
ThetaCuspC5InverseReserveGrowth; final leaf audit ongoing.

A further coupled relation available from N19's paper proof is
alpha*delta>beta^2, equivalent to e*e''>(e')^2. Thus
alpha*dot beta-beta*dot alpha>alpha*beta. This retains growth of the
shape ratio beta/alpha and can be used in the remaining full clock sign;
no separate public Lean theorem is asserted yet.

N21/N22 common regularization mechanism: define on all real s
Ebar(u,s)=integral_0^1 e(u,r*s) dr and
Qbar(u,s)=2*integral_0^1 (1-r)*e(u,r*s) dr.
FTC and change of variables give E=s Ebar and Q=s^2 Qbar,
with Ebar(u,0)=Qbar(u,0)=c(u)>0. Differentiation under these fixed
compact integrals preserves the full source and gives smooth extensions.
For s>0, F*=s^5*Qbar^(8/5)*exp(6*s^2*Qbar/5). All normalized
shape variables have regular formulas: alpha=e/Ebar,
gamma=Ebar/Qbar, beta=s*p/Ebar, delta=s^2*r/Ebar,
epsilon=s^3*w/Ebar. The normalized reserve polynomial therefore
extends smoothly with value24 at0, and J* extends as s times a smooth
factor. This single construction addresses actual endpoint recovery and
analytic identification of N22, without assuming an unspecified remainder
or treating the coefficient calculation as the analytic germ. PAPER only.

2026-10-04 N20 final67315 exited0, empty log. Leaf wired once into
RHTower; no umbrella build. N19 final20860 also exited0 and was wired
once. Strict normalized inverse-reserve growth is now CERTIFIED. N21
endpoint reconstruction and N22 actual analytic germ remain PAPER only.
Full N16 clock order, full C5 and all-degree/RH closure remain open.

2026-10-04 N21 continuation: revalidated N20 saved strict-growth theorem
and current TH map. Corpus search85606 was partial1220976; dslope query
returned no applicable smooth real quotient closure. Lexical parameter-
integral search97687 returned zero hits. Direct source inspection found
HTGeometry.SmoothAngularAverage.average_smooth and its compact derivative
argument; adapt that argument to the real unit interval.
Exact factorization proof avoids change of variables: in r,
(d/dr)E(u,r*t)=t*e(u,r*t), and
(d/dr)[Q(u,r*t)+2t(1-r)E(u,r*t)]=2t^2(1-r)e(u,r*t).
FTC on [0,1] yields E=t Ebar and Q=t^2 Qbar for every real t,
including t=0. Formalization now targets these smooth actual-source
factors, the positive profile factor, and then the full Green endpoint
recovery. Full N16 clock order remains open.

N21 regularization scratch72498 exited0; all11 printed endpoints standard3.
Saved ThetaCuspC5RegularizedAction with minimal N19 import and public
contDiff_unitIntervalParameterIntegral for the next clock-germ argument.
Final51037 is running. Smooth factors now identify F*=t^5*f,
Rbar=regularActionInverseReserve on t>0 with regular value24 at0,
and J*=t*intrinsicInverseSmoothFactor on t>=0, with factor value
6*c(u)^(8/5) at0. These are source identities, not endpoint premises.
The full reconstruction scratch /tmp/th_n21_green_recovery.lean is ready
for audit once the saved factor leaf finishes. Its claimed recovery is
for every real u and t>0; no same-half-line or clock-order premise is needed.

N21 complete recovery scratch27413 exited0. Primitive continuity, exact
inverse-source derivative, and full intrinsicActionProfile_green_recovery
all printed standard3. Saved ThetaCuspC5IntrinsicGreenRecovery; final leaf
audit running. Formula holds for every real u and positive t:

    F*(u,t)=4*integral_0^t [J*(u,s)/d(u,s)^2]*Green(u,t,s) ds.

No assumed endpoint limit, integrability, source order or same-half-line
condition remains. N21 is mathematically closed, pending final saved-leaf
audit; N16 full clock order and all-degree positivity remain open.

N22 next actual object: psi=t*Cbar, with
Cbar=k*(Ebar+e)*integral_0^1 cosh(r*k*y) dr>0, smooth on all real t.
Thus J*/psi equals the globally smooth ratio
intrinsicInverseSmoothFactor/Cbar on t>0. Its value at0 is
R0=3*c^(8/5)/(k*c). A scratch defining and identifying this actual ratio
is prepared; the fourth-jet claim remains unproved. If the earlier N22
logarithmic expansion is correct, the actual ratio has vanishing jets1,2,3
and fourth jet (4/225)*R0*(891c^2-1017c*b-122v+176b^2).
Do not count a smooth quotient or algebraic sign as an analytic jet proof.

2026-10-04 N21 final77853 exited0, empty log; recovery leaf wired once.
N21 is CERTIFIED. N22 actual quotient smoothness scratch15458 exited0,
all5 endpoints standard3, after fixing one `id` normalization in the clock
FTC proof. Saved ThetaCuspC5RegularizedClockRatio; final63823 running.
The actual quartic sign remains open, not implied by smoothness.
Search45419 (partial1221292) returned real/complex jet mechanisms, no
checked inverse-clock germ closure. Use source-verified iterated derivative
product and reflection laws. Next exact step: all-order endpoint jets of
Ebar and Qbar follow from E=t Ebar and Q=t^2 Qbar; no termwise series
or assumed Taylor remainder is required. This supplies the actual source
jets needed to prove or refute N22's891 coefficient.

N22 source-jet scratch8925 and final43559 exited0, all4 axiom reports
standard3; ThetaCuspC5RegularizedSourceJets saved and wired. First actual
four-jet assembly66306 failed only redundant simplification steps. Its
private product/power/quotient/exponential/hyperbolic rules all printed
standard3. Corrected86356 reached the actual local monotonicity proof;
remaining errors were unsimplified exp(0) and a beta-reduction before
rewriting the original quotient. Complete corrected audit73998 running.
The actual fourth coefficient, positivity, and local order are not counted
as certified until that audit exits0.

## N23 — intrinsic inverse source as clock supersolution (PAPER CONJECTURE)

Continue the full physical interval 0<t<=u, after N22's local test.
Existing N12 uses the clock's exact equation
psi''-(d'/d)psi'=k^2*d^2*psi. Conjecture the actual intrinsic inverse
source satisfies the opposite strict inequality:

    J*''-(d'/d)J*'-k^2*d^2*J* > 0.

This is stronger than N16 but removes the transcendental coth comparison.
The exact flux derivative is

    ((J*'*psi-J*psi')/d)' = (psi/d)*[J*''-(d'/d)J*'-k^2*d^2*J*].

Smooth first-order factors supply the zero initial flux. Positive actual
forcing would propagate the ratio order through the whole interval.
No supersolution sign is currently proved.

Retain the N19 variables, dot=t*d/dt, D=2alpha+beta,
M=3beta+delta, A=9+12Z+16gamma, P=A/5-4, R=Rbar,
kappa=k^2*t^2*d^2=9*Z^2*D^2/(2*c(u)*t^2). The proposed exact cleared
forcing, after factoring F*/(4*t^6), is

    [P^2-P+dot P-(M/D)*P-kappa]*R
       +[2P-1-M/D]*dot R+dot(dot R).

Here dot P=(12*dot Z+16*dot gamma)/5. The highest new source variable
zeta=t^5*e''''/E appears linearly with coefficient -A/5 in dot(dot R).
The already-certified affine source inequality would give
zeta<166*t^2*delta-648*t^4*alpha. Thus this route needs no new high-order
source sign premise: the remaining task is a complete correlated sign
proof of the displayed expression, including the actual center c(u).
Do not replace c(u), displacement, and shape variables by independent
free numbers. The source identities c''>4c, c'(0)=0 and c(0)>18 suggest
c(u)>18*cosh(2u), which would control the center-dependent clock rate on
t<=u; this relation is not claimed Lean-proved here. N23 requires its own
paper/Lean sign audit, not merely a wrapper around an assumed inequality.

2026-10-04 N22 CLOSED LOCALLY. Corrected scratch73998 exited0: actual
fourth-jet classification, strict fourth-jet positivity, and strict local
order of the original J*/psi all printed exactly standard3. Saved
ThetaCuspC5IntrinsicClockGerm. Final99561 caught a redundant tactic from
warning cleanup; reverted that single edit. Final4115 exited0, one harmless
unnecessary-sequence warning, no errors. Leaf wired once; no umbrella build.
All five leaves in this continuation are now saved, directly audited and
wired: RegularizedAction, IntrinsicGreenRecovery, RegularizedClockRatio,
RegularizedSourceJets, IntrinsicClockGerm (ThetaCuspC5 prefix).
The actual ratio has jets1=jets2=jets3=0 and fourth jet
(4/225)*R0*(891c^2-1017B-122C/c+176(B/c)^2)>0 for every center u>=0.
Successive strict derivative comparison yields actual ratio strictMonoOn
some (0,delta). This is an analytic local theorem, not a formal coefficient
or numerical experiment. N16 global order, N13/full C5 and all-degree/RH
remain open. Map updated and RN heading preserved.
N23 search1758 was non-partial1221472/1221473. Every candidate/source-argument/
idea/ingredient section inspected; hits were source_only/not_checked,
mostly irrelevant reciprocal algebra plus standard Wronskian identities.
No actual inverse supersolution sign was found. The above N23 conjecture
remains the concrete next global sign attack.

2026-10-04 N23 continuation: revalidated saved N22/map/N20 exact flow;
previous turn classified PROGRESS. No owned live job at start.
Paper attack on the COMPLETE N23 forcing: its linear part around
Z=0,alpha=gamma=1,beta=delta=epsilon=zeta=0 cancels its Z term. Five
times the remaining linear block is

    T=64(alpha-gamma)+92beta-108delta-155epsilon-25zeta.

The apparent order-two debt cancels on the actual source. Set
V=(tE-Q)^2/(tQ) and define the positive quintic weight

    H(t,s)=(1053/5)t^4-(170/3)t^2*s^2+16*s^5/(15t).

A direct four-fold integration identity gives the PAPER exact cancellation

    E*T +64V +25t^5*e''''(t) +integral_0^t H(t,s)e''''(s) ds = 0.

Indeed H'''=64s^2/t, H''''=128s/t, H'''''=128/t;
H'(0)=H'''(0)=0, and the primitive
H*w-H'*r+H''*p-H'''*e+H''''*E-(H'''''/2)*Q
has derivative H*e'''' and value0 at0. At t it equals
155t^4*w+108t^3*r-92t^2*p-64t*e+128E-64Q/t.
Thus the highest source derivative enters with one explicit positive
integral weight and one positive endpoint weight; the remaining variance
is retained with its exact adverse sign. The source affine fourth-jet
inequality can control both weights. This identity has not yet been
Lean-audited; the complete nonlinear forcing sign remains open. This is
an attack on its genuine cancellation, not an independent-variable sign
assumption or a numerical estimate.

N23 further PAPER sign discovery: after retaining the complete second
Euler flow, the epsilon=t^4*e'''/E coefficient of the full force is

    Ceps=Rb-2*Adot/5-(A/5)*(2*A/5-2-2alpha-M/D),
    Rb=(Ppoly+25D-15A)/25,
    Adot=12Z(1+alpha)+16gamma(1+alpha-2gamma).

Using the certified M<D(1+3Z/8), exact cancellation gives

    25*Ceps < -243Z^2/2-354Z*gamma-96gamma^2
               -3033Z/8-528gamma+145alpha+50beta-171.

This upper bound is strictly negative on the actual chamber:
gamma>=1, alpha<1+2t<=2+t^2, beta<=9t^2, Z>=18t^2.
Indeed the positive alpha/beta terms are at most290+595t^2;
the constant negative terms total-795 and the negative Z coefficient
more than pays595t^2. Thus the complete force decreases in BOTH new
high-jet coordinates: coefficient zeta is -A/5<0, and coefficient epsilon
is Ceps<0. Replacing each by its already-certified affine source upper
bound would produce a strict lower force depending only on the actual
curvature through order TWO. This coefficient identity/sign is PAPER,
not yet Lean-certified. It is the next full-force sign subproblem, not
a reason to stop at the fourth-order quadrature.

2026-10-04 N23 CERTIFIED HIGHER-SOURCE ELIMINATION. Quintic quadrature,
its strict positive kernel and complete affine-source reserve are saved in
ThetaCuspC5InverseForceQuadrature (final6045 exit0). The complete second
Euler flow, actual clock-operator identity, exact shape-kernel form and
strict epsilon-coefficient sign are saved in ThetaCuspC5InverseClockOperator
(final13593 exit0; scratch20823 standard3). Both leaves wired once.
The complete force S strictly exceeds intrinsicClockSecondSourceForce,
which substitutes eps=166t^2 beta-648t^4 and
zeta=166t^2 delta-648t^4 alpha simultaneously. All source derivatives
above order two are thereby eliminated without a sign premise. The actual
kappa=t^2*k(u)^2*d(u,t)^2 is retained. Its coupling with center/displacement
and the remaining second-source polynomial sign are the next hard problem.
No global inverse-clock order, full C5 or all-degree theorem is claimed.

N23 next PAPER attack: preserve the source-center coupling in the clock
mass rather than replace c(u) by an independent constant. The certified
positive defect b=c''-4c suggests the exact propagation formula
c(x)=c(0)cosh(2x)+(1/2) integral_0^x sinh(2(x-s))*b(s) ds,
since c'(0)=0. The associated flux c'cosh(2x)-2c sinh(2x)
has derivative b cosh(2x)>0. Hence c/cosh(2x) strictly increases,
and on 0<t<=u the actual clock mass obeys
k(u)^2*cosh(2t)<1/4. This is a structural center/displacement constraint
for the remaining full-force sign, not an independent shape assumption.
Neither propagation nor this clock constraint is yet audited here.
The same exact propagation should hold for the entire reflected source.
Set B(u,s)=(b(u+s)+b(u-s))/2=e''-4e. Then
 e=c(u)cosh(2t)+(1/2)integral sinh(2(t-s))*B(u,s),
 E=c(u)sinh(2t)/2+(1/4)integral (cosh(2(t-s))-1)*B(u,s),
 Q=c(u)(cosh(2t)-1)/2+(1/4)integral (sinh(2(t-s))-2(t-s))*B(u,s).
All integrals are over 0..t. These use one common positive source B,
retaining the moment correlations lost by bounding alpha/gamma/beta
independently. Exact primitives are H*e'-H'*e+E for the E kernel
and H*e'-H'*e+2(t-s)E+Q for the Q kernel. Positivity of the full
second-source force as a functional of this common B remains open.
Further structural reading of the source elimination: B=e''-4e obeys
B''<162B. Its even initial derivative vanishes. Writing M0=integral B,
the exact relations p=4E+M0 and r=4e+B(t) turn the two already-audited
higher-source replacements into e'''<16E+166M0 and e''''<16e+166B(t).
The zero-defect model is therefore preserved exactly by the lower force.
CAUTION: positivity of a free function B alone cannot settle the force:
its endpoint value could break the order-two moment cancellation. Retain
B''<162B or the certified quintic quadrature when handling that endpoint.
Next concrete sign attack: isolate the full force's linear shape block,
pay it by the quintic identity, and analyze its nonlinear remainder using
the common defect moments and actual center coupling. No independent
positive-B cone or endpoint sign is asserted sufficient.

2026-10-04 N23 COMMON SOURCE PROPAGATION CERTIFIED. Scratch26785 exit0:
all four reflected representations (e,p,E,Q), actual center representation,
and clock-mass/displacement constraint printed standard3. Saved
ThetaCuspC5CommonDefectPropagation; final89702 exit0, harmless unused-simp
warnings. Wired once. Exact representations hold for every real u,t;
common-source positivity and clock constraint use the physical chamber.
The proposed strict monotonicity of c/cosh was not needed or exported.
Three new N23 leaves are now saved/audited/wired; full remaining force
positivity, global inverse-clock order, full C5 and all-degree/RH remain
open. The next attack is the complete nonlinear remainder, retaining
common-defect moments, their differential constraint and quintic
cancellation; no assumed-sign wrapper is a closure.

N23 linearization clarification from the complete audited kernel: if kappa
is kept as an independent algebraic slot, its first-order expression is
432Z-24kappa+T/5, not T/5 alone. The Z term cancels only at the actual
leading mass kappa=18Z. A global decomposition must retain the exact debt
-(kappa-18Z)*Rbar. The quintic identity controls T, not this clock debt.
The new common-source/center identities address precisely the correlation
needed for that remaining term. Do not discard it or assert its global
sign from the local analytic germ.

2026-10-04 N24 PAPER clock-coordinate energy attack, based on the audited
N23 full operator and common source. Let Z=tE,y=Z',d=y',c=c(u).
The actual r<9e integrates to p<9E and e-c<9Q/2. Consequently
 d-2c<9(Z+Q)<=18Z<cZ,
so d<c(2+Z). This gives the positive energy reserve
 G=cZ(4+Z)-y^2, G'=2y[c(2+Z)-d]>0, G(0)=0.
Thus the actual clock coordinate z=k*y satisfies
 z^2<18Z+(9/2)Z^2 on the full physical interval.
This controls the integrated clock coordinate and avoids bounding its
second-order mass independently. Test it against the COMPLETE N16
first-order polynomial/rational-clock comparison, with the existing
source-shape quadrature retained. This is a new structural energy proof,
not a numerical optimization or a claim of global ratio order.
Also retain exact second-order debt: if L=d-2c,H=E/t-c, then
 kappa-18Z=18t^2(L-H)+(9/(2c))*t^2*L^2.
Its kernel L-H=integral_0^t[(5/2)t-s-s^2/(2t)]r(s)ds is positive.
The higher-source elimination remains available if the first-order
comparison does not close. Neither global comparison is yet proved.
N24 scratch58236 CERTIFIED the source-coordinate acceleration inequality,
positive energy and universal clock-coordinate energy cone (standard3).
Stronger PAPER form retains actual rho=c''(u-t)/c(u-t). Global projective
monotonicity gives r(u,s)<rho*e(u,s) for 0<=s<=t. Integrating on this same
fixed interval gives d<2c+rho(Z+Q)<=2c+2rho Z and hence
 y^2<4cZ+2rho Z^2,
 z^2<18Z+(9rho/c)Z^2.
This retains the actual source ratio and center, rather than replacing
rho by9 and c by18. It also preserves the exact leading clock correction
as t tends to zero. Formalizing this source-linked version before using
it in the full first-order comparison; no global ratio sign claimed.

N25 NEW PAPER profile conjecture from the actual Bose budget. The exact
saturated budget profile is
 Fsat=t^(9/5)*(2sinh(Q/2))^(8/5)*exp(6Q/5).
Our current F* replaces 2sinh(Q/2) by Q. Its unused factor starts
1+Q^2/15. Thus propose Fplus=F*(1+Q^2/15). The budget reduces exactly to
 (15+4x^2)*x*cosh x-(15+9x^2)*sinh x>=0, x=Q/2.
This has a positive derivative-chain proof on paper; no numerical check.
The inverse Green operator is linear. For the second component F*Q^2,
the logarithmic shape coefficient changes from m=16 to m=36. In general
 A_m=9+12Z+m gamma,
 R_m=D*[144Z^2+24mZgamma+m(m-10)gamma^2+156Z+13m gamma-9+5alpha+25beta]/25
       -M*A_m/5.
Thus the corrected inverse source is F*/(4t^4)*(R_16+Q^2*R_36/15).
At the endpoint R_36=112, so its fourth ratio jet adds
(4/225)*R0*(420c^2), exactly changing the known coefficient891 to1311.
This links the previous two source orientations and offers more comparison
reserve without dropping the full Bose condition. Budget, inverse identity,
and this analytic-germ identification are PAPER until separately audited.
The full corrected inverse-source/clock sign remains the actual target.

2026-10-04 N24 CLOCK ENERGY CERTIFIED. Corrected scratch84104 exit0,
all five audited endpoints standard3. Saved ThetaCuspC5ClockCoordinateEnergy;
final32095 exit0, empty log, wired once. The actual interval-projective
energy bound is now unconditional on 0<t<=u. It does not prove global
inverse-clock order. The exact positive mass debt scratch71001 also
passed with all five endpoints standard3; saved leaf audit pending.

N25 budget paper proof sharpened: for
H(x)=(15+4x^2)*x*cosh(x)-(15+9x^2)*sinh(x),
H'(x)=3x*(x*cosh(x)-sinh(x))+4x^3*sinh(x)>0 because
(x*cosh(x)-sinh(x))'=x*sinh(x)>0. Both start at zero. Thus the
enriched profile has STRICT positive Bose budget for every real center
and positive displacement. The Lean scratch is prepared; not yet run.
Deep corpus search43698 non-partial1222460: all result groups inspected;
existing original inverse positivity/operator identity retrieved, no
corrected-profile closure or global current-sign producer.

N24 mass-debt final65664 exit0/empty log; saved and wired once. N25 Bose
scratch55418 failed only on Pi function application normalization;
corrected96954 exit0, both endpoints standard3. Saved
ThetaCuspC5EnrichedActionProfile; final74786 exit0/empty log, wired once.
The strict budget is now certified. PAPER inverse formula is
Jplus=F*/(4t^4)*[R16*(1+Q^2/15)+Q^2*I/15],
I=(4gamma/5)*[D*(24Z+42gamma+13)-5M]. The actual denominator budget
M<D*(1+3Z/8) makes I strictly positive. Hence Jplus strictly exceeds
(1+Q^2/15)*Joriginal on the full physical chamber. Scratch prepared to
audit this identity and inequality; they do not yet establish clock order.

N25 hard-sign analysis: with C=t*d/y*(z*coth z), the complete corrected
current is current16+(Q^2/15)*current36, where
current_m=(A_m/5-4-C)*R_m+dot(R_m). For the generic R_m, the exact
coefficient of delta in this current simplifies to
[A_m*(C-4)+10D]/5; the epsilon coefficient is -A_m/5. This cancellation
is PAPER, not a certified sign. The rational clock reserve equals
z^4/[3*(15+3z+z^2)] beyond 1+z^2/3. Global control must retain this
reserve, the source-shape quadrature and the source-linked clock energy.
The new profile alone does not eliminate the unresolved global comparison.

N26 PAPER structural source domination, motivated by the remaining
center/displacement debt. Corpus PrimitiveTransport already proves
b/G strictly increases, for b=c''-4c and
G=216*(q+3/2)^2/q^4, q=theta likelihood coordinate. The literal completed
source split gives, with S=q+3/2 and likelihood cumulants K_j,
 b/G=1+(q/S)^4*[-(2/27)S^6*K4+(4/9)S^5*K3-(4/9)S^4*K2].
Every bracketed scaled cumulant tends to zero by the corpus spectral-gap
theorems. Thus b/G tends to1, and its existing strict monotonicity forces
0<b<G globally. This is an exact first-atom domination of the complete
curvature defect, not a free-source or decay assumption. It supplies a
source-specific envelope for the common reflected B and should retain
the center dependence lost by the constant bound B<=b(0). The limit,
identity and global domination still require Lean audits. Full comparison
positivity remains the hard target; this source domination alone is not it.
The envelope also has exact primitive T=54*(q+1)/q^3 with T'=-G.
Consequently the complete reflected excess slope obeys
 p-4E < [T(u-t)-T(u+t)]/2,
while r-4e < [G(u-t)+G(u+t)]/2. Both retain the same actual endpoints.
Together with the common-source representations, these replace a free B
by its source-specific model and supply a concrete next sign attack on
the full corrected current. N26 scratch28389 certified the cumulant
identity but failed on inverse-quotient simplification and the direction
of the limit-order lemma. Corrected audit56184 is running. No mathematical
counterexample or global-current sign has been obtained.
N26 further PAPER consequence forced by the same corpus identities:
write F=-G'>0, H=-b'>=0 and f=F'/F<0. Existing slope comparison plus
b<G gives H<F. Positive defect Sturm flux gives H'>fH>fF=F'.
Therefore G-b is positive, decreasing and strictly convex on the physical
source half-line. In particular H-F strictly increases and
 w<4p+[F(u-t)-F(u+t)]/2.
This retains the endpoint difference of the literal source factor instead
of replacing w by a constant multiple of a primitive. It targets the
adverse epsilon term in the complete first-order current. These derivative
consequences are being added to the same scratch audit, not assumed.
For the complete current the proposed next substitution is
 epsilon < 4t^2*beta + t^4*[F(u-t)-F(u+t)]/(2E).
For the already-audited original second-order force the companion bound
is zeta < 4t^2*delta-t^5*[F'(u+t)+F'(u-t)]/(2E).
These preserve the exact model source at both endpoints and leave actual
clock mass intact. No new assumed-sign bridge is needed; the remaining
task is positivity of the resulting COMPLETE expression. A useful proof
decomposition should separate the exact cosh source from its common
defect integrals, then use the newly exposed positive decreasing convex
model correction. Proving only another local germ or a coefficient
improvement would not close that global obligation.

2026-10-04 N25 INVERSE CERTIFIED. Scratch23434 and saved final24984 exit0;
all four endpoints standard3, final log empty. The enriched literal inverse
formula, strictly positive increment and strict comparison with the scaled
original inverse are saved and wired in ThetaCuspC5EnrichedActionInverse.

N26 scratch87592 exit0: all ten audited endpoints standard3. Exact
normalized defect identity/limit1, global b<G, common-source endpoint
domination, exact T primitive and excess-slope bound, H<F, H'>F', complete
sourceDefectRatio>0, reflected w model difference and pointwise fourth
curvature model derivative bound are CERTIFIED. Saved leaf final audit
pending. Earlier56184 failed on pointwise function quotient normalization;
15753 certified all but the third-source difference (Pi subtraction
rewrite);87592 repaired that and verified both additional source signs.
These were elaboration repairs; no failed mathematical conjecture is
claimed. Full current positivity and all-degree/RH remain open.
N26 saved ThetaCuspCurvatureDefectModelDomination; final84673 exit0,
empty log. Wired once. All five new N24-N26 leaves are saved/audited/wired;
owned total44. Scratch/staging removed only after successful final audits.
No umbrella build. This continuation is PROGRESS in actual source/clock
control, not a solution of the full global current, C5 or all-degree/RH.
Next conjecture stays on the complete corrected current with the newly
certified endpoint model difference replacing its adverse epsilon term.
Final lint77347 exit1:16 unrelated unreachable modules, no new TH leaf
among errors and no forbidden proof declaration reported. Exact imports
verified once; RN heading preserved. No owned live jobs or scratch files.

2026-10-04 N27 complete-current attack. Revalidated actual saved N25/N26
source and current map. Deep search2916 non-partial1222982, all result
groups inspected; own enriched profile and source model facts retrieved,
no complete current sign producer. Next mathematical conjecture remains
current16+(Q^2/15)*current36>0 on0<t<=u. Formalize the exact current and
its highest-source affine dependence, then insert the N26 endpoint
difference without dropping the clock term. A potential full-sign proof
subtracts the existing source-shape quadrature block, leaving a nonlinear
remainder and the retained rational coth reserve. Neither positivity of
that remainder nor global clock order is yet proved.

N27 scratch92400 CERTIFIED all four endpoints standard3: generic normalized
inverse reserve Euler flow; exact delta/epsilon dependence of the COMPLETE
first-order current; derivative of actual enriched inverse/clock ratio;
strict actual endpoint-model comparison. The exact derivative is
 (Jplus/psi)'=F0/(4t^5*psi)*Kplus,
Kplus=K16+(Q^2/15)*K36, with actual C=t*psi'/psi retained.
The difference from Kmodel equals
 [(A16+(Q^2/15)*A36)/5]*(epsilonModel-epsilon)>0.
The source-model correction is therefore explicitly retained as a positive
term, not merely discarded. Positivity of Kmodel itself is NOT established
and must not be assumed: replacing a source derivative by its first-atom
model loses a positive source gap, including at the modular seam. The
previous affine actual-source cap remains available jointly with this
new cap. The hard target is Kplus, not a requirement that one particular
coarser lower expression be positive everywhere. Saved leaf audit pending.

N27 next PAPER decomposition attacks the full sign rather than another
local expansion. Put h=Q^2/15, Abar=A16+h*A36, Hbar=1+h, and
Bshape=64(gamma-1)-22(alpha-1)+57beta-55delta-25epsilon.
Subtract (Abar/125)*Bshape from Kplus. ALL epsilon dependence cancels;
the remaining delta coefficient is exactly
 Abar*(5C-9)/25+2D*Hbar.
Thus this remaining delta contribution can be adverse only when C<9/5.
The existing coupledShapeBlock_variance_identity identifies Bshape as
 [64(Z-Q)^2/(tQ)-integral K*w-25t^4*w(t)]/E,
with K positive. The complete expression retains positive variance,
actual clock elasticity and a single positive-weight source integral.
The proposed hard proof is positivity after combining that integral with
the nonlinear remainder, using actual source orientation and N26 source
gap; no sign of either piece separately is assumed.

The lost model source term also has the exact PAPER representation
epsilonModel-epsilon=t^4/(2E)*integral_(u-t)^(u+t)(H'-F'),
H'-F'=defectSturmFlux/F+(-f)*(F-H)>0, f=F'/F<0.
This explains why the complete source correction must be kept when a
bare model lower expression cannot yet be proved positive. These new
integral/decomposition formulas have not yet been separately audited.

N27 saved final54168 exit0/empty log; import verified once. Lint22246
exit1:14 unrelated unreachable modules, no new TH module or forbidden
proof declaration among diagnostics. Log /tmp/th-n27-enriched-current-lint.log.

N28 hard-sign attack, same full current conjecture. The peeling proposed
above is algebraically exact on paper. Use its actual Peano identity and
retain the model-source gap as a positive integral, so the unknown sign
is one combined nonlinear remainder, not independently relaxed jets.
The source gap density H'-F' is positive by the saved N26 Sturm flux;
its primitive gives the exact endpoint correction. No claim yet that
this correction dominates a negative model remainder. Investigate the
complete combined expression with actual clock elasticity throughout.

N28 exact positive-source kernel PAPER (audit running):
L(t,s)=25t^4+(85/3)t^2(t^2-s^2)-(7/4)(t^4-s^4)
       +16/(15t)(t^5-s^5), L_s=-coupledShapeKernel, L(t,t)=25t^4.
For rho=H'-fF>0 and rho_even=(rho(u+s)+rho(u-s))/2,
the complete loss of replacing w by w_model is integral_0^t L*rho_even.
L>0 on the physical interval by a positive (t-s),(t+s) decomposition.
Thus E*Kplus=E*Remainder+weight*(variance-modelQuadrature+integral L*rho_even).
No sign of the whole right side is yet proved.

N29 stronger PAPER conjecture: the remaining delta coefficient after
Peano peeling is strictly positive EVERYWHERE, not only when C>=9/5.
A lower clock envelope follows by differentiating
 (3+z^2)z*cosh(z)-(3+2z^2)sinh(z): derivative
 z*(z*cosh(z)-sinh(z))+z^3*sinh(z)>0.
Thus z*coth(z)>(3+2z^2)/(3+z^2). Actual z^2>=18Z follows from
 y^2-4cZ=(E-te)^2+4tE(e-c)>=0, so
 C>D/(1+a)*(1+12Z)/(1+6Z).
Set h=Q^2/15, Abar=(1+h)(9+12Z)+g(16+36h).
The coefficient is [Abar*(5C-9)+50D*(1+h)]/25.
Use D>=2a, a>=g>=1 and 15g*h<=Z^2. After multiplying positive
(1+a)(1+6Z), its lower numerator is
 (1+h)*Nbase+20g*h*R,
R=a-9+(66a-54)Z,
Nbase=N0+N1*Z+N2*Z^2,
N0=100(a-g)^2+(216g+109)(a-g)+(g-1)(116g+81)>=0,
N1=1404+3462(a-1)+192(g-1)+600(a-1)^2+1056(a-1)(g-1)>0,
N2=144+792(a-1).
Since R>=-9, the last term is >=-180gh>=-12Z^2;
Nbase-12Z^2>0. This proves the algebraic conjecture on paper and would
remove the final third-source sign ambiguity from the COMPLETE current.
Still no sign of the source integral plus nonlinear/clock remainder.
N28 SAVED AUDIT32018 exit0, empty log. Exact complete-current Peano
identity, positive gap density, backward Peano kernel and its strict
positive integral now formalized in ThetaCuspC5CurrentSourceQuadrature.
Wired once; owned total46. Scratch62150 already audited core endpoints
with standard3; final assembly axiom check follows via N29 scratch import.
The new exact identity still does not settle the full current sign.
N29 SAVED AUDIT49792 exit0; one harmless unnecessarySeqFocus style warning
at174, no errors. Saved ThetaCuspC5CurrentSourceOrientation and wired once;
owned total47. The exact global positivity of the remaining delta
coefficient is proved on0<t<=u, with actual clock and enrichment retained.
The Peano remainder equals its lower-jet part plus this coefficient*delta,
and this entire contribution is strictly positive. This is a solved
source sign ambiguity; the full current sign remains UNSOLVED.
N30 next hard target is the single combined expression
 E*LowerJetRemainder+E*DeltaCoefficient*delta
 +Weight*(variance-modelQuadrature+integral L*rho_even)>0.
All three displayed positive contributions remain available. Neither
LowerJetRemainder nor variance-modelQuadrature is assumed positive.
The actual clock must stay: its lower envelope was used ONLY for the
third-source coefficient, not as an upper bound on the full adverse clock.
Do not drift back to another local germ or a sign-premise wrapper.
Final import axiom audit64378 exit0: all seven N27-N29 endpoints depend
only on propext, Classical.choice, Quot.sound. Final lint19747 exit1:
14 unrelated unreachable modules; no new TH leaf or forbidden declaration.
All three new imports verified once. All owned scratch/staging removed;
logs/search JSON retained. No owned live jobs. Goal remains active.

2026-10-04 N30 continuation. Revalidated saved N28/N29 and current TH map.
Previous turn PROGRESS: full-chamber third-source contribution positive,
not complete current closure. Current target remains exactly
 E*LowerJetRemainder+E*DeltaCoefficient*delta+
 W*(variance-modelQuadrature+integral L*rho_even)>0.
The actual clock is adverse in the complete current but favorable in
DeltaCoefficient; independent use of its lower bound in the whole
current is invalid. Seek a bound/decomposition of the whole expression
preserving both effects. No new sign assertion or local-germ detour.
N30 PAPER Schur coupling from actual reflected source. The saved source
relations r>4e and0<p<2e imply e*r-p^2>0, hence a*delta>b^2.
Since the COMPLETE enriched Peano delta coefficient is positive, extract
DeltaCoefficient*(delta-b^2/a)>0 and retain b^2/a in the polynomial.
For each action power m, the exact remaining polynomial in b has form
 Remainder_m(b,delta)=Remainder_m(0,0)+b*Linear_m+b^2*Quadratic_m
   +(2/a)*b^3+[A_m*(5C-9)/25+2(2a+b)]*(delta-b^2/a),
Quadratic_m=A_m/5+31/5-2a-C+A_m*(5C-9)/(25a).
The source cone9(a-1)^2<=2Z follows from a<1+2t and18t^2<=Z.
Together with g>=1, m>=16 and the saved LOWER clock envelope, this forces
Quadratic_m>0. The lower envelope is used only on this favorable scalar
coefficient; the full remaining affine-in-b expression retains actual C.
This would expose every nonlinear beta/delta term as a positive term,
leaving affine slope plus the same coupled source quadrature/clock problem.
Not yet Lean-audited. Whole-current positivity remains the conjecture.
N30 important scope correction during paper audit: "affine in b" means
at fixed C. Actual C=lambda*(2a+b), lambda=kE*coth(k*y), and lambda is
independent of p when E,e are held. Substitution therefore leaves a
quadratic clock interaction in the affine part. The extracted positive
Schur reserve is valid, but it does NOT establish positivity of all
physical nonlinear slope terms. Keep this distinction explicit.
If P0=P_m at b=0, the affine part has exact C coefficient
 -[2aP0/25+b*(P0/25+2a-3A_m/5)]. The remaining clock term is
 -lambda*(2a+b)*[2aP0/25+b*(P0/25+2a-3A_m/5)].
This must stay coupled to the constant/linear source terms and Peano
integral. Source coefficient positivity alone is not a full-current proof.
N30 SAVED AUDIT37266 exit0, empty log. Formalized actual reflected
curvature determinant, strict a*delta>b² coupling, global quadratic
coefficient positivity, positive Schur reserve and exact COMPLETE current
decomposition in ThetaCuspC5CurrentSchurCoupling. Wired once; owned total48.
This is a new positive coupled-source contribution, not full current
closure. Final imported axiom and lint checks follow. Actual clock still
couples to slope in the residual expression as explained above.
N31 next PAPER attack stays on the whole current: insert the certified
rational UPPER clock envelope in the COMPLETE current, before separating
source terms. Write z=k*y, D=2a+b,
 Cenv=D/(1+a)*(15+3z+6z²+z³)/(15+3z+z²).
The complete current is affine decreasing in C with positive coefficient
R16+(Q²/15)R36, so actual K>Kenv. The N29/N30 positive coefficient
certificates remain valid at Cenv because Cenv>Cactual satisfies their
lower-clock premises. Conjecture Kenv>=0 for the actual physical source.
Attack that sign itself, with the common source quadrature and positive
Schur reserve retained. Do not count merely exporting the envelope
comparison as closing the hard obligation. Do not replace the actual
center/projective source correlations by independent extrema.
N30 final imported axiom14794 exit0: all six endpoints use only
propext, Classical.choice, Quot.sound. Final lint75676 exit1:17 unrelated
unreachable modules; no new TH leaf or forbidden proof declaration.
Import once, RN preserved. All owned scratch/staging removed; logs kept.
No owned live jobs. Assessment PROGRESS: new actual Schur correlation and
strict reserve proved, full coupled sign and arbitrary-degree/RH open.

2026-10-04 N31 continuation: attack the SIGN of the complete rational
upper-clock-envelope current. Previous Schur reserve is genuine progress
but does not discharge the clock debt. Preserve actual source coordinates
and common clock when testing a whole-expression positive decomposition.
Search running at /tmp/th-n31-complete-sign-search.json. No numerical
experiments or claim that a comparison-only theorem closes the frontier.
N31 PAPER complete-current closure on the unbounded chamber2<=t<=u.
Use c(u)>18cosh(2t) and p<2e, a<1+2t, preserving actual center.
The hyperbolic fourth-order lower polynomial implies
 k*(1+t)*(1+2t)<t, hence k*t*d<2Z.
The rational envelope L(z)<z+3 then gives
 Cenv<2Z+6(1+t)<1+12Z/5<=A16/5-4.
R16 and Flow16 are already strictly positive. For m36, R36>R16;
the increment flow is positive globally: differentiating
 I=(4g/5)[D(24Z+42g+13)-5M]
leaves only -5(3-a)delta-5epsilon adverse. Bounds
 delta<=aZ/2 and epsilon<=83Z*beta/9 are paid by
 24D*Z*(1+a), using a>=1. Thus Flow36>Flow16.
Both COMPLETE currents at Cenv are positive for2<=t<=u, not merely
one source coefficient. Remaining sign domain0<t<2 retains all centers.
This is an unbounded-domain closure, not a search for an optimal cutoff.
Formal audit not yet run. Full N31 conjecture remains open.
N31 SAVED AUDIT93552 exit0, empty log. The complete rational-upper-clock
current and actual enriched current are now positive on2<=t<=u in
ThetaCuspC5OuterClockCurrent. Its enrichment flow inequality is global
on0<t<=u. Wired once; owned total49. Scratch48404 already exit0;
final imported axiom audit now running. Lint35761 exit1:12 unrelated
unreachable modules; no new TH leaf or forbidden proof declaration.
N31 is PARTIAL DOMAIN CLOSURE: entire unbounded region solved, bounded
displacement region0<t<2 and arbitrary-degree/RH still open. No numerical
experiments, cutoff optimization, umbrella build, or heartbeat increase.

N32 next full-sign attack: preserve the simultaneous source moments in
the remaining chamber, instead of relaxing alpha, beta, delta independently.
For w=e''', exact integration by parts suggests
 E*(delta-beta)=t^2*integral_0^t s*w(s),
 E*(beta-3*(alpha-1))=integral_0^t s*(t^2-s^2)*w(s)/2.
These are signed moment identities, NOT inequalities: w has no assumed
sign. Inserting delta=beta+its moment into the COMPLETE Peano current
changes its integral kernel to W*coupledShapeKernel-DeltaCoefficient*t^2*s;
the endpoint term and actual clock remain. Study the sign of the whole
new expression, including the kernel's possible change of sign. Do not
export these identities alone as a closure or add a source-sign premise.
The N30 Schur reserve remains available wherever this reorganization
does not give a usable sign. Full N31 positivity remains the conjecture.
N31 final imported axiom78566 exit0: global enrichment flow, full upper
current and full actual outer-current endpoints use only propext,
Classical.choice, Quot.sound. Final module has no warnings. All owned
scratch files removed, audit/search logs retained; no owned live jobs.
N32 search47277 returned relevant coupled-source APIs with partial
retrieval/model stages; all result groups inspected. No inner sign or
the proposed two moment identities retrieved. Exact source definitions
and derivative bridges checked in the existing quadrature leaf.

2026-10-04 N32 continuation. Previous turn PROGRESS revalidated: full
outer sign audited, inner0<t<2 and all-degree/RH still open. Current
attack retains the two signed source moments in the complete current.
Paper kernel audit: after transferring a fraction lambda of delta to
beta, the source-gap backward kernel is
 W*Lgap(t,s)-lambda*Delta*t^2*(t^2-s^2)/2.
Its positivity cannot be assumed independently of the actual clock.
Seek its exact admissible transfer and keep the untransferred Schur
reserve. This is part of the full inner sign attack, not a declaration
that a new decomposition alone proves the current positive.
N32 PAPER exact admissible source transfer. Write eta=lambda*Delta.
The backward kernel is nonnegative on[0,t] EXACTLY when
 eta<=1053*W/10 (W>0). Necessity is its value at s=0. At equality,
 Lgap-1053*t^2*(t^2-s^2)/20=
 s^2*(1459*t^2+41*s^2)/60+16*s^4*(t-s)/(15*t),
strictly positive for0<s<=t. This is a source-moment boundary, not a
numerically optimized cutoff. Choose actual eta=min(Delta,1053*W/10).
Then eta>0,Delta-eta>=0; retain (Delta-eta)*(delta-beta^2/alpha).
The complete model remainder becomes
 E*LowerJet+E*eta*beta+E*(Delta-eta)*beta^2/alpha+W*variance
 -[integral (W*Kpeano-eta*t^2*s)*w_model+25*W*t^4*w_model(t)].
It has no actual delta/epsilon. The exact difference from E*K is the
nonnegative retained Schur gap plus the STRICTLY POSITIVE source-gap
integral with the admissible backward kernel. All clocks are actual and
common. Prove and audit this elimination, then attack the sign of this
single first-source/model expression. That last sign remains conjectural.
N32 PAPER strict improvement over untransferred Schur/model substitution.
Let Rbase=E*LowerJet+E*Delta*beta^2/alpha+W*variance-W*modelQuadrature.
Then Rnew-Rbase=eta*[E*(delta-beta^2/alpha)+
 t^2*integral_0^t s*reflectedSourceModelGap(s)]>0.
Both terms are actual source contributions already sign-controlled;
eta>0. This proves the transfer loses strictly less than that previous
Schur/model lower expression, while eliminating actual delta/epsilon.
It does not assert dominance over every other available comparison or
positivity of Rnew itself. Lean audit of the complete identity is running.

N32 SAVED AUDIT90498 exit0, empty log. Exact admission, complete-current
identity, retained source-gap positivity and strict Rbase<Rnew<E*K saved
in ThetaCuspC5CurrentMomentTransfer; wired once, owned total50. Imported
axiom audit89065 running. Lint7470 exit1:24 unrelated unreachable
modules, all error lines inspected; no new owned TH leaf or forbidden
proof declaration. Rnew positivity remains the hard sign obligation.

N33 next attack is the SIGN of this complete first-source remainder,
not another elimination wrapper. Keep the actual clock z=k*y and
the saved source-linked energy z²<18Z+(9*rho_left/c(u))*Z², together
with the actual model source at the same endpoints. The rational
clock envelope retains the fourth-order cancellation; its quadratic
truncation cannot be used globally. Do not transplant the ACTUAL
fourth-source inequality c''''<166c''-648c to the model source:
that implication has not been proved. The model derivative involves
F', and its available direct bound uses G, whereas actual affine
control uses b=c''-4c<G. This distinction must be resolved in the
full comparison before claiming any positive remainder.

N33 PAPER replacement mechanism, targeting the full sign rather than
transplanting the actual fourth-source bound to the model. With the same
admitted eta, K=WKpeano-eta*t²*s and L=WLgap-eta*t²(t²-s²)/2,
L'=-K, L(t)=25Wt⁴ and w(0)=0. Thus the COMPLETE actual quadrature is
 Qeta_actual=integral_0^t L*w',
and the actual affine source inequality gives
 Qeta_actual < integral_0^t L*(166*r-648*e).
This uses L>=0 (strict inside), not a sign for K or w. The gap is the
positive integral of L*(166*r-648*e-w'). All terms are the actual source.
Two further integrations by parts eliminate r from the upper quadrature:
 Qeta_affine=166*[25Wt⁴*p(t)+(55W-eta)t³*e(t)]
   -integral_0^t [648L-166L'']*e(s),
 L''=(eta-170W/3)t²+21W*s²-64W*s³/(3t).
This gives a complete lower expression with curvature only through its
first derivative, keeping the same clock and positive Schur contribution.
The final even-curvature integral may have a signed kernel and MUST be
retained until its full contribution is paid. The current choice of eta
does not by itself imply 648L-166L''>=0. These N33 identities and the
whole resulting sign are PAPER only; audit applicability and then attack
the complete expression. No new module for them has yet been written.
N32 final imported axiom89065 exit0: all seven audited endpoints use
only propext, Classical.choice, Quot.sound. Saved module warning-free.

2026-10-04 N33 continuation: previous turn PROGRESS revalidated against
saved N32 source. Formalize actual fourth-source gap through the
admitted backward kernel, then preserve the complete even-source
integral while attacking its sign. Do not infer a sign from successful
elimination alone. The actual source-affine slack is strictly positive;
the final even-source kernel can change sign at the admitted eta.

N34 PAPER new source comparison exposed by the N33 sign attack.
Let B=c''-4c, G=sourceDefectPrimitive, beta=B/G, q=actual coordinate,
F=-G', and h(q)=16+120/q+180/q². The MODEL fourth-source envelope
minus the ACTUAL-AFFINE envelope equals G*chi, with chi=h(q)-162beta.
The saved beta strictly increases to1, while h(q) strictly decreases
to16. Therefore chi strictly decreases to-146. At the physical center,
the exact modular source jets give c(0)<20; source_projective_upper
gives B(0)<100; q(0)<2 gives G(0)>160 and h(q(0))>121. Hence
chi(0)>0. Continuity then gives a UNIQUE positive source crossing.
The affine envelope is smaller before that crossing and the model
envelope is smaller after it. This is a source-defined change of order,
not a numerical cutoff search. Use their minimum in the positive
backward-kernel quadrature to retain both improvements. The full
resulting current sign still requires proof. Scratch crossing proof
prepared, not run yet; no theorem is claimed before audit.

N35 PAPER full-sign target exposed by the unique crossing: pointwise
best fourth-source envelope equals Affine-G*max(0,-chi). Therefore set
 Rbest=Raff+(1/2)*integral_0^t L(s)*[G(u+s)*max(0,-chi(u+s))
                       +G(u-s)*max(0,-chi(u-s))] ds.
Both correction terms are nonnegative. The same complete-current
identity has the strictly positive combined-source gap plus its
nonnegative Schur term; Rbest>=0 would close the inner current.
Also Rbest-Rmodel is the positive-part integral with max(0,chi) instead.
Thus this retains the stronger affine source near the center AND the
stronger explicit model source in the tail, at actual source locations.
Do not discard the common clock or replace chi by a freely chosen
cutoff. All statements in this N35 paragraph remain PAPER, including
the full sign; N33/N34 combined scratch is still being audited.

N33/N34 SAVED FINAL18156 exit0, empty log. Exact actual fourth-source
quadrature, positive affine slack, complete affine-current lower
comparison, interior even-curvature identity, unique source-envelope
crossing, best pointwise source bound and exact affine tail correction
are Lean-certified in ThetaCuspC5CurrentAffineEnvelope. Wired once,
owned total51. Imported axiom audit now running. Lint50718 exit1:
16 unrelated unreachable modules, all errors inspected; none owned
new TH leaf or forbidden proof declaration. This closes the source
envelope order classification, not the complete inner sign or RH.
N35 combined-current identity and nonnegativity are still PAPER targets.

N33/N34 final imported axiom10414 exit0: all ten audited endpoints
use only propext, Classical.choice, Quot.sound. Saved leaf warning-free.
N35 STRONGER PAPER consequence from the exact source slope comparison:
retain h(q)=16+120/q+180/q²=-f(q)*(4+12/q). Positive Sturm flux
and H<(4+12/q)B give c4<4*c2+h(q)*B, with B=c2-4c. This smooth,
source-correlated envelope is STRICTLY below BOTH previous envelopes
everywhere: Affine-Correlated=(162-h)B>0, and
Model-Correlated=h*(G-B)>0. Thus it also strictly improves their minimum.
The exact slack is flux/F+h*sourcePrimitiveReserve, both terms strictly
positive. This preserves the local source-coordinate correlation lost
in the constant affine coefficient and in replacing B by G. It is not
a numerical optimization. The min-envelope N35 current mechanism above
is valid but is now superseded as the strongest NEXT SIGN TARGET by
this correlated envelope; neither full sign has yet been proved.
Search76041 running; direct paper proof prepared for Lean audit.

N35 scratch49181 exit1 only on a misplaced unfold; corrected, then
complete scratch5621 exit0, empty log. Actual fourth-source correlation
strictly improves BOTH affine and model envelopes, with exact slack
flux/F+h*sourcePrimitiveReserve. Full current identity retains its Schur
reserve and correlated-source gap integral, both nonnegative and the
latter strictly positive. Raff<Rcorr<E*current is certified in scratch.
Rcorr>=0 remains OPEN. New leaf ThetaCuspC5CorrelatedFourthSource saved
and wired once; final audit pending. Search76041 partial: judging stage
malformed JSON, inventory complete, source-only candidates checked
against actual source/Lean. All20 candidates/20source arguments and
proposed ingredient set inspected; no existing inner-sign producer.

N35 saved final48190 exit0, empty log; wired once (owned total52).
Imported axiom75705 exit0: all nine endpoints standard3 only.
Lint59199 exit1: twelve unrelated unreachable modules, all errors
inspected; no owned TH leaf or forbidden proof declaration.
N36 search55443 nonpartial, complete inventory, background refresh;
all candidate/source/ingredient groups inspected. Generated inner-current
proposal mixed unrelated Hawking current APIs and is inapplicable.
Local inverse-clock positivity was ALREADY proved in IntrinsicClockGerm;
rebuilding that local germ would not move frontier.

N36 PAPER next full-current mechanism: let B=c''-4c, G=source primitive,
F=-G', H=-B', h=-F'/G. N35 gives sigma=hB+H'>0. Exact source flux
J=F*B-G*H=F*PrimitiveReserve is positive and satisfies J'=-G*sigma<0.
Also (B/G)'=J/G². Thus normalized defect has strictly decreasing slope
in its intrinsic coordinate integral dx/G². Test this finite-interval
constraint inside the complete current, retaining boundary and clock
terms. Full Rcorr>=0 remains the actual conjecture, not implied by
J>0 or J'<0 separately. New flux law paper only pending search/audit.

N36 search35042 partial (malformed filter/judge JSON), index1224658,
complete inventory1224661/current1224663, refresh in background. All20
candidate and20 source argument records and empty proof/ingredient sets
inspected. The actual primitive derivative and normalized slope are
relevant; no existing primitive-Wronskian concavity theorem was found.
Scratch19259 exit1 only redundant ring after field_simp; removed.
Scratch26254 exit1 only reversed integral_symm argument order; verified
actual Mathlib signature and repaired. Flux dissipation, strict flux
monotonicity, finite intrinsic-clock bounds and three-point source
concavity had no mathematical proof errors. Scratch3520 auditing repair.

N37 PAPER intended full-sign use of N36, not an achieved sign theorem:
T_u(x)=G(x)[B(u)/G(u)+J(u)*integral_u^x G(s)^(-2) ds]. Strict clock
concavity gives B(x)<T_u(x) for x!=u on the nonnegative source axis,
with exact common center B(u),H(u). T_u solves T''=h*T and matches
B,B' at u; actual B''=hB-sigma. Hence the difference has a positive
Green representation on either side of u. Solving c''=4c+B then gives
a single center-matched fourth-order comparison model, whose forcing
is the SAME sigma already retained in the current. Next hard task:
prove the COMPLETE inverse-clock current sign using this coupled
Green representation. Ordering c alone does not imply ordering the
nonlinear current; do not infer it. Keep full clock and action terms.

N36 scratch3520 exit0, empty log. Saved
ThetaCuspCurvatureDefectPrimitiveFlux; final56414 exit0, empty log.
Wired once after N35, owned count53. Certified J>0, exact J'=-G*sigma,
strict decrease, exact normalized-defect interval integral, strict
clock slope bounds, two-sided common-center tangent and three-point
clock concavity. Imported axiom audit follows. Lint30156 exit1, fifteen
unrelated unreachable modules; all errors inspected, no owned TH leaf
or forbidden declaration. Scoped diffcheck passes. The full inner
current sign, C5 compensation and arbitrary-degree/RH remain OPEN.
Assessment: new interval source structure and sharper complete-current
lower comparison, but no newly closed inner-current subdomain.
N37 must use the common Green slack in the complete nonlinear current;
repeating source-envelope comparisons alone will not settle this sign.

N37 PAPER audit of the proposed next mechanism: do NOT assume that
raising a center-matched curvature decreases the raw enriched current.
For a constant-center curvature scale c with fixed positive displacement,
the exact action-power kernel has leading enriched term
(576/625)*(2*alpha+beta)*Z^3*Q^2. Under a center-preserving positive
curvature variation v, its leading relative first variation is
[v+(t/2)v'+2*V1/t+2*V2/t²]/c, with V1=integral_0^t v and
V2=2*integral_0^t (t-s)v(s). This is positive when those terms are
positive, while highest-jet variations are adverse near the germ.
This is a PAPER diagnostic of a likely overstrong raw-current
monotonicity statement, not an actual-source counterexample or Lean
no-go. Check this carefully before investing in that lemma. The
surviving exact source Green representation remains valid; the
complete current must retain its positive bulk and signed variation,
or use an appropriate positive normalization. No route is retired.

N36 final imported axiom26531 exit0: all eight endpoints depend only
on propext, Classical.choice, Quot.sound. Saved module warning-free.
All N35/N36 owned scratch and staging files removed; audit logs and
search JSON retained. No owned running build/search process remains.
Both modules wired once; RN heading preserved. RH goal not achieved.

N38 exact clock-cancellation attack, using corpus search33789 (nonpartial,
complete inventory1224817/current1224818, background refresh). All20
candidate/20 source/empty proof/one ingredient groups inspected. Energy
upper/lower and rational envelope are applicable; proposed energy-only
sign inference is not sufficient. Saved source APIs read directly.
Scratch19455 exit0: complete constant-shape current with coarse clock
C=1+6Z is EXACTLY
 -(5968/75)Z²-(4464/125)Z³-(336/25)Z⁴-(1728/625)Z⁵<0 for all Z>0.
This is a no-go for that clock relaxation, not a theta-source counterexample.
Rational envelope retains exact correction
 Clinear(z)=1+z²/3-z⁴/[3(15+3z+z²)].
Positive survivor under audit: complete enriched constant-shape current
with Clinear(z), Z=z²/18, is positive globally. The unenhanced term follows
from saved linearEnvelope_lt_constantInverseClockGrowth; enrichment has
positive cross reserve 4R36R16+Flow36R16-Flow16R36. Paper proof is closed;
new positive survivor added to scratch for audit. For actual source,
retain this quartic clock correction together with the N35/N36 common
source slack in the FULL current; independent quadratic clock estimates
cannot prove even the zero-defect comparison. No actual-source sign closed.

N38 positive scratch3183 exit0, empty log. Saved/wired
ThetaCuspC5ClockQuarticCancellation (owned count54). Final74609 running;
lint18373 running. Failed-relaxation card created at
5-failed/theta-c5-quadratic-clock-current-relaxation.md, with exact
negative theorem, full positive survivor and dependency-closed proof.
Do not call the actual-source current falsified: constant-shape model
has zero source derivatives and only diagnoses the quadratic relaxation.

N39 PAPER next hard current attack: keep clock/action and fourth source
in ONE moment representation. N38 positive comparison uses z²=18Z,
whereas actual z²>=18Z with exact source excess
 z²-18Z=k²[(E-t*e)²+4*t*E*(e-c(u))].
Equivalently, writing vmean=E/(c(u)*t), actual
 z²=(9/2)*Z*vmean*(1+alpha)².
Do not replace this excess by an independent arbitrary variable.
With r0=c''(u), v(s)=reflected fourth curvature and the odd reflected
jets zero, the common Peano representations are
 e(t)=c(u)+r0*t²/2+integral_0^t (t-s)^3*v(s)/6,
 E(t)=c(u)*t+r0*t³/6+integral_0^t (t-s)^4*v(s)/24,
 Q(t)=c(u)*t²+r0*t⁴/12+integral_0^t (t-s)^5*v(s)/60.
These formulas use e''''=v (NOT e'''=v); preserve the displayed orders.
The N36 center-matched model and SAME positive sigma Green remainder
then constrain all moments jointly. Target: prove the full rational-clock
current polynomial after clearing only positive denominators, retaining
quartic clock correction and these common source moments. This is a
paper attack, not a proved sign or a reason to repeat comparison wrappers.

N38 saved final74609 exit0/empty log; imported axiom20364 exit0,
all three endpoints standard3 only. Wired once, owned count54.
Lint18373 exit1: twelve unrelated unreachable modules, all inspected;
no owned TH or forbidden declaration error. Scoped diffcheck clean.
Failed-relaxation card finalized with its positive survivor audited.
All owned N38 scratch/staging removed, logs/searchJSON retained.
No owned live build/search processes. Actual inner sign and RH remain open.

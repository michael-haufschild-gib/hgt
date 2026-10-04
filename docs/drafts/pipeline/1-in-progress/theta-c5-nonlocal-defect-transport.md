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

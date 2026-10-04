# RN: center variation of the full finite-pair canonical current

2026-10-04. Formalized and directly audited: 25 public theorems across four leaves.
The global pointwise negative-current conjecture is false for the actual source.
RH and the integrated Schur-coordinate comparison remain open.
Parent: ../../1-in-progress/rn-finite-pair-positive-transport-primitive.md.

Corpus: actual transport a,B and their coupled ODEs; PacketPositivity;
CanonicalSpeed; actual center jets H_y(0,0)=0, H_yy(0,0)=-2I;
ThetaConfluentCoordinateCurrent projective descent and sourceCurrent identity.
Deep center-moment search inspected; derivative mass and center-source curvature
results are source inputs, not a proof of the new upper comparison.

Put q=c(0)>0, d=c''(0)>0, R=d/q, alpha=I/J, P=k(0)^2.
Projective descent c''/c<=R gives v<=R*p. Convexity of p and p(0)=0 give:
  p(t)-q*t <= R*t^2*p(t)/6,
  t*c(t)-p(t) <= R*t^2*p(t)/3.
Both have derivative proofs with zero center value. For the first, the second
derivative of R*t^2*p/6-p+q*t is nonnegative because t*c>=p and v<=R*p.
For the second, differentiate once and use the same two inequalities.

Integrating against the actual k^2 retains exact Ward identities:
  integral p*k^2=P/2,
  integral t^2*p*k^2=J/2,
  integral (t*c-p)*k^2=2I-P,
  integral t*k^2=J/2.
Therefore P<=(q+R/6)*J and 2I-P<=R*J/6, hence
  I/J<=q/2+d/(6q).
This is a structural moment comparison, with all constants fixed by exact
Taylor/transport identities. No numerical experiment or bound optimization.

For fixed t>0, paper differentiation at x=0 along y=x gives:
  a_x(t)=-p(t)+x*[alpha-(c(t)+p(t)^2)/2]+o(x),
  B_x(t)=t+x*b(t)+o(x),
  b(t)=[I_t-alpha*H(t,t)]/k(t)^2,
  I_t=integral_t^infinity u*p(u)^2*k(u)^2 du.
Then the canonical current Ican(x,x,t)/x tends to
  L(t)=p*c*[t*p/2+1/2-b(t)]-t*c*alpha+t*d(t)/12
       +q*[p*c+t*p*v-t*c^2]/(2*p^2),
where d(t)=c''(t). Since b(0)=b'(0)=0 and b''(0)=2alpha,
  L(t)/t -> q^2/2-q*alpha+5*d/12 >= d/4>0.
The exact parameter-limit theorem proves a positive actual canonical current
for small t>0 and then sufficiently small x>0. Continuity in y supplies a
strictly ordered x<y example. This falsifies the pointwise conjecture, not RH
or the integrated Schur-coordinate comparison.

Positive survivor and next proof route: retain the exact
moment upper comparison and the positive center current, while the already
formalized integrated normalized-Schur Hessian is negative. Their coexistence
forces a signed compensation across source time: a globally negative
pointwise canonical current cannot be the finite-pair producer. Work on the
complete integrated current, retaining this positive center contribution.

## Exact parameter-limit proof, formalized

For fixed t>0 use smooth secant averages
  s(x)=integral_0^1 c(t+u*x)du,
  d(x)=integral_0^1 v(t+u*x)du,
  bnode(x)=integral_0^1 u*v(t+u*x)du.
Their values at0 are c,v,v/2 and derivatives are v/2,d(t)/2,d(t)/3.
These equal the literal finite secant, its t derivative and x derivative for x>0.
Set lambda(x)=1/2-p(x)/(2*p(t+x)),
    lambda_t(x)=p(x)*c(t+x)/(2*p(t+x)^2).
They are exactly the finite canonical speed and its t derivative on y=x;
values at0 are 1/2,0 and node derivatives -q/(2p),q*c/(2p^2).

Define A=-lambda*(x+2t)*s-lambda_t and
D=bnode-lambda*d-(lambda*(p(t)+p(t+x))+lambda_t)*s.
At0, A0=-t*c and D0=-p*c. Their node derivatives are
  A1=-c/2-t*v/2+t*q*c/p-q*c/(2*p^2),
  D1=d(t)/12+q*v/(2p)-p*v/2-c^2/2+q*c-q*c^2/(2*p^2).

Remove all packet divisions before taking the parameter limit:
  Q1(x)=k(t)*k(t+x)-(H(0,x)/J)*k(t)^2,
  Q2(x)=(H(0,x)/J)*H(t,t)-H(t,t+x),
  x*k(t)*k(t+x)*Ican(x,x,t)=A(x)*Q1(x)+D(x)*Q2(x).
Q1(0)=Q2(0)=0, Q1'(0)=-p*k^2, Q2'(0)=t*k^2.
The last identity follows from the literal firstLeft(t,t)=-t*k(t)^2 Ward law.
Q1''(0)=k^2*(p^2-c+2alpha),
Q2''(0)=-2alpha*H(t,t)-secondLeft(t,t).
A0*Q1'(0)+D0*Q2'(0)=0 exactly. Dividing the remaining products by x^2
therefore needs only first derivatives of A,D and second-order Taylor quotients
of Q1,Q2. The resulting limit is exactly L(t) above. No unproved higher
regularity of an inverse-Gram coefficient is needed.

For the source-time profile limit, it suffices that b(t)->0; no b'' theorem is
needed. Write U=(p-q*t)/t^3, W=(c-q)/t^2, Z=v/t. Exact algebra gives
  (p*c+t*p*v-t*c^2)/(t*p^2)
    =[c*(U-W)+(p/t)*Z]/(p/t)^2.
The audited source derivatives give U->d/6, W->d/2, Z->d and p/t->q.
Hence this quotient tends to 2d/(3q), proving the coefficient 5d/12 in L/t.

## Validation and closure

Completed 2026-10-04, final sequential audit88345 exit0:
- ThetaFinitePairCenterMoment: 9 public theorems.
- ThetaFinitePairCurrentCenterProfile: 4 public theorems.
- ThetaFinitePairCurrentCoefficients: 8 public theorems.
- ThetaFinitePairCurrentGerm: 4 public theorems.

Each actual source file passed `lake --old env lean <file>` with empty
diagnostics. Clean leaf exports also passed. All25 public `#print axioms`
queries in /tmp use exactly propext, Classical.choice, Quot.sound. All four
leaves are wired into RHTower.lean; no umbrella or full build was run.
Formal lint34138 exits1 on twelve unrelated unreachable modules, with no
own-leaf error or forbidden proof declaration. Exact list is recorded in the
working log. No new axioms, RH premises, numerical experiments, heartbeat
increases or subagents were used.

The capstone `exists_positive_finiteCanonicalCurrent` has no premises:
  exists t x y, 0<t and 0<x and x<y and 0<finiteCanonicalCurrent x y t.
The theorem `finiteCanonicalCurrent_eq_deriv` identifies this literal function
with C_y-lambda*C_t-lambda_t*C. Thus the counterexample concerns the actual
transport current, not a surrogate or freely chosen coefficients.

The strongest positive survivor currently audited is the source-derived moment
comparison, its strictly positive center variation coefficient, and the exact
current node limit exposing that coefficient. Paper proof and Lean proof are
both complete. Only the pointwise negative-current conjecture is retired;
route RN, integrated compensation, general anchors, arbitrary rank and RH
transfer remain open. Successor:
../../1-in-progress/rn-finite-current-integrated-compensation.md.

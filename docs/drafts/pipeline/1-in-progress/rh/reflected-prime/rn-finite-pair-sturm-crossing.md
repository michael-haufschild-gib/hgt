# RN-P-7z: finite-pair signed Sturm crossing

2026-10-04. Route RN; strict quotient monotonicity and exact single-crossing
classification formalized and directly audited,22 public theorems.
Certificate: ../../../3-formalized/theta/rn-finite-pair-sturm-crossing.md.
Parent: rn-positive-correction-current.md. Packet positivity remains Lean pending.

Hard target: full finite-pair center Schur coordinate compensation. The last
advance proved a correction-current sign but Gaussian saturation showed why
that sign and B>t alone are insufficient. This step retains the actual
curvature variation through the signed forcing of N=a+s*B.

For x,t>0 set
  s=(p(t+x)-p(t))/x, d=(c(t+x)-c(t))/x, e=(v(t+x)-v(t))/x,
  j=t*s-p(t), j0=t*c(t)-p(t), q=j*s/d.
Here s'=d, d'=e, j'=s+t*d-c. The forcing is
  d-2*j*s=d*(1-2*q).

Actual-source ingredients:
- c,v positive on positive ray; p'=c, c'=v, v'=a.
- c*a-v²>0 from ThetaCurvature.logEnergy_pos.
- c*v-p*a>0 from ThetaCoordinate.projectiveSlopeReserve_pos.
- c²-p*v>0 from ThetaCoordinate.slopeEnergy_pos and c(0)>0.

Thus v/c increases and c/p decreases. Three finite comparisons follow:
1. p(t)*e<c(t)*d. For u>=t, combine p(u)*a(u)<c(u)*v(u)
   with c(u)/p(u)<=c(t)/p(t), then integrate over [t,t+x].
2. c(t)*d>=v(t)*s, by integrating v(u)*c(t)>=v(t)*c(u).
3. c(t)*j0<t*p(t)*v(t), by integrating
   u*v(u)*c(t)<t*v(t)*c(u) over 0<u<t.
Also s>c(t)>0 and j>0.

Let K=((s+t*d-c)*s+j*d)*d-j*s*e, the numerator of q'.
The first comparison yields
  p*K > d*(p*(p+2*j)*d-s²*j0).
Multiplying the bracket by c and using comparisons2,3 gives
  c*(p*(p+2*j)*d-s²*j0) > p*v*s*j >0.
Hence K>0 and q'>0 everywhere x,t>0. No numerical constants,
source truncations, generic curvature premise, or RH hypothesis occur.

Formalized consequences: q strictly increases; the signed forcing has at
most one zero and cannot return from nonpositive to positive. Endpoint q(0)=0
and the finite large-value argument below give existence and exact one-crossing
classification, now directly audited. The next nonlocal step must retain
N's exact ODE and boundary values. N>0 alone would still leave a second signed
coefficient in the full coordinate current, as the parent card records.

## Endpoint completion, paper proof

The ratio q is continuous at0 with q(0)=0: d(0)=(c(x)-c(0))/x>0.
Integrating v<2c gives d<2s, hence q>j/2 for t>0. Let
T=1+1/v(1). Since (t*c(t)-p(t))'=t*v(t)>=v(1) on t>=1,
j0(T)>=1. Also j>j0, so q(T)>1/2. The intermediate value theorem
and strict increase give exactly one positive tau with q(tau)=1/2.
Thus forcing d-2js is positive on [0,tau), zero at tau, negative afterward.
Its exact existing signed-density identification is
  forcing(x,t)=-s(x,t)^2*ThetaSturm.density(0,x,t).
So the actual energy density is negative before tau and positive afterward.
This is an exact finite-pair classification, not merely a conditional barrier.

## Next packet-positivity attack

For N=a+sB the exact ODE is N'=(Sigma+2j)*N+forcing*B,
Sigma=p(t)+p(t+x). Multiplying by rho=k(t)k(t+x) and by
exp(-2*integral_0^t j) gives derivative with precisely the forcing's sign.
The initial N value is positive by the existing normalized-row decrease.
A zero tail limit would then prove N>0: the weighted N increases to the
unique forcing crossing and strictly decreases afterward to zero.

The nontrivial analytic endpoint is s(t)*O_x(t)->0. A paper route retains
O<=H(0,x)*H(t,t), proves p(t+x)/p(t) bounded using decreasing c/p, and uses
H(t,t)<=k(t)*integral_0^infinity 2u*k(u) du. Then p(t)k(t)=-k'(t)->0
by the actual Schwartz source, proving the endpoint. These endpoint
transfers and the N ODE are now audited, using the stronger diagonal-tail
comparison to shorten the endpoint proof. N positivity does not alone settle the second signed coefficient in the full coordinate current.

The packet-positivity paper argument is now closed, including its source-tail
endpoint: see ../../../3-formalized/theta/rn-finite-pair-packet-positivity.md. Lean
transfer and all public axiom audits passed 2026-10-04. The tail corpus search returned non-partial inventory65098,
with actual prefixBalance_eq_tail and integral_transportDensity hits, but no
ready s*O endpoint. Its suggested center-secant limit is inapplicable to this
atTop problem and was not used.

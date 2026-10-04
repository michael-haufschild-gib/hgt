# RN-P-7ae: actual coarea score defect

2026-10-04. Formalized in ThetaGaussianCoareaScore.lean.
Parent: ../../1-in-progress/rn-finite-current-integrated-compensation.md.

Use the corpus's actual Gaussian coarea potential V, amplitude
A_y(u)=exp(V(0,0,u)-V(0,y,u)), slope p, curvature c, and q=c(0).
The score needed after differentiating the normalized Schur covariance is

  B_y(u)=A_y(u)-y*partial_y A_y(u)
        =A_y(u)*(1+y*leftDerivative(y,0,u)).

The equality to the actual endpoint derivative holds for u>0. Define J_y(u)
as its exact mass derivative, produced by the existing shift and potential
derivative theorems. For every y>0,

  lim z->0+ J_y(z^2)=q+c(y)-2*p(y)/y>0.

Consequently B_y is not antitone on the positive mass half-line. For every
x,y>0 there are 0<u<w such that

  (A_x(w)-A_x(u))*(B_y(w)-B_y(u))<0.

This refutes a separate monotone-covariance producer. It does not determine
the sign of the integrated covariance or refute the full RN inequality.

## Exact positive survivor and paper proof

The boundary defect has the exact positive curvature representation

  q+c(y)-2*p(y)/y = (1/y)*integral_0^y s*(y-s)*c''(s) ds.

Its primitive is s*(y-s)*c'(s)-(y-2*s)*c(s)-2*p(s).
The source identity p(0)=0 gives the endpoints; actual c''>0 gives strict
positivity. No abstract convexity premise is introduced.

Write t=shift(x,y,u), l=length(x,y,u), S=p(x+t)+p(y+t). Direct
differentiation, t_u=1/l and l_u=2/l, gives

  V_xu=[l*((x+y+t)*c(x+t)-t*c(y+t))-(x+y)*S]/l^3.

At fixed y>0 this expression and V_y(0,y,u) are continuous at u=0.
The center rate at u=z^2 is p(z)/z for z>0, tending to q. Substitution into

  J_y=A_y*[(M_00-M_0y)*(1+y*V_y(0,y,u))+y*V_yu(0,y,u)]

gives the stated defect. Its strict sign yields positive derivatives at
positive masses. Antitonicity would force those derivatives nonpositive.
Extracting an ordered score increase and using strict decrease of A_x gives
the adverse covariance pair.

## Validation

Export5123 passed. Final sequence29877 exited0 with
`lake --old env lean GaloisForLFunctions/RHTower/ThetaGaussianCoareaScore.lean`
and all9 public axiom queries in /tmp. Every axiom closure is exactly
propext, Classical.choice, Quot.sound. An informational ring-normalization
suggestion remains; there are no source errors or warnings. The import is
wired into RHTower.lean. No full build, numerical experiment, additional
axiom, unproved premise, heartbeat increase or subagent was used.

The surviving hard problem is the coupled score integral
integral Q_xy > (integral density(0,x)/Z)*integral Q_0y,
Q_xy=density(x,y,u)*(1+y*V_y(x,y,u)), for 0<x<=y.
Its actual integrability/derivative transfer and compensation sign remain open.

Lint72816 exited1 with14 unrelated unreachable modules and no own-leaf or
forbidden-declaration error; exact names are retained in the working log.

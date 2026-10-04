# RN-P-7ah: actual source concavity in the potential and Ward clocks

2026-10-04. Formalized in ThetaDiagonalClockGeometry.
Parent: ../../1-in-progress/rn-finite-current-integrated-compensation.md.

Let k be the actual theta source, U=-log k, p=U', c=p', v=c' and a=c''.
On x>0 put

  r=p/x, z=x*p-1, Q=z'=p+x*c,
  A=x*c-p,
  M=3*x*c^2-3*p*c-x*p*v,
  R=c*v-p*a,
  B=x*M-2*A^2,
  C=x*M-A^2.

The literal source satisfies B>0 and C>0 everywhere on the positive ray.
The slope ratios with respect to the two increasing clocks are positive
and strictly decreasing:

  s_U=(p/x)'/p=A/(x^2*p),
  s_z=(p/x)'/Q=A/(x^2*Q),
  s_U'=-B/(x^3*p^2)<0,
  s_z'=-2*C/(x^3*Q^2)<0.

Both strict global chord comparisons are formalized. For every 0<x<y,

  (U(y)-U(x))*s_U(y) < r(y)-r(x) < (U(y)-U(x))*s_U(x),
  (z(y)-z(x))*s_z(y) < r(y)-r(x) < (z(y)-z(x))*s_z(x).

These express strict concavity of the actual boundary coarea rate p/x
in source potential and in the diagonal Ward clock. No inverse-clock
existence or sign is assumed as a premise.

## Dependency-closed paper proof

The admitted source geometry gives p,c,v,A,M,R>0 on x>0,
A'=x*v and M'=x*R+4*v*A. Consequently

  B'=M+x^2*R>0,
  C'=M+x^2*R+2*x*v*A>0.

Both reserves vanish at zero, proving their strict positivity. Exact
algebra gives

  B=x^2*c^2+x*p*c-2*p^2-x^2*p*v,
  C=2*x^2*c^2-x*p*c-p^2-x^2*p*v.

Differentiating the displayed source slope ratios gives the two strict
negative derivatives. For the lower U chord, r(t)-U(t)*s_U(y) has positive
derivative for x<t<y. For the upper chord, U(t)*s_U(x)-r(t) has positive
derivative there. The same argument applies to z. All inputs are established
properties of the actual source; no abstract curvature hypothesis remains.

## Validation

API1601 passed. Final direct source check/export3895 used
`lake --old env lean GaloisForLFunctions/RHTower/ThetaDiagonalClockGeometry.lean`
with the corresponding olean output path and exited0 with no diagnostics.
The leaf is wired into RHTower.lean. All20 public theorem axiom queries26415
exited0, each with exactly propext, Classical.choice and Quot.sound. The
manifest comparison found20 expected,20 audited, none missing or extra.
Lint36597 exited1 with18 unrelated unreachable modules and no own-leaf or
forbidden-declaration error; the working log records all18. Targeted
whitespace validation passed. No full or umbrella build, numerical
experiment, added axiom, unproved source premise, heartbeat increase or
subagent was used.

## Remaining mathematical step

For positive coarea mass u, let alpha=shift(0,x,u), beta=x+alpha,
ell=alpha+beta, S=p(alpha)+p(beta), and

  N=ell*(beta*c(beta)-alpha*c(alpha))-x*S,
  T=alpha*c(alpha)+beta*c(beta)+alpha^2*v(alpha)+beta^2*v(beta).

The actual rate m=S/ell has m_x=N/ell^3. Its proposed source-potential
concavity requires

  (3*x*p(x)+ell^2*c(x))*N-p(x)*ell^2*(T-S)>0.

At u=0 this is exactly x^2*B>0, now proved. For u>0 the complete two-endpoint
comparison remains unproved. The identity

  N=ell*(A(beta)-A(alpha))+2*u*(r(beta)-r(alpha))

shows where the new potential chord law enters while retaining the other
term and its variable weight. Even a proof of this whole-mass comparison
must still be coupled with the normalized mixed row to control the complete
Ward forcing. Global normalized diagonal compensation, the finite-pair
chamber, general anchors, arbitrary rank and arithmetic RH transfer remain
open. This result does not prove or falsify RH.

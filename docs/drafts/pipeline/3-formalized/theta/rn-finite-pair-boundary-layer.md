# RN: exact negative finite-pair boundary layer

2026-10-04. Formalized and directly audited: nine public theorems in
ThetaFinitePairBoundaryPackets and ThetaFinitePairBoundaryCurrent.
Parent: ../../1-in-progress/rn-finite-current-integrated-compensation.md.

Write k for the literal source, p=-(log k)', c=p', q=c(0), J=H(0,0),
I=integral_0^infinity t*k'(t)^2 dt, and gamma=I/J-q/2.
The corpus's actual center source gap proves gamma>0.

## Exact theorem

For every fixed r>=0, as x->0+,
  finiteCanonicalCurrent(x,x,r*x) -> -gamma/(2*(1+r)^2)<0.
Consequently the actual current is eventually negative along each such ray.
The complete matched transport moment satisfies
  transportMoment(x,x,r*x)/x -> gamma>0.
These concern the same literal current whose positive interior germ was
formalized in rn-finite-pair-current-center-variation.md. The two limits
retain different parameter regimes; neither changes the other theorem.

## Dependency-closed paper proof

The actual source and axis kernel jets give, for every real scaling a,
  (k(a*x)-k(0))/x^2 -> -q*k(0)*a^2/2,
  (H(0,a*x)-J)/x^2 -> -I*a^2.
The globally valid divided-Schur identity is
  H(u,v)=H(0,u)*H(0,v)/J+u*v*dividedSchur(u,v).
Its continuous axis extension has value 2I-k(0)^2 at the origin. Therefore
  (H(a*x,b*x)-J)/x^2 -> -I*(a-b)^2-k(0)^2*a*b.
This includes zero scaling directions and needs no uniform joint remainder.

Apply these exact jets to the actual cleared packet numerators. At t=r*x,
  a_x(t)/x -> gamma-q*r,
  B_x(t)/x -> r.
The compact secant averages satisfy s_x(t)->q and both derivative averages
->0. Also
  lambda(x,x,r*x) -> r/(2*(r+1)),
  x*lambda_t(x,x,r*x) -> 1/(2*(r+1)^2).
Thus for the exact diagonal current Ican=A*a+D*B,
  x*A -> -1/(2*(r+1)^2),
  x*D -> -q/(2*(r+1)^2).
The two packet contributions cancel their r terms, giving the stated negative
profile. Separately C=a+s_x*B gives the positive matched coefficient gamma.

The profile suggests a negative boundary mass gamma/2 after source-time
integration, but no weak measure convergence or improper limit interchange
is asserted by these theorems. The actual weighted prefix limit and global
finite-pair signed compensation remain open.

## Validation

Clean exports: packets in sequence19053, current52982, both with empty diagnostics.
Final sequence8949 exited0:
- `lake --old env lean GaloisForLFunctions/RHTower/ThetaFinitePairBoundaryPackets.lean`
- `lake --old env lean GaloisForLFunctions/RHTower/ThetaFinitePairBoundaryCurrent.lean`
- All nine public `#print axioms` queries in /tmp.

Both actual-source audit logs were empty. Each theorem uses exactly propext,
Classical.choice, Quot.sound. Both leaves are wired in RHTower.lean. No full
or umbrella build, added axiom, RH premise, numerical experiment, heartbeat
increase or subagent was used. Explicit parameter-path typing removed one
elaboration timeout; treating source values as fixed algebraic variables
removed unnecessary normalization inside function arguments.

Lint61941 reports13 unrelated unreachable modules, recorded in the working
log, and no own-leaf error or forbidden proof declaration. The RH goal remains
active: integrated compensation, general anchors, arbitrary rank and arithmetic
transfer are not closed by this boundary theorem.

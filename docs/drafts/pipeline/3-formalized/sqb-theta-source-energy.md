# SQB: quantitative theta-mode energy and strict source disk

The actual theta mode now has a uniform relative energy bound and an
explicit pointwise disk bound. The resulting phase current remains
positive after the half-spectral gauge required by the transformed
differential equation. Native occurrence and RH remain unproved.

## Statements

For every actual Xi divisor copy q, write z=b+ic=xiSpectralPoint(q),
u=SelbergThetaSourcePhase.mode(q), Phi=thetaCuspFullSource, and Q=Phi'/Phi.
Put f=exp(-c x)Phi, U=exp(-c x)u, w=exp(-c x)|u|^2/Phi, m=integral f,
M=integral w, and L=u'/u. Lean proves

    Im(integral x U)=m/b^2,
    m/b^2 < M < 2m/b^2,
    |1+b u(x)/Phi(x)| < 1                 for every real x,
    b (Im(L(x))+b/2)>0                   for every real x.

The statements take only the actual divisor copy and, for pointwise
statements, the real spatial point. The nonzero ordinate, finite positive
mass, integrability, smoothness and vanishing endpoint terms are proved.

## Closed proof

The previously proved bounded source ratio R=u/Phi multiplies the tilted
theta Schwartz source. Multiplication of a Schwartz function or its
derivative by x supplies the required signed moments. These facts prove
absolute integrability of U, xU, w, xw, Qw and xQw and all endpoints used
below. No quadrature or numerical certificate enters the proof.

Integrating U'=-ibU-if and (xU)' gives Im(integral xU)=m/b^2.
The exact derivative w'=(c-Q)w-2 Im(U) then gives

    integral x(Q-c)w=M-2m/b^2.

With mu=(integral xw)/M, strict decrease of Q makes
P(x)=-(x-mu)(Q(x)-Q(mu))w(x) nonnegative everywhere and strictly positive
at mu+1. Continuity and integrability imply integral P>0. The proved
gauge balance integral Qw=cM and the definition of mu give
integral P=-integral x(Q-c)w. This proves the strict upper energy bound.
The strict lower bound is the positive variance identity at tilt -c.

For the pointwise strengthening, define H=w+2 Re(U)/b. Its exact
derivative is H'=(c-Q)w and both endpoint limits are zero. If Q(x)>=c,
strict decrease of Q makes H strictly decreasing to x from the left.
If Q(x)<=c, it makes H strictly increasing from x to the right. Thus
H(x)<0 for every x. Clearing positive factors gives

    b^2|u(x)|^2+2b Phi(x)Re(u(x))<0,

which is precisely the strict disk inequality. Combining this with the
previously proved phase-density identity gives b(Im(L)+b/2)>0.

The disk also implies |u/Phi|<2/|b| analytically. This corollary is not
exported as a separate Lean declaration. All these bounds retain the
complete source and transverse parameter; none claims native occurrence.

## Audit

Module: `formal/GaloisForLFunctions/RHTower/SelbergThetaSourceEnergy.lean`.
Namespace: `RHTower.SelbergThetaSourceEnergy`. Five public declarations,
466 lines, wired once into `RHTower.lean`.

- Complete scratch and canonical source checks passed using
  `lake env lean FILE`, both without diagnostics. Logs:
  `/tmp/sqb31_check.log`, `/tmp/sqb31_source_check.log`.
- Final leaf build passed:
  `lake --old build GaloisForLFunctions.RHTower.SelbergThetaSourceEnergy`.
  The preflight and every final `Built` line identify only this leaf;
  it rebuilt in 33 seconds. Dependencies were replayed from existing
  artifacts, so this is not a fresh whole-dependency audit. Logs:
  `/tmp/sqb31_preflight.log`, `/tmp/sqb31_leaf_build.log`.
- All five public declarations passed `#print axioms` in
  `/tmp/sqb31_axioms.lean`. Output `/tmp/sqb31_axioms.log` contains only
  `propext`, `Classical.choice`, `Quot.sound`.
- The latest repository formal lint reports one separate wiring error:
  `SelbergMaassProjectionFlux` is unreachable from `RHTower.lean`.
  It reports no error in this module or its wiring. This separate module
  was not edited. Log: `/tmp/sqb31_lint.log`. The earlier energy-only
  revision passed repository lint in `/tmp/sqb30_lint.log`.
- Declaration indexing passed; scoped whitespace checks passed.
  Index log: `/tmp/sqb31_index.log`.

All owned foreground Lean/Lake processes exited. No numerical computations,
full builds, umbrella builds, or frontier-map edits were used.

## Remaining mathematical obstacle

The complete native modular Gram norm and normalized residual have not
been bounded using these source estimates. The actual Q-dependent forcing
in the transformed equation remains present. A proof must transport the
original source into normalized native approximate vectors at the unchanged
full Xi target before the existing real-preimage classification can prove RH.
The frontier map is read-only and has not been edited by this work.

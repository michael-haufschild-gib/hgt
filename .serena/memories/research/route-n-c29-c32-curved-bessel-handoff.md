# Route N C29-C32 positive survivor (2026-08-10)

Route N is terminal as an RH-producing mechanism. Its strongest positive survivor is a complete handoff to Route T mass propagation.

## C29
`XiMassSpacelikeContourOptimality.lean`
- exact attained maximum of curved contour rate
  `(sigma*c+h*s)^2-(u*s)^2`
  equals `Re sqrt((sigma+i*u)^2+h^2)^2`;
- actual nonnegative optimizer;
- strict improvement `h-u < sqrt(h^2-u^2) < kappa`;
- sharp critical slope `a/sqrt(a^2-1/4) < a/(a-1/2)`.

## C30
`XiMassHyperbolicFourierRepresentation.lean`
- exact full-line branch-free substitution `x=a sinh t`;
- mass Fourier transform is integral of entire hyperbolic kernel
  `a cosh t exp(-(sigma+i*u)a cosh t) exp(-i*h*a sinh t)`;
- all change-of-variables and integrability obligations closed.

## C31
`XiMassHyperbolicCurvedContourDecay.lean`
- one-sided lower contour deformation for every `0<=theta<pi/2`, proved by recentering and applying symmetric strip theorem;
- exact shifted norm with
  `A=sigma cos theta+h sin theta`, `B=u sin theta`;
- Lorentz boost `A cosh x+B sinh x=q cosh(x+r)`,
  `q=sqrt(A^2-B^2)`, `r=arsinh(B/q)`;
- exact Fourier bound `|F| <= 2*a*exp(r)*K_1(a*q)`;
- coefficient-faithful comparison
  `K_1(s) <= exp(-(s-s0))*K_1(s0)` for `0<s0<=s`.

## C32
`XiMassOptimalCurvedBesselDecay.lean`
- proves C29 optimizer has `c>0`;
- converts optimizer to actual angle `0<=theta<pi/2` using complex argument;
- proves `q=Re sqrt((sigma+i*u)^2+h^2)`;
- provides existential optimal Bessel and fixed-base full-exponent bounds.

Both new modules are imported by `GaloisForLFunctions/RHTower.lean`.
Direct `lake env lean` and explicit olean compiles pass.
Capstone axiom audits use only `propext`, `Classical.choice`, `Quot.sound`.

C41-S is closed. Remaining Route T open core: source-derived centered von Mangoldt cancellation in residual timelike-plus-glancing cone before termwise norms.
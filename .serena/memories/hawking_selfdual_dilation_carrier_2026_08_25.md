# Self-dual Hawking dilation carrier (2026-08-25)

Exact new route files:
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingSelfDualEinsteinDilationCarrier.lean`
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingSelfDualDilationSexticIncidence.lean`

Core result:
- Exact AdS4 self-dual double-copy plane-wave vertex vanishes on diagonal but, at common transverse cusp charge, equals `(1/2) h^2 (p-q)^2`.
- Hawking dilation eigenmode is a Mellin continuum. Pair moment is
  `4 B(a+2,a)-4 B(a+1,a)+B(a,a)=B(a,a)/(2a+1)`.
- Gamma normalization collapses coefficient to `a h^2`.
- Exact BM ingoing exponent gives `a=-2 alpha=1+rho/2`; theta cusp charge is `h=rho/2`.
- Therefore quadratic coefficient is `A^2(1+rho/2)(rho/2)^2`, nonzero at every Xi divisor.
- This supplies actual doubled-weight carrier in exact self-dual Einstein cusp-horizon principal germ. Every tilted divisor is forced to mix against a symmetric BM angular operator.
- Anti-self-dual conjugate supplies negative-charge carrier. With two horizon memories, protected sextic triple pole is nonzero and lower one-/two-Green continuous completions cannot cancel. Jost incidence iff Xi tilt is zero.

Honest remaining equation:
identify full non-self-dual reduced Teukolsky source with chiral principal germ modulo Teukolsky range, or exclude cancellation by other same-three-Green contributions in global Evans projection.

Verification:
direct compiles passed; new theorem axiom audit only `propext`, `Classical.choice`, `Quot.sound`. Lint remains red only from pre-existing unrelated umbrella reachability failures. Temp scratch and object artifacts removed. No git used.
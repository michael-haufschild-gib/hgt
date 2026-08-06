# Route R phase-quadrature frontier (2026-08-06)

New unconditional Lean modules, wired into `GaloisForLFunctions/RHTower.lean`:
- `RHTower/RouteRPrimeLogEssentialCapPhaseGeometry.lean`
- `RHTower/RouteRPrimeLogEssentialCapRadialPhasePolarization.lean`
- `RHTower/RouteRPrimeLogEssentialCapReflectedPhaseHermiticity.lean`
- `RHTower/RouteRPrimeLogEssentialCapPhaseQuadraturePolarization.lean`

Key new result: for nonzero `z : ℂ`,
[
  \operatorname{im}(z+z^{-1})^2+
  \operatorname{im}(i(z-z^{-1}))^2
  =(\|z\|-\|z^{-1}\|)^2
  =(\operatorname{normSq}z-1)^2/\operatorname{normSq}z.
]
Thus one prime plus even/odd reflection quadratures eliminates the real-axis phase-node escape; joint Hermiticity iff `‖z‖=1`.

For Route R physical half-density character, the quadrature port:
- equals reciprocal Gamma gain mismatch squared;
- equals `(deningerHalfDensityMateGain-1)^2 / deningerHalfDensityMateGain`;
- times retained coefficient normSq equals paired physical-minus-source positive phase energy;
- after multiplying by mate gain, equals normSq of explicit pre-divisor Cartier/Bockstein comparison defect.

Formal endpoint bridges:
`CCMRationalAdelicPrimeXiReflectedPhaseQuadratureLanding p rho` iff:
- `CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho`;
- `CCMRationalAdelicPrimeXiSameFiberNormIdentity p rho`;
- `CCMRationalAdelicPrimeXiSourceDaggerIdentity p rho`;
- source Cartier physical dilation defect = 0;
- actual cofinal central Bockstein source-null-homology.
Global landing at one prime iff RH.

Unconditional source-side laws:
- source phase character is unitary;
- reflected source even and oriented odd moments are real;
- physical reflected moment imaginary part is exact fixed-grade evaluation of an independently defined phase-twisted reflection-minus-identity half-grade source boundary.

Honest remaining producer: prove both physical quadratures inherit source reality (equivalently fixed-grade source boundary evaluation descends/nulls). Existing variable-grade boundary exactness alone does not imply this; fixed-grade evaluation does not commute with source homology. Regular/singular det2-BV data provide the two natural quadrature channels but no current theorem annihilates their common mate-gain defect.

Verification:
- direct `lake env lean` green on all new modules;
- targeted `lake build GaloisForLFunctions.RHTower.RouteRPrimeLogEssentialCapPhaseQuadraturePolarization` green;
- key theorem axiom audits: only `[propext, Classical.choice, Quot.sound]`;
- forbidden declaration scan clean;
- no stale Route-R Lean process.
# Hawking–Teukolsky mediator pole multiplicity endpoint (2026-08-25)

New corpus-absent result formalized in `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskyMediatorPoleMultiplicityEndpoint.lean`; imported by `formal/GaloisForLFunctions/RHTower.lean`.

Let `a = Re ρ`.
- Functional-reflection mediator `z_F=-5i/2`, `Ω_F(n)=-i(4n+5/2)` is simultaneously BM `QNMPlus(2n,z_F)` and `QNMMinus(2n+1,z_F)`. Hence normalized full Jost and literal physical boundary Jost have order 2; physical Green has order -2.
- Reflected-real-pair mediator `z_R=i(2a-7/2)`, `Ω_R(n)=-i(4n+3-a)` is always `QNMPlus(2n,z_R)`. Companion radial parameter is `b=a-3/2-2n`; inside `0<a<1`, it is a negative integer iff `a=1/2`. Thus physical Green order is -2 iff critical line, and -1 when tilted.
- Physical Gamma prefactor is regular/nonzero: `c_R=a-4n-2` lies between consecutive negative integers; `c_F=-4n-3/2`.
- Pointwise theorem: `d4BMXiMediatorPhysicalGreen_orders_eq_iff`.
- Global endpoint: `riemannHypothesis_iff_d4BMXiMediatorPhysicalPoleMultiplicityMatches`.

Scientific scope: exact Birmingham–Mokhtari/Aros hypergeometric scattering incidence, not yet full nonlinear gravitational producer. Existing mediator bright factors are separated first-mass/Eisenstein components, not full gauge-invariant reduced second-order Teukolsky source. Remaining open core: prove gauge-invariant nonlinear source has nonzero projection onto relevant mediator principal parts; then pole-order mismatch can force tilted multi-channel mixing.

Verification:
- `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskyMediatorPoleMultiplicityEndpoint.lean` passed.
- New theorem axioms: only `propext`, `Classical.choice`, `Quot.sound`.
- Static lint sees new module reachable; remaining lint failures are pre-existing unreachable modules: `RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauColdBoundaryNoGo`, `SuzukiShiftedXiBoundaryFactorization`, `HTGeometry.SecondOrderConstraintDescent`.
- Scratch/generated oleans removed. No git used.
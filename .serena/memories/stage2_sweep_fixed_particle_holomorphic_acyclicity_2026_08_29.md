# Fixed-particle holomorphic acyclicity formalized (2026-08-29)

Promoted card:
- `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/06-integrable-qft-yang-baxter/fixed-particle-holomorphic-acyclicity-identity-zero-yang-baxter.md`

New Lean modules:
- `formal/GaloisForLFunctions/HTGeometry/HolomorphicRightEvolution.lean`
- `formal/GaloisForLFunctions/HTGeometry/FixedParticleHolomorphicAcyclicityIdentityZeroYangBaxter.lean`

Main declarations:
- `differentiableOn_firstSegmentPrimitive`
- `analyticOnNhd_rightComplexEvolution`
- `isUnit_rightCaratheodoryEvolution`
- `eq_zero_of_continuous_right_volterra_on_Icc`
- `FiniteHolomorphicRightCocycle.exists_holomorphic_invertible_gauge`
- `FiniteHolomorphicRightCocycle.fixedParticleHolomorphicAcyclicityIdentityZeroYangBaxter`

Proof architecture:
- Constructed multivariable holomorphic Peano--Baker evolution using complex radial Picard terms, compact-uniform factorial bounds, and locally uniform holomorphic limits.
- Transported left evolution through opposite Banach algebra to obtain right evolution.
- Proved classical ODE law, explicit inverse witness, right-Volterra uniqueness.
- Constructed radial logarithmic cocycle, finite Reynolds generator, and gauge covariance by ODE uniqueness on [0,1].
- Adjacent collision identity on a generating set implies center normalization for all permutations.
- Specialized to coordinate right action of `Equiv.Perm (Fin n)` and finite-dimensional continuous endomorphism fibers; proved direct finiteness of endomorphism monoid.

Verification:
- `lake build GaloisForLFunctions.HTGeometry.FixedParticleHolomorphicAcyclicityIdentityZeroYangBaxter` passed.
- Axiom audit for new analytic/ODE/capstone theorems reports only `propext`, `Classical.choice`, `Quot.sound`.
- Module wired into `formal/GaloisForLFunctions/HTGeometry.lean`.
- Full `scripts/formal_tools.py lint` was blocked only by unrelated concurrently-created modules not yet wired into HTGeometry/RHTower umbrellas; no new-module proof debt was reported.
- All owned /tmp scratch files removed.

Do not rebuild or re-audit these modules in later sweep turns unless changed.
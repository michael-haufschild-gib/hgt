# Theta cusp Hawking Araki-Woods/Davies mixing endpoint (2026-08-23)

New module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingArakiWoodsDaviesMixingEndpoint.lean`; imported by `formal/GaloisForLFunctions/RHTower.lean`.

Scientific correction: a pointwise form-factor zero is invisible to reservoir-only a.c. mixing. A self-adjoint scattering dilation may have complex resonances, and one tuned Friedrichs on-shell denominator does not prove full return to equilibrium. The exact survivor is the weak-coupling two-level Davies/level-shift sector pinned at a Bohr frequency.

Construction:
- theta Born shell form factor `F_a(omega)=omega^2 XiC(omega+a i)/(4 sqrt 3 pi)`;
- exact Hartle-Hawking Araki-Woods on-shell amplitudes `sqrt(1+n_H) F_a` and `sqrt(n_H) conj(F_a)`, with proved norm squares equal to prior KMS down/up shells;
- Davies rates `2 pi` times those weights;
- explicit two-state population generator, mass conservation, Gibbs stationarity, exact detailed balance;
- transverse `(1,-1)` mode eigenvalue `-Gamma`;
- explicit exponential deviation semigroup and long-time mixing iff `Gamma>0` iff `XiC(omega+a i) != 0`;
- capstone `riemannHypothesis_iff_thetaCuspHawkingArakiWoodsDaviesMixing`.

Scope is explicit: Hartle-Hawking thermal sector, not global Unruh KMS; theta input remains moving-mirror Born coefficient; no claim of full interacting Pauli-Fierz mixing iff second-order width. Full return to equilibrium needs regularity/small coupling and higher-order channels can exist.

Verification: direct Lean compile passed. Axiom audit for sector and capstone uses only `propext`, `Classical.choice`, `Quot.sound`. No forbidden declarations. `scripts/formal_tools.py lint` found only pre-existing unreachable-module errors (`HeadTailVector` and four HTGeometry modules); new module is reachable and under line limit.
# Theta-cusp Hawking quantum-Stratonovich boundary endpoint (2026-08-23)

New wired module:
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingQuantumStratonovichBoundaryEndpoint.lean`

Core result:
- Generic skew two-port exchange coordinate obeys symmetric singular-interaction jump law
  `out - in = A_g(out + in)/2`.
- `quantumStratonovichCayley_boundary_iff` proves unique solution is Cayley block with
  retention `(1-|g|²/4)/(1+|g|²/4)` and transition `g/(1+|g|²/4)`.
- Specialization `g = λ * thetaCuspHawkingFriedrichsShellFormFactor a ω` recovers existing
  source-faithful theta/Hawking Cayley outputs exactly:
  `thetaCuspHawkingQuantumStratonovichBoundary_iff_cayley`.
- `riemannHypothesis_iff_thetaCuspHawkingQuantumStratonovichBoundaryScatteringMixing` packages
  unique boundary S-matrix plus genuine Hawking Gibbs/KMS repeated-collision mixing.

Physical provenance:
- Quantum Wong-Zakai/Stratonovich Markov limit with scattering: Gough, arXiv:math-ph/0511046.
- Hudson-Parthasarathy QSDE as symmetric Schrödinger boundary-value problem:
  Chebotarev-Gregoratti, arXiv:funct-an/9706006.
- This is full nonperturbative S-matrix of singular quantum-Markov/white-noise limit, NOT raw
  Davies-Fulling moving-mirror Bogoliubov matrix; raw full-mirror=Cayley remains falsified.

Sharp no-go:
- `quantumStratonovich_lossless_KMS_every_nonzero_mix_not_force_unitCouplingWinding` adds exact
  boundary selection to prior delayed-onset countermodel.
- `g(λ)=λ²` satisfies same symmetric boundary law, exact losslessness, Hawking KMS detailed
  balance, and mixing for every nonzero real λ, but coupling winding is 2.
- Therefore Cayley provenance and all finite-coupling mixing do not force RH.
- Remaining source producer is theta-specific first-order transversality/no delayed onset:
  singular Hawking coupling must be bright at first order in every noncentral tilted sector.

Wiring/docs:
- Imported by `formal/GaloisForLFunctions/RHTower.lean`.
- Current-route row added to `docs/reports/endpoints.md`.

Verification:
- Targeted module compiled and olean emitted.
- Axiom audits: only `[propext, Classical.choice, Quot.sound]`.
- `scripts/formal_tools.py lint` passed.
- No git commands used.

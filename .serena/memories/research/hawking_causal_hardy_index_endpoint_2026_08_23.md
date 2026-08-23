# Hawking causal Hardy index endpoint (2026-08-23)

Created `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingCausalHardyIndexEndpoint.lean`, wired into `formal/GaloisForLFunctions/RHTower.lean`, documented in `docs/reports/endpoints.md`.

Key unconditional bridge:
- Upper theta-Hawking anomaly resonance `r` gives causal zero `b=-i r` and unit-aperture Cayley disk node `(b-1)/(b+1)`.
- Node lies in disk.
- Associated Blaschke Hardy scattering multiplier is isometric/lossless.
- Its outgoing range is exactly orthogonal complement of nonzero Szegő/Gamow kernel line.
- Hardy defect has finrank 1.
- Defect dimension equals physical Wigner--Smith winding charge.
- Hence boundary unitarity/KMS and ordinary passive minimality do not imply analytic asymptotic completeness.

RH reduction:
`riemannHypothesis_iff_thetaCuspHawkingCausalHardyAsymptoticComplete`.
Explicitly labelled REDUCTION/OPEN PRODUCER, not proof. Remaining producer: identify exact nonlinear theta-mirror KMS wave operator on analytic state space and derive generalized asymptotic completeness modulo prescribed soft/horizon/IR memory, excluding additional finite-rank Hardy defects without assuming Xi zero-freeness.

Hostile-test results:
- Generic passive minimality is false producer: inner Blaschke multipliers are lossless isometries with proper codimension-one range.
- Source-native finite prime ferromagnetic Lee--Yang route already has local-uniform no-go in corpus.
- Ordinary asymptotic completeness is too strong for massless scattering due IR memory; quotient/generalized completeness is needed.

Verification:
- Target `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingCausalHardyIndexEndpoint.lean` succeeded before lint.
- `./scripts/formal_tools.py lint` found only pre-existing unrelated unreachable modules; new module is reachable and no proof-debt violations were reported.
- Later axiom-audit import was blocked by pre-existing missing build artifact `HedenmalmRootFluxModularCharge.olean`; do not claim fresh axiom output.
- No git commands used.

Literature inspiration:
- Lax--Phillips/Friedrichs resonance-as-Hardy-state and functional models of dissipative operators.
- KMS analytic Hilbert realizations/standard real subspaces.
- Generalized asymptotic completeness accommodating massless soft memory.
Related prior memories: `mem:research/hawking_markov_coupling_order_no_go`, `mem:research/hawking_full_mirror_standard_van_hove_clock_endpoint_2026_08_23`, `mem:research/hawking_full_mirror_weak_coupling_order_endpoint_2026_08_23`.

# Replica observer-Jacobian compensation law (2026-08-07)

Exact open-core correction for static-local quantum complexity route.

- Raw observer Jacobian Gram determinant is not an observation invariant: repeating every reporter row k times sends G to kG and det(G) to k^v det(G), without changing matched fibres/tubes.
- Physical iid pure-state replicas exhibit same compensation. Pullback projective/Fubini–Study Gram scales exactly by r; determinant scales by r^v. Tensor fidelity and matched threshold both raise to r.
- Therefore normalized determinant lower-tail probability is exactly replica-invariant under every source measure, and existential capture over every finite or infinite target type is exactly unchanged.
- Full-rank Gram subclass already falsifies any universal raw pseudodeterminant lower-tail decay law; do not reopen this invariant.
- Minimum spectral gap also remains retired.
- Correct remaining fixed-time open core: bound incidence-normalized coarea mass of complete shallow-circuit tube after return removal. Must include intrinsic transverse sheet volume, endpoint–circuit occupancy, and fibre-sheet multiplicity. Connect to weighted resonance partition Z_r, but current result does not close Brown–Susskind.

Formal modules:
- formal/GaloisForLFunctions/HTGeometry/ReplicaObserverJacobianCompensationLaw.lean
- formal/GaloisForLFunctions/HTGeometry/PureStateReplicaProjectiveGramLaw.lean

Card:
- docs/drafts/pipeline/3-formalized/replica-observer-jacobian-compensation-law.md

Axiom audit: only propext, Classical.choice, Quot.sound. Modules and HTGeometry umbrella built successfully before shared concurrent edits. Novelty remains unverified; classical identities are rediscovered, possible novelty is circuit-union no-go/invariant correction.
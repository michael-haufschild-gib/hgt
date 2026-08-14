# Resolution-quotient replica frame capacity (2026-08-14)

## Failure and corrected invariant
Raw occupied endpoint cardinality cannot universally force inverse finite-replica frame energy: arbitrarily many distinct normalized rays may occupy one arbitrarily small projector cluster. Correct target invariant is packing cardinality after quotienting at observer Hilbert--Schmidt resolution.

## Formal survivor
New module:
`formal/GaloisForLFunctions/HTGeometry/ResolutionQuotientReplicaFrameCapacityLaw.lean`

It is wired into:
`formal/GaloisForLFunctions/HTGeometry.lean`

Key declarations:
- `exists_maximalSeparated_finset_cover`
- `norm_finitePureProjectorEuclidean_sub_sq`
- `finite_average_pow_le_diagonal_offDiagonal`
- `exists_resolutionPacking_projector_cover`
- `resolutionPacking_replicaFrameEnergy_le`
- `exists_resolutionPacking_replicaFrameEnergy_le`
- `resolutionPacking_replicaFrameEnergy_le_two_inv`
- `resolutionPacking_completeTarget_transfer`
- `finitePureStateFidelity_ge_of_projector_distance_le`
- `resolutionPacking_fidelity_transfer`
- `resolutionPacking_replicaFidelity_transfer`
- `adaptive_resolutionPacking_shortcuts_force_recurrence_energy`

Exact law for a nonempty normalized delta-separated projector dictionary of size N:
`F_r <= N^-1 + (1-N^-1)(1-delta^2/2)^r`.
If remainder is <= N^-1, then `F_r <= 2/N`.
Maximal separated set covers complete finite target at same delta. An epsilon capture transfers to a center at epsilon+delta with exact fidelity threshold and all-replica power. Capstone substitutes `2/N` into adaptive observer--spectral recurrence-energy law.

## Verification
Passed:
- `lake env lean /tmp/hgt_resolution_packing.lean`
- `lake env lean GaloisForLFunctions/HTGeometry/ResolutionQuotientReplicaFrameCapacityLaw.lean`
- `lake build GaloisForLFunctions.HTGeometry.ResolutionQuotientReplicaFrameCapacityLaw`
- axiom scratch: only `propext`, `Classical.choice`, `Quot.sound`
- no forbidden proof debt; targeted diff check clean.
Global `scripts/formal_tools.py lint` found only unrelated pre-existing/unowned reachability failures for `HTGeometry.BarnesKernelMellin` and `HTGeometry.JetDifferentialPolynomial`; new module is reachable.

## Cards
- Paper proof/falsifier: `docs/drafts/pipeline/2-fully-proven/resolution-quotient-replica-frame-capacity-law.md`
- Formal certificate: `docs/drafts/pipeline/3-formalized/resolution-quotient-replica-frame-capacity-law.md`
- Master log updated: `docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md`

## Honest remaining frontier
Target geometry and parent composition are closed. This does not prove Brown first onset, monotone/linear growth, or first recurrence timing. Genuine remaining analytic core is a quenched centralizer-centered recurrence-energy bound after return/carrier excision for one ordinary time-independent local Hamiltonian. The illustrative raw-cardinality qubit counterexample is paper-proved but not yet a Lean declaration. Related memories: `mem:quantum_recurrence/observer_spectral_frame_energy_reciprocity_2026_08_14`, `mem:quantum_recurrence/replica_projector_frame_bridge_2026_08_14`.
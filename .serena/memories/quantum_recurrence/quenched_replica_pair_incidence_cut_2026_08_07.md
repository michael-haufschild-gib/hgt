# Quenched replica pair-incidence cut law (2026-08-07)

Module: `formal/GaloisForLFunctions/HTGeometry/QuenchedReplicaPairIncidenceLaw.lean`
Card: `docs/drafts/pipeline/3-formalized/quenched-replica-pair-incidence-cut-law.md`

Conjecture loop:
- Global source-only replica frame potential comparison is true/classical but rejected as too lossy because it restores all near-diagonal source pairs and erases occupied target geometry.
- Surviving law: compressed covariance collision equals the exact product-source integral of squared overlap after projection of both replica endpoints to the occupied return-removed target span.
- Every measurable source-pair relation `R` splits the collision exactly into `R` and `R^c`; the complete shortcut mass is bounded by occupied Hilbert number times this one split.

Core capstone:
`quenchedReplica_pairIncidenceCut_bound` proves
`(mu.real E * threshold^r)^2 <= h_r * (integral_R k_r + integral_(R^c) k_r)`.
Source fibre-sheet multiplicity is retained on `X×X`; duplicate target labels and exact-return zero residuals leave the kernel invariant.

Other theorems:
- `finiteCoordinate_covarianceCollision_eq_pairKernel`
- `replicaTargetIncidenceCollision_eq_integral_pairKernel`
- `integral_replicaTargetPairIncidenceKernel_add_compl`
- `replicaTargetPairIncidenceKernel_withZero`
- `replicaTargetPairIncidenceKernel_duplicated`

Verification:
- `lake env lean GaloisForLFunctions/HTGeometry/QuenchedReplicaPairIncidenceLaw.lean`: PASS.
- `lake build GaloisForLFunctions.HTGeometry.QuenchedReplicaPairIncidenceLaw`: PASS, 8658 jobs.
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
- Forbidden-token scan: clean.
- Umbrella import wired in `HTGeometry.lean`.
- Global lint reaches no error in new module but remains red on unrelated unwired RHTower modules: ConstrainedProlateSpectralIdentification, ProlateDunsterBesselOffDiagonal, ProlateFourierSignSectors, ProlateHermiteRescale, ProlateSeparationSimplicity.

Honest remaining frontier: for ordinary fixed-q Gaussian static local Hamiltonians, construct physically correct recurrence-pair relation R, bound its mass, and prove growing-replica decay of the occupied-image compressed pair kernel on R^c strongly enough to beat h_r. External application novelty is unverified; global frame-potential identity is classical.
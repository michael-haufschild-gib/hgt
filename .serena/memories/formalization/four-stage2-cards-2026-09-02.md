# Four Stage-2 cards formalization pass (2026-09-02)

Goal: formalize all theorems in four specified Stage-2 cards without extra hypotheses/axioms; promote only genuinely complete cards.

## Completed Lean infrastructure

Centralizer:
- `HTGeometry/AllReplicaStaticCentralizerPlanarSeparation.lean` has exact all-replica graph-local weighted Hermitian family, trivial common kernel, Hall law, zero-energy atom exclusion, and all-energy Ward annihilation.
- Remaining exact bridge: nonzero-energy free matrix semicircle atomlessness via full inner rank / Strong Atiyah. Card remains Stage 2.

Cascade:
- `HTGeometry/UniversalFirstOrderEntireCascadeUnitCost.lean` has actual arbitrary-cascade algebraic branch, law coordinate frame, primitive packaging, exact unit-response Wronskian cancellation, place peel, determinant reflection.
- Remaining exact bridge: compatible nested height-one Wiman place/branch flag plus place-specific RatIn/response bounds. Card remains Stage 2.

Schanuel:
- `RHTower/SchanuelStageTwoDefectSlopeNormalForm.lean` packages clauses 1–4, affine integral-closure normalization/function field, actual coordinate pullbacks and exact regulator integrals on supplied divisor-avoiding paths.
- Remaining clause 5: projective compactification/normalization plus scheme analytification/complex-point evaluation/path production. Card remains Stage 2.

Differential variational building:
- Existing completion/lattice/standard-apartment infrastructure retained.
- New `DifferentialOperatorOreTorsion.lean`: canonical Ore-torsion submodule and torsion-free quotient.
- New/expanded `DifferentialVariationalProjectiveBuildingCarrier.lean`: corrected left-homothety carrier for left lattices; arbitrary linear, coefficient, matrix, and semidirect projective actions with identity/composition.
- `DifferentialVariationalSemilinearMatrixAction.lean`: DiffOp embedding into completed pseudodifferential field and matrix unit lift.
- New `DifferentialVariationalProjectiveStandardApartment.lean`: exact left-homothety coweight classification, injective standard apartment, rank-two nonbase point, coefficient invariance.
- New `DifferentialVariationalOreModule.lean`: literal Ω/Tor_R; full DiffOp semilinearity; torsion descent; inverse/functorial action; freeness; completed matrix unit; exact operator-row-lattice conductor certificate. This is not yet the completed-building Cartan vector; that comparison remains open.
- Top leaves wired to `HTGeometry.lean`; no umbrella build.
- Direct checks pass. Targeted builds pass for ProjectiveStandardApartment and VariationalOreModule.
- Batched #print axioms for every new declaration: only [propext, Classical.choice, Quot.sound].
- Remaining: all-lattice apartment coverage/noncommutative Cartan, relative-position vector/metric and link to operator balance, completeness/CAT(0) semisimplicity/no parabolics, axes/boundary flags, Fréchet/order reconstruction. Card remains Stage 2.

## Validation / hygiene
- `git diff --check` passed.
- `scripts/formal_tools.py lint` found no new-file lint problem but exits nonzero on unrelated pre-existing/uncommitted unreachable modules in RHTower/HTGeometry.
- All /tmp/Hgt*.lean scratch/audit files deleted.
- No Lean processes started by this task remain.
- Do not modify unrelated dirty-worktree files.

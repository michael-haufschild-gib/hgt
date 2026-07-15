# Hypertranscendental horizon Q-system core

- **ID:** `hypertranscendental-horizon-q-system-core`
- **Stage:** 3-formalized
- **Type:** THEOREM (LEAN)
- **Scientific status:** `[FORMALIZED CORE] [NOVEL SYNTHESIS]`
- **Paper parent:** `hypertranscendental-horizon-q-system`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ProjectiveHorizonCausticQSystem`

## Formalized declarations

- `rectangularSchurQSystem_rank_one`
- `rectangularSchurQSystem_rank_two`
- `qSystem_zero_propagation`
- `twoBorderMinor`
- `det_twoBorderMinor`
- `det_fromBlocks_twoBorder_mul_center`

## Certified content

The Lean module proves the all-rank Desnanot--Jacobi identity for an arbitrary matrix with an
invertible central block and two border directions.  It also evaluates the actual rectangular
Schur/Toeplitz determinants and certifies the Q-system at ranks one and two over every commutative
ring.  Rank two is the first identity involving a `3 x 3` horizon determinant.  Finally, it proves
over an integral domain that vanishing of a central amplitude and an adjacent amplitude forces one
of the two transverse amplitudes to vanish.

The remaining paper-level step identifies the four bordered determinants with the four adjacent
rectangular Jacobi--Trudi determinants, including the harmless row/column reindexing signs.  The
algebraic-independence argument giving simultaneous nonvanishing is also paper-level.  The card
therefore claims the general determinant engine and nontrivial horizon instances, not complete
formalization of the source-specialization theorem.

## Verification

The targeted leaf build

```text
lake build GaloisForLFunctions.HTGeometry.ProjectiveHorizonCausticQSystem
```

passes.  No full build was run.  Scratch axiom inspection and repository formal lint are deferred
to the lane verification gate.

## Boundary

The Lean theorem does not assert that the Q-system relation is a dynamical evolution or that its
nonvanishing converse characterizes hypertranscendence.  Its indices are static horizon depths.

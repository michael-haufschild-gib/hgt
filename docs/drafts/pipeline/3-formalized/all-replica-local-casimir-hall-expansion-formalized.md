# All-replica local-Casimir Hall expansion — formalized closure

- **ID:** `all-replica-local-casimir-hall-expansion-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./all-replica-local-casimir-hall-expansion.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [BRIDGE]`

## Lean modules

- `GaloisForLFunctions.HTGeometry.AntisymmetricStructureCasimir`
- `GaloisForLFunctions.HTGeometry.CentralCasimirHallExpansion`
- `GaloisForLFunctions.HTGeometry.AllReplicaCollectivePauliCasimir`
- `GaloisForLFunctions.HTGeometry.CentralCasimirCommonKernelCorrection`
- `GaloisForLFunctions.HTGeometry.CentralCasimirComplementHallExpansion` (new)
- `GaloisForLFunctions.HTGeometry.LieGeneratedCentralHallExpansion`,
  `AllReplicaTwoLocalPauliLieGeneration`, `FiniteReplicaCollectiveCommutantExact`,
  `FiniteReplicaCollectiveCommutantUniversalBound`, `FiniteReplicaTwoLocalPauliWordHall`
  (the positive-length replacements recorded on the paper card)

Umbrella: `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

1. `finiteReplicatedSiteCollectivePauli_bracket`, `..._comm_of_ne`,
   `finiteAllReplicaCollectiveCommutatorMatrix_bracket`, `..._conjTranspose` — equations `(1)`,
   `(8)`, `(9)`: the concrete collective Pauli commutator representation is Hermitian with the
   exact structure constants, at arbitrary site and replica cardinality.
2. `finiteAllReplicaCollectiveCommutator_quadraticCasimir_commutes` — equation `(3)`, centrality
   of the quadratic Casimir (the coordinate-free reason is
   `AntisymmetricStructureCasimir`: contracted-antisymmetric structure constants force it).
3. `finiteAllReplicaCollectiveCommutatorMatrix_mulVec_eq_zero_iff`,
   `hermitianMatrixFamilyCommonKernel`, `finiteAllReplicaCollectiveSingletSubspace` — equation
   `(2)`: the simultaneous kernel is the sitewise singlet sector.
4. `hermitianQuadraticCasimir_nonneg_and_isUnit_of_commonKernel` — equation `(11)` and
   invertibility of the Casimir off the singlet sector, giving `(4)`.
5. `completedHermitianFamily`, `completedHermitianFamily_central`,
   `completedHermitianFamily_commonKernel_eq_bot`,
   `completedHermitianFamily_scaled_biTight` — equations `(5)`–`(6)`: the completed scaled family
   is self-adjoint and exactly bi-tight,
   `∑ B*B = ∑ BB* = I`.
6. `centralHermitianMatrixFamily_subspace_finrank_of_orthogonal_commonKernel` — equations
   `(13)`–`(14)` and the boxed `(7)`: every subspace orthogonal to the simultaneous kernel expands
   exactly.
7. `finiteAllReplicaCollectiveCommutator_subspace_finrank_of_orthogonal_singlet` — the concrete
   arbitrary-site, arbitrary-replica instance of `(7)`.
8. `finiteAllReplicaCollectiveCommutator_subspace_finrank_mod_singlet` — the mixed-subspace form
   `dim U ≤ dim V + dim S_r`.

## Verification

- `lake env lean` clean, no warnings, on `CentralCasimirComplementHallExpansion` and on the
  edited `CentralCasimirHallExpansion` (four RCLike scaling declarations were made public so the
  bi-tightness statement `(6)` can be stated outside that file).
- `lake build GaloisForLFunctions.HTGeometry.CentralCasimirComplementHallExpansion` — green.
- `#print axioms` on statements 2–8: `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella import present.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

Equation `(15)` — one-step weight-two Hall expansion inside the singlet quotient — is explicitly
the *next* theorem named by the paper card, not a gate of the statements proved here.  The card's
own hostile audit records that no rank-to-complexity implication is permitted from this bridge.

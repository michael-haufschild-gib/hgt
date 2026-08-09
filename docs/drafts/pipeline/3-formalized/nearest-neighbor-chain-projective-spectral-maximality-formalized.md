# Nearest-neighbour chain projective spectral maximality — formalized closure

- **ID:** `nearest-neighbor-chain-projective-spectral-maximality-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./nearest-neighbor-chain-projective-spectral-maximality.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [PRIORITY OPEN]`

## Lean modules

- `GaloisForLFunctions.HTGeometry.NearestNeighborQubitChainMaximalRank` (new)
- `GaloisForLFunctions.HTGeometry.CommutingHermitianSpectrumSum` (new)
- `GaloisForLFunctions.HTGeometry.CommutingTermTemporalRankBound` (new)
- `GaloisForLFunctions.HTGeometry.NearestNeighborQuditPathRecurrenceLaw`,
  `NearestNeighborQuditPathGenericityLaw`,
  `ArbitraryGraphLocalHamiltonianGenericityLaw`,
  `ReplicaCollisionExtremality`,
  `PolynomialHermitianSpectrumGenericity` (reused)

Umbrella: `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

1. `exists_uniformQubitChainMaximalRank_dense_residual_fullMeasure` — the main theorem: for every
   open `n`-qubit path with `n ≥ 2`, the full real trace-zero onsite-plus-edge Hamiltonian space
   has a dense, residual, full-measure subset on which
   * the spectrum is simple (`Function.Injective` eigenvalues) — item 1;
   * `MaximallyProjectiveEnergy` holds, i.e. trace is the only rational affine relation — item 2;
   * `anchoredTemporalRank = 2 ^ n - 1` — the boxed equation `(2)`.
   It is the `q = 2` instance of the general qudit-path law
   `exists_uniformQuditPathTracelessRecurrenceGeometry_dense_residual_fullMeasure`, whose proof is
   the formalised endpoint-extension induction (Lemmas 1–4 of the paper card).
2. `MaximallyProjectiveEnergy.injective` — simplicity from maximal rank.
3. `maximallyProjectiveEnergy_orientedGap_injective` — Lemma 2: maximal rank makes every nonzero
   ordered gap distinct.
4. `PhysicallyRealizedTensorTreeSystem.hermitianSuperspaceMaximalSet_dense_residual_fullMeasure` —
   the corollary for every interaction graph containing a spanning path: any Hermitian
   Hamiltonian space containing the path-local subspace inherits dense, residual, full-measure
   maximal projective rank.
5. The recurrence-rarity corollary `(17)` is inside the qudit-path recurrence law: the strict
   anchored return frequency tends to `(2 arcsin(ε/2)/π) ^ (q ^ n − 1)`, and no nonzero exact
   projective return occurs.
6. `exists_joint_eigenvector_of_commute`, `exists_eigenvalue_split_of_commuting` — every
   eigenvalue of a sum of pairwise commuting Hermitian matrices is a sum of eigenvalues of the
   summands.  Proved without a simultaneous eigenbasis: in one summand's eigenbasis the other is
   block diagonal across equal eigenvalues, so restricting an eigenvector of the sum to a single
   eigenvalue block yields a joint eigenvector.  mathlib has no such lemma.
7. `anchoredGapSubspace_le_span_componentGapSet`, `card_componentGapSet_le`,
   `anchoredTemporalRank_sum_le`, `anchoredTemporalRank_le_of_commuting` — Corollary 2 `(18)`:
   a Hamiltonian written as `m` commuting Hermitian terms with at most four levels each — two-qubit
   terms — has anchored projective rank at most `3 m`.  Statement 1 supplies `(19)`.

## Verification

- `lake env lean` clean, no warnings, on all three new modules.
- `lake build GaloisForLFunctions.HTGeometry.NearestNeighborQubitChainMaximalRank` — green.
- `#print axioms` on statements 1, 6, 7: `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella imports present.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready: primary-source collision audit and specialist audit of the
      endpoint-transition induction are still open, and the finite-resolution crossover upper
      bound is a separate open theorem (paper card, hostile boundary item 4).

# Disconnected local spectral factorization genericity — formalized closure

- **ID:** `disconnected-local-spectral-factorization-genericity-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./disconnected-local-spectral-factorization-genericity.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED]`

## Lean modules

- `GaloisForLFunctions.HTGeometry.DisconnectedProjectiveGapModuleLaw`
- `GaloisForLFunctions.HTGeometry.HypergraphComponentFactorization`
- `GaloisForLFunctions.HTGeometry.HypergraphProjectiveSpectralFactorization`
- `GaloisForLFunctions.HTGeometry.BlockSumSpectralGenericity`

Umbrella: `GaloisForLFunctions.HTGeometry`.  The Lean statements are for an arbitrary finite
interaction hypergraph, of which the card's disconnected interaction components are the special
case of the two-section components.

## Formal theorem chain

1. `finiteComponentSumEnergy_update_sub`, `anchoredGapSubspace_component_le_total`,
   `anchoredGapSubspace_finiteComponentSumEnergy_eq_iSup` — equations `(2)`–`(4)`: total gaps are
   sums of component gaps and every component gap is a total gap, so the total gap module is the
   join of the component gap modules.  With `Submodule.finrank_iSup_le_…` this is the universal
   upper bound `(5)`.
2. `componentScaleRelationPolynomial_ne_zero`, `exists_scales_componentProjectivelyIndependent`,
   `exists_witness_hypergraphBlock` — the mutually transverse scaled witness of proof step 2, and
   the componentwise relation polynomial `(7)` with its nonvanishing at that witness.
3. `componentAnchoredGap_linearIndependent`, `iSup_anchoredGapSubspace_eq_span_componentAnchoredGap`,
   `anchoredTemporalRank_finiteComponentSumEnergy_eq_sum` — the boxed equation `(1)`:
   `dim_ℚ M(H) = Σ_r (D_r − 1)`.
4. `componentProjectivelyIndependent_of_mem_hypergraphComponentGenericSet`,
   `hypergraphComponentGenericSet_dense_residual_fullMeasure` — the countable null/meagre
   exceptional set of proof step 3; the good set is dense, residual and of full Lebesgue measure.
5. `anchoredTemporalRank_hypergraphHamiltonian_eq_sum`,
   `anchoredTemporalRank_eq_sum_hypergraphComponents` — `(1)` for the actual parameterized
   hyperedge-local Hamiltonian.
6. `injective_finiteComponentSumEnergy_of_componentProjectivelyIndependent`,
   `injective_eigenvalues_of_componentProjectivelyIndependent`,
   `injective_eigenvalues_hypergraphHamiltonian` — generic total spectral simplicity.
7. `componentProjectivelyIndependent_of_maximallyProjective_sigma`,
   `blockSumProjectiveGenericSet_dense_residual_fullMeasure`,
   `blockDiagonalProjectiveGenericSet_dense_residual_fullMeasure` — the same statements for a
   finite family of non-interacting polynomial Hermitian families.

Equation `(9)` — "component gap modules maximal internally and transverse externally" — is the
`ComponentProjectivelyIndependent` predicate that statements 3–6 are stated over.

## Verification

- `lake env lean` clean, no errors and no warnings, on all four modules.
- `#print axioms` on statements 1–7: `propext`, `Classical.choice`, `Quot.sound` only.
- All four umbrella imports present.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready: independent specialist audit still open on the paper card.

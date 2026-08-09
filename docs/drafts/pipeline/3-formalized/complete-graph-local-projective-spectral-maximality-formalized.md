# Complete-graph local projective spectral maximality — formalized closure

- **ID:** `complete-graph-local-projective-spectral-maximality-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./complete-graph-local-projective-spectral-maximality.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [PRIORITY OPEN]`

## Lean modules

- `GaloisForLFunctions.HTGeometry.CompleteGraphLocalProjectiveMaximality` (new)
- `GaloisForLFunctions.HTGeometry.CommutingHermitianSpectrumSum` (new)
- `GaloisForLFunctions.HTGeometry.HypergraphLocalHamiltonian`,
  `AnchoredProjectiveReturnDensityLaw`, `KroneckerSumSpectrum` (reused)

Umbrella: `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

1. `completeTwoLocalHyperedges`, `twoSection_completeTwoLocalHyperedges`,
   `twoSection_completeTwoLocalHyperedges_connected` — the all-to-all two-local architecture is
   the hypergraph of all two-element site subsets, whose two-section is the complete graph, hence
   connected.  This is the exact hypothesis of the corpus genericity law.
2. `completeTwoLocalMaximalSet_dense_residual_fullMeasure` — the maximal-rank set is dense,
   residual and of full Lebesgue measure in the whole real coefficient space of arbitrary
   one-site and two-site Hermitian terms on the complete graph.
3. `injective_eigenvalues_completeTwoLocalMatrix` — item 1: simple spectrum.
4. `maximallyProjective_completeTwoLocalMatrix` — item 2: trace is the only rational affine
   relation among the eigenvalues.
5. `anchoredTemporalRank_completeTwoLocalMatrix_eq` and
   `anchoredTemporalRank_completeTwoLocalMatrix_uniform` — the boxed item 3 / equation `(1)`:
   projective spectral rank `∏_v dim_v − 1`, that is `q ^ n − 1` for uniform `q`-level sites.
6. The recurrence-density corollary `(12)` is the anchored-return-density law of
   `AnchoredProjectiveReturnDensityLaw`, applied at maximal rank.
7. `anchoredTemporalRank_le_of_commuting` (with `card_image_eigenvalues_kroneckerSum_zero` and
   `eigenvalues_zero_eq_zero` supplying the level count for a term supported on a tensor factor)
   — the corollary `(13)`: a sum of `m` commuting terms with at most `q^k` levels each has
   anchored projective rank at most `m (q^k − 1)`.  The second half of the corollary — every
   neighbourhood contains a Hamiltonian of rank `q^n − 1` — is statement 2 (density).

## Verification

- `lake env lean` clean, no warnings, on both new modules.
- `lake build GaloisForLFunctions.HTGeometry.CompleteGraphLocalProjectiveMaximality` — green.
- `#print axioms` on statements 1–5, 7: `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella imports present.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready: exact-object primary-source audit and the metric first-return
      exponent remain open on the paper card.

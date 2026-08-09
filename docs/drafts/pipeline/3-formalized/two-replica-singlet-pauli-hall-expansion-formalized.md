# Two-replica singlet Pauli Hall expansion — formalized closure

- **ID:** `two-replica-singlet-pauli-hall-expansion-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./two-replica-singlet-pauli-hall-expansion.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [BRIDGE]`

## Lean modules

- `GaloisForLFunctions.HTGeometry.TwoReplicaTensorHilbertSchmidt` (new) — the trace, the adjoint
  and the Hilbert–Schmidt pairing of a sitewise two-replica tensor product, each computed factor
  by factor, plus the local orthogonality relations between the singlet algebra `span{I, F}` and
  the replica differences.
- `GaloisForLFunctions.HTGeometry.TwoReplicaEdgeHallExpansion` (new) — the site-by-site output
  family of a fixed-orientation edge commutator and its value `(7)` on every identity/swap word.
- `GaloisForLFunctions.HTGeometry.TwoReplicaEdgeHallAssembly` (new) — edge-sector orthogonality,
  the exact mismatch kernel `(12)`, and the Hall inequality `(4)`.

All three are imported by the umbrella `GaloisForLFunctions.HTGeometry`.  They rest on the
already-formalized local layer (`TwoReplicaEdgeCommutatorSwapBasis`,
`TwoReplicaGlobalSingletEdgeCasimirBridge`, `TwoReplicaLocalSingletSynchronization`).

## Formal theorem chain

### The three maps the card asked for

The card's closing list was: *the mismatch coordinate projections on the synchronized quotient,
the fixed-orientation Pauli commutator on each mismatch fibre, and the injection assembling
distinct edge-defect sectors into the full Hilbert–Schmidt space.*  All three are now concrete.

1. `trace_finiteTwoReplicaLocalMatrix`, `conjTranspose_finiteTwoReplicaLocalMatrix`,
   `trace_conjTranspose_mul_finiteTwoReplicaLocalMatrix` — a sitewise tensor product has the trace,
   the adjoint and the Hilbert–Schmidt pairing of a product.  The trace factorization is
   `Finset.prod_univ_sum` through the configuration equivalence.
   `trace_conjTranspose_mul_finiteTwoReplicaLocalMatrix_eq_zero`: one orthogonal slot kills the
   whole pairing.  **This is the global tensor form of `(11)`.**
2. `isHermitian_twoReplicaLocalSwapRaw`, `conjTranspose_swap_mul_twoReplicaLocalDiff` and the four
   pairing lemmas `trace_conjTranspose_{diff,swapDiff}_mul_{swapRaw,diff,swapDiff}` — the local
   Hilbert–Schmidt relations: `D_a` and `F D_a` are orthogonal to `span{I, F}` and to each other,
   and each has square `8`.
3. `edgeOutputLocal u v a b x` — the site-by-site output letter: `localDiffLetter (x u) a` at `u`,
   `localDiffLetter (x v) b` at `v`, and the original identity/swap letter elsewhere.
   `edgeOutput u v a b x` is `0` on endpoint-matched words and the negated sitewise tensor product
   otherwise.
4. `finiteTwoReplicaCollectiveCommutator_swapRaw_eq_edgeOutput` — **`(7)` on any register**: the
   fixed-orientation edge commutator takes every identity/swap word to `edgeOutput`.  Proved from
   the local swap relations already in the corpus, with no spectral input.
5. `trace_conjTranspose_edgeOutput_mul_edgeOutput_cross` — **`(11)` globally**: two edges whose
   vertex pairs differ produce Hilbert–Schmidt orthogonal outputs, because at a vertex of the
   symmetric difference one factor lies in `span{I, F}` and the other in its orthogonal complement.
6. `trace_conjTranspose_edgeOutput_mul_edgeOutput_of_ne_left` — the two mismatch types of one edge
   are orthogonal, because at the shared endpoint one factor is `D_a` and the other is `F D_a`.
7. `trace_conjTranspose_sum_mul_sum_eq_zero` — orthogonality passes to linear combinations.
8. `setEndpoints`, `edgeReader` — the endpoint-evaluation reader.  Fixing one matrix index pair at
   each endpoint where the corresponding difference letter is nonzero, and multiplying back the
   two identity/swap letters of the chosen mismatch type, produces a linear map that sends the
   edge output of a word of that type back to the word itself:
   `edgeReader_edgeOutput`.  This is the inverse of the fixed-orientation Pauli commutator on one
   mismatch fibre, and it is what makes the reverse inclusion of `(12)` available without any
   Gram-matrix computation on the non-orthogonal pair `{I, F}`.
9. `edgeCommutatorCoeff u v a b` — the fixed-orientation edge commutator as a linear map on
   identity/swap coefficients; `edgeCommutatorCoeff_eq_sum` expands it over words.
10. `edgeCommutatorCoeff_eq_zero_iff` — **`(12)` in both directions**:
    `A_{e,ab}(embed c) = 0 ↔ ∀ x, x u ≠ x v → c x = 0`.  The forward direction splits the
    coefficient vector into its two mismatch types (orthogonal by 6, hence each summand vanishes
    separately), applies the reader of 8 to each, and finishes with the corpus injectivity
    `finiteTwoReplicaSwapInvariantEmbed_injective`.  The reverse direction is
    `edgeCommutatorCoeff_eq_zero_of_matched`.

### The Hall inequality

11. `twoReplicaEdgeHallExpansion` — **the boxed `(4)`**.  For a finite family of edges whose vertex
    pairs are pairwise distinct, and any subspace `Ũ` of identity/swap coefficients whose only
    all-edge-matched vector is `0`,
    `dim Ũ ≤ dim (⨆_j map (A_{e_j,ab}) Ũ)`.
    The proof is exactly `(14)`–`(17)`: the single map `G = ∑_j A_{e_j,ab}` is injective on `Ũ`
    because cross-edge orthogonality forces every summand to vanish separately (5, 7), each
    summand's vanishing forces the mismatch coordinates of that edge to vanish (10), and the
    transversality hypothesis then forces `c = 0`.
12. `twoReplicaEdgeHallExpansion_connected` — the same statement on a connected interaction graph,
    where `(13)` (`twoReplicaGlobal_edgeMismatch_zero_iff`, already in the corpus) turns the
    all-edge-matched condition into membership in the global permutation line `𝒢₂`, so the
    hypothesis reads `Ũ ∩ 𝒢₂ = 0` exactly as in the card.

Only one fixed Pauli orientation `(a, b)` per graph is used, as the card claims.

## Verification

- `lake env lean` clean, no warnings, on all three modules.
- `lake build` green on all three.
- `#print axioms` on statements 1, 4, 5, 10, 11, 12 and on `edgeReader_edgeOutput`:
  `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella imports present in `GaloisForLFunctions/HTGeometry.lean`.

## What is *not* claimed

The card's own hostile audit lists the mixed-subspace gluing theorem (Hall for a subspace crossing
both the `𝒮₂/𝒢₂` and `𝒮₂^⊥` layers) and the higher-replica permutation-incidence theorem as open.
Those are separate statements, not part of `(4)`; nothing here asserts them.  No quantitative
operator-scaling condition number follows either — the theorem is rank nondecrease.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

# Prime Ising trees from the ferromagnetic cavity map

- **ID:** `prime-ising-tree-cavity-lee-yang`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE] [FORMALIZATION]`
- **Source:** Bethe--Peierls tree recursion, Lee--Yang ferromagnetism, and the existing `HTGeometry` Blaschke/Schur API
- **Statement:** For every finite rooted prime-labelled tree with normalized disagreement weights `0 <= c_e <= 1`, the exact Ising cavity recursion preserves the unit disk; after substituting the centered prime fields, every zero of the finite interacting tree partition has zero imaginary part.

## Goal

Extend the Lean corpus from products of independent or two-spin Lee--Yang blocks to an arbitrary-size genuinely interacting class.  The tree theorem must reuse the exact Schur/Blaschke identity already formalized in `HTGeometry`, specialize to the existing two-spin quadratic at one edge, specialize to the synchronized-cluster block at zero disagreement weight, and provide a finite prime-field consumer for the active ferromagnetic Ising route.  It does not construct the completed source comparison or prove that the source admits a compatible tree realization.

## Gates

- [x] 0 -> 1 in-progress: the cavity recurrence and disk invariant are exact; existing Blaschke infrastructure supplies the local inequality
- [x] 1 -> 2 fully-proven: complete finite-tree proof, `[PROVED HERE]`, no open finite dependency
- [x] 2 -> 3 formalized: Lean theorem names recorded, target build green, axiom audit and lint pass
- [ ] 3 -> 4 publication-ready: standalone statement, proof, physics provenance, Lean certificate, and downstream source comparison

## Candidate competition

1. **Asano contraction.**  It is the classical global stability mechanism, but the smallest contraction deletes the mixed coefficients and does not itself construct the source realization.
2. **Random-current switching.**  It derives correlation inequalities once an Ising representation exists, but does not solve inverse moment-cone membership.
3. **Tree cavity recursion.**  It produces an arbitrary-size interacting model now, directly generalizes the corpus's synchronized and two-spin blocks, and reduces every finite zero theorem to the existing Blaschke disk map.  This is the selected bridge.

## Exact identity and proof

For normalized disagreement weight `c in [0,1]`, the child-to-parent message transform is

`T_c(r) = (c + r) / (1 + c r)`.

It is the Blaschke factor with parameter `-c`.  Equivalently,

`normSq(1 + c r) - normSq(c + r) = (1 - c^2)(1 - normSq r)`.

Hence `norm r < 1` implies the denominator is nonzero and `norm(T_c(r)) <= 1`.  At a node with field `u_p`, the message is

`R = u_p * product_children T_(c_e)(R_child)`.

If every field lies in the open disk, then `norm R < 1`: the strict factor comes from `u_p`, while every transfer factor is contractive.  The recursively normalized amplitude is a product of nonzero child amplitudes and denominators `1 + c_e R_child`; therefore the full partition `A * (1 + R)` is nonzero.

For centered prime fields, `Im z < 0` puts every field inside the disk.  Global spin inversion gives the reciprocal identity

`Z_T(u) = (product_nodes u_p) * Z_T(u^{-1})`,

so the common exterior `Im z > 0` is reduced to the interior.  The resulting zero theorem forces `Im z = 0`.

## Lean certificate and consumers

`formal/GaloisForLFunctions/RHTower/PrimeIsingTreeCavity.lean` contains:

- `cavityTransfer_eq_blaschkeFactor` and `normSq_cavityTransfer_gap`;
- `norm_cavityTransfer_le_one`, using `GaloisForLFunctions.blaschke_schur` directly;
- `treeConditionalWeights_inside` and `treePartition_ne_zero_of_fields_inside` for arbitrary finite rooted trees;
- `treePartition_reciprocal`, the exact global spin-inversion identity;
- `treePartition_singleEdge_constantField`, identifying the one-edge model with `leeYangPairBlock`;
- `primeIsingTreePartition_singleEdge_eq_primeEulerFerromagneticBlock`;
- `primeIsingTreePartition_synchronizedPrimeChain_eq_cluster` for duplicate-free words; and
- `primeIsingTreePartition_independentPrimeChain_eq_independent`, identifying the `c=1`
  zero-interaction endpoint with the old independent-spin partition;
- `differentiable_primeIsingTreePartition` and `primeIsingTreePartition_zero_im`; and
- `riemannHypothesis_of_primeIsingTreePartition_tendstoLocallyUniformly_mul_XiC`, which discharges
  entireness and real-zero hypotheses and reduces the full route to a locally uniform source
  comparison with a zero-free entire factor.

The module is exported by `RHTower.lean` and consumed by
`prime-source-ferromagnetic-ising-lee-yang-limit-rh.md`.

The target build passes.  The axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound` for the principal identities, nonvanishing theorems, compatibility consumers, and
zero theorem.  The formal lint gate reports no proof debt.

## Physics provenance

- H. A. Bethe, *Statistical Theory of Superlattices*,
  <https://doi.org/10.1098/rspa.1935.0122>;
- T. D. Lee and C. N. Yang, *Statistical Theory of Equations of State and Phase Transitions. II.
  Lattice Gas and Ising Model*, <https://doi.org/10.1103/PhysRev.87.410>;
- K. de'Bell and M. L. Glasser, *The Ising model on a closed Cayley tree: Zeros of the partition
  function*, <https://doi.org/10.1016/0375-9601(84)90063-X>.

## Open core after this bridge

The completed Euler--Gamma/theta source has not been shown to select a cofinal family of these trees, and no zero-free normalization/comparison with `XiC` is known.  The tree theorem closes a finite interacting model class; it does not close the arithmetic inverse problem or the locally uniform completed-source limit.

## Log

- 2026-07-14 -- Created in `1-in-progress` after the cavity identity survived comparison with Asano contraction and random-current switching and was found to reuse the existing `HTGeometry` Blaschke theorem.
- 2026-07-14 -- Formalized the arbitrary-branching tree recursion, disk invariant, spin-inversion law, prime-field zero theorem, one-edge prime-Euler consumer, and synchronized-chain consumer; promoted to Stage 3 after target build, axiom audit, lint, and diff checks passed.
- 2026-07-14 -- Applied the tree theory back to the rest of the corpus: `c=1` recovers the existing independent prime partition, all tree partitions are entire, and the locally uniform `E * XiC` comparison now implies RH directly.

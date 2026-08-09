# Fixed observer-channel codimension law — formalized closure

- **ID:** `fixed-observer-channel-codimension-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./fixed-observer-channel-codimension-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [BRIDGE]`

## Lean modules

- `GaloisForLFunctions.HTGeometry.ObserverVisibleLocalTimeDimension`
- `GaloisForLFunctions.HTGeometry.FixedObserverBlockChannelCodimension`

Umbrella: `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

1. `QuantumAlg.observerChannel_subspace_finrank_le` — abstract inequality `(2)`:
   for a real-linear `T : V → W` and subspaces `U ≤ V`, `K ≤ W` with `T(U) ⊆ K`,
   `dim U ≤ dim (ker T) + dim K`.
2. `QuantumAlg.observerChannel_subspace_finrank_add_rank_le` — the rank form of `(2)`:
   `dim U + rank T ≤ dim V + dim K`.
3. `QuantumAlg.observerChannel_preimage_finrank_eq` — exact preimage formula `(3)`:
   `dim T⁻¹(K) = dim (ker T) + dim (K ⊓ range T)`.
4. `QuantumAlg.finrank_blockTangentChannel_add_one` — for a unit state `ψ` inside a complex
   block `B`, the projective tangent channel `B ⊓ ψ^⊥` has complex dimension `dim_ℂ B − 1`.
5. `QuantumAlg.finrank_real_blockTangentChannel_add_two` — its real dimension is
   `2 (dim_ℂ B − 1)`.
6. `QuantumAlg.centered_mem_blockTangentChannel` — every block-preserving Hamiltonian sends
   the state into that channel.
7. `QuantumAlg.finrank_blockPreserving_add_observerRank_le` — the quantum block consequence `(4)`:
   for a Hermitian dictionary of `M` generators, a unit state `ψ ∈ B`, and any real coefficient
   subspace `U` whose assembled Hamiltonians preserve `B`,
   `dim_ℝ U + rank_ℝ T_ψ + 2 ≤ M + 2 dim_ℂ B`.
8. `QuantumAlg.finrank_range_observerActionMap_eq_qfim_rank` — the observer rank in `(4)` is
   exactly the rank of the quantum Fisher information matrix.
9. `QuantumAlg.finrank_blockPreserving_add_qfim_rank_le` — the quantum Fisher form of `(4)`:
   `dim_ℝ U + rank (QFI) + 2 ≤ M + 2 dim_ℂ B`.

The bound is stated additively; it is the subtraction-free form of
`dim_ℝ U ≤ M − v_ψ + 2(d − 1)`, valid without a separate `d ≥ 1` side condition.

The Pauli specialization quoted on the paper card,
`v_ψ = 2 Σ_{k=1}^{q} C(n,k)`, is the corpus constant
`GaloisForLFunctions.HTGeometry.productInputObserverRank`.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/FixedObserverBlockChannelCodimension.lean` —
  clean, no warnings.
- `lake build GaloisForLFunctions.HTGeometry.FixedObserverBlockChannelCodimension` — green.
- `#print axioms` on statements 4–9: `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella import present in `GaloisForLFunctions/HTGeometry.lean`.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized: unconditional Lean theorems, umbrella wiring, axiom audit
- [ ] 3 → 4 publication-ready

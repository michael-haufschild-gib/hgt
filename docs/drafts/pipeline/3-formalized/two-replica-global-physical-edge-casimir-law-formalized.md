# Two-replica global physical edge-Casimir law — Lean certificate

- **ID:** `two-replica-global-physical-edge-casimir-law-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `two-replica-global-physical-edge-casimir-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Capstones

- `GaloisForLFunctions.HTGeometry.linearIndependent_finiteTwoReplicaSwapRaw` — the `2^{|V|}` swap
  words are linearly independent.
- `GaloisForLFunctions.HTGeometry.finiteTwoReplicaPhysicalEdgeCasimir_edgeExtension` — the global
  edge Casimir acts as the local four-coordinate edge operator tensored with the spectators, so the
  local model is not a surrogate.
- `GaloisForLFunctions.HTGeometry.finiteTwoReplicaPhysicalEdgeCasimir_intertwines_swapCoeff` —
  `K_{uv} ι(c) = ι(K^coeff_{uv} c)`.
- `GaloisForLFunctions.HTGeometry.finiteTwoReplicaPhysical_connectedGraph_kernel_iff` — the
  connected-graph common-kernel classification: the common kernel over the edges of a preconnected
  graph is the span of the global identity and the global replica swap.

Axiom audit: `[propext, Classical.choice, Quot.sound]`.

## What was already closed

`HTGeometry/TwoReplicaGlobalSingletEdgeCasimirBridge.lean` had everything the card's formal-status
section lists: arbitrary-register sitewise multiplication, the Möbius extractor and injectivity of
`ι`, edge-extension multiplication (`Ext(S,A) Ext(T,B) = Ext(ST,AB)`, the card's key identity),
weight-two support of all nine edge generators, the global/local Casimir equality, the
physical/coefficient intertwinement, and the connected-graph classification.

The displayed matrix

    K^coeff c = ( -32(c_01+c_10), 64c_01+16c_10, 16c_01+64c_10, -32(c_01+c_10) )

is `twoReplicaEdgeSwapCasimirCoeff` in `TwoReplicaLocalSingletSynchronization.lean`, entry for
entry, and its kernel statement is `twoReplicaEdgeSwapCasimirCoeff_eq_zero_iff`.  Note that the same
file also carries a *correlation*-basis model, `twoReplicaEdgeCasimirCoeff`, whose matrix is
different — `(0, 48c_01-48c_11, 48c_10-48c_11, -16c_01-16c_10+32c_11)`.  Both are correct; they are
related by `F = (I + C)/2`, and the card's matrix is the identity/swap one.

## What the assembly needed

The umbrella build, and the card's opening claim as a statement about the *family*:

`HTGeometry/SwapWordIndependence.lean` proves `linearIndependent_finiteTwoReplicaSwapRaw`.  The
corpus had injectivity of the coefficient embedding; the card asserts that the swap words are
linearly independent.  These are the same fact read through `Fintype.linearIndependent_iff`, and the
card's emphasis is right: no dimension count is used anywhere — the Möbius extractor recovers each
coefficient directly.

The same module records `span_range_finiteTwoReplicaSwapRaw`, identifying the span of the words with
the range of the embedding.  The card writes the sector as a span; the corpus states every singlet
theorem at the range, so the bridge is worth having explicitly.

## Not claimed

The card's own limitation stands: this is exact quadratic recovery on the two-replica singlet
sector, not the all-subspaces Hall inequality for the full mixed space, and it says nothing about
cavity decay, anti-concentration, complexity growth, plateau measure, or recurrence scale.

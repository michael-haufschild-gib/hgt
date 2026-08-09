# Positive graph edge-Casimir kernel law — Lean certificate

- **ID:** `positive-graph-edge-casimir-kernel-law-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `positive-graph-edge-casimir-kernel-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Capstones

- `GaloisForLFunctions.HTGeometry.finiteTwoReplicaPhysicalGraphCasimir_embed_eq_zero_iff` — the
  card's boxed equivalence: `K_G ι(c) = 0` iff `c = a δ_0 + b δ_1`, for any preconnected simple
  graph on a nonempty finite register.
- `GaloisForLFunctions.HTGeometry.finiteTwoReplicaPhysicalGraphCasimir_ker_inf_twirlRange` — the
  same statement as a submodule identity on the product-Clifford singlet sector, with
  `finrank_...` = 2.
- `GaloisForLFunctions.HTGeometry.finiteTwoReplicaPhysicalGraphCasimir_mem_qlocalShadow` — the
  card's "Moreover" clause: if `W` contains every first edge image of `s`, then `K_G s` lies in the
  one-step weight-at-most-`q` shadow of `W`, for every `q ≥ 2`.

Axiom audit: `[propext, Classical.choice, Quot.sound]`.

## What was already closed

`HTGeometry/TwoReplicaPositiveGraphEdgeCasimir.lean` had the whole argument:

- the matrix-to-Euclidean Hilbert equivalence and the Hilbert–Schmidt inner product identity;
- trace-cyclic self-adjointness of Hermitian commutators, hence of every collective Pauli
  commutator as a superoperator;
- the sum-of-squares energy identity `⟪X, K_G X⟫ = ∑ ‖A X‖²`, which is the card's `(1)` and the
  step its hostile audit flags as supplying "missing noncancellation";
- the connected singlet-sector kernel classification;
- `q`-local shadow containment;
- `ker K_G ⊓ range ι = span{global identity, global swap}`.

The card's own formal-status section listed these and left only the umbrella build.

## What the assembly needed

The umbrella build, and two statements the card asserts but the corpus did not carry, both in
`HTGeometry/GraphEdgeCasimirSingletKernelRank.lean`:

1. **"Exactly two universal zero modes."**  The corpus identified the kernel with the *range* of the
   synchronized coefficient map; it did not say that range is two-dimensional.  It is, on a nonempty
   register: `finiteTwoReplicaGlobalSynchronizedMap_injective` reduces to injectivity of the
   coefficient embedding together with `twoReplicaAllIdentity ≠ twoReplicaAllSwap`, so
   `finrank_finiteTwoReplicaGlobalSynchronizedSubmodule = 2`.  Nothing about the Casimir enters — the
   two modes are independent for register reasons alone.  This is what "after removing its two
   universal zero modes" quantifies, and it is why nonemptiness is a hypothesis: on the empty
   register the two words coincide and the sector is one-dimensional.

2. **The singlet sector under its own name.**  The card says "on the complete product-Clifford
   singlet sector"; the corpus stated the classification at the swap-word range.  These agree by
   `finiteProductCliffordTwoReplicaTwirl_range_eq` (the global twirl-range law), so
   `finiteTwoReplicaPhysicalGraphCasimir_ker_inf_twirlRange` records the card's phrasing directly.

## Not claimed

The card's hostile audit is respected: the kernel classification is on the singlet sector only, not
on the full matrix space; and the quotient/complement implementation that turns `K_G` into an
injective recovery map is deferred to the parent card, `visible-kernel-recovery-hall-law`.

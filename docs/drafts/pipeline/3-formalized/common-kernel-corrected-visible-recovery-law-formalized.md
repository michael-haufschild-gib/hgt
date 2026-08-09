# Common-kernel-corrected visible recovery law — Lean certificate

- **ID:** `common-kernel-corrected-visible-recovery-law-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `common-kernel-corrected-visible-recovery-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Capstones

- `GaloisForLFunctions.HTGeometry.visibleKernelRecovery_subspace_finrank_with_kernel` — the card's
  `(1)`: injectivity of the recovery map is not required; the defect is exactly `dim ker R`.
- `GaloisForLFunctions.HTGeometry.visibleKernelRecovery_subspace_finrank_mod_commonKernel` — the
  card's `(2)`, the intrinsic form.
- `GaloisForLFunctions.HTGeometry.finiteTwoReplica_graphVisibleRecovery_finrank_mod_synchronized` —
  the card's `(3)`, the physical connected-graph instance for every `q ≥ 2`.
- `GaloisForLFunctions.HTGeometry.finiteTwoReplica_graphVisibleRecovery_finrank_le_shadow_add_two` —
  `(3)` with the correction replaced by the constant `2`.

Axiom audit: `[propext, Classical.choice, Quot.sound]`.

## What was already closed

Both abstract statements and the physical instantiation.  The abstract proof is the card's: layer
disjointness makes the output sum direct, and two applications of rank–nullity — to `F` and then to
`R` — turn the visible-rank hypothesis into `(1)`.  The forgetful map `ker R → U_S ∩ N` gives `(2)`.

The physical recovery map is the connected graph edge Casimir restricted to detector-kernel
directions.  Two facts from the graph-Casimir layer make it usable: its kernel on the singlet sector
is the span of the global identity and global swap, and its output is literal one-step `q`-local
Pauli output.

## What the assembly needed

The umbrella build, and the card's headline reading made exact.

The card says "the physical singlet recovery mechanism loses no dimension beyond the two universal
modes".  In the corpus the correction term was `dim(U_S ⊓ N)` — a subspace dimension, with nothing
pinning its size.  `HTGeometry/GraphVisibleRecoveryTwoModeCorrection.lean` supplies the bound:

- `finrank_inf_globalSynchronized_le_two` — the correction is at most `2` for *any* source, since
  `N` is two-dimensional on a nonempty register (`positive-graph-edge-casimir-kernel-law`);
- `finiteTwoReplica_graphVisibleRecovery_finrank_le_shadow_add_two` — `(3)` with that constant.

The distinction matters for the card's own claim: an absolute constant independent of the register
is what makes "unreduced all-subspaces Hall is false, but Hall modulo two modes holds" a usable
statement rather than a bookkeeping identity.

## Premise status

`(3)` carries visible-rank, hidden-image, and `U_W`-reproduction premises.  All three are supplied
for the canonical product-Clifford decomposition — the reproduction premise by the one-site
quadratic return in `HTGeometry/TwoReplicaSingleSiteZeroTwirlRecovery.lean` — giving the
unconditional inequality recorded on `visible-kernel-recovery-hall-law-formalized.md`.

The safety property the card notes is unaffected: if the recovery map had zero modes outside `N`,
the hypothesis would simply fail and the theorem would draw no false Hall conclusion.

## Not claimed

Nothing about anti-concentration, complexity growth, plateau, or recurrence follows from these
dimension counts.

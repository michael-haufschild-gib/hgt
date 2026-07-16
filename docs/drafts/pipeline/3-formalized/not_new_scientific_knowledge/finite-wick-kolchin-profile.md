# Finite Wick-reduced Kolchin profile

- **ID:** `finite-wick-kolchin-profile`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / INFRASTRUCTURE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source:** `docs/drafts/pipeline/1-in-progress/wick-kolchin-interaction-spectrum.md`
- **Statement:** Finite connected-sector jet packets define a transcendence-rank profile whose
  excess above chosen Gaussian sectors is zero whenever every higher connected sector vanishes;
  both the total and reduced ranks are invariant under injective base-field algebra embeddings.
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`

## Goal

Install the exact algebraic negative control required by the Wick--Kolchin interaction program.
The result prevents a hypertranscendental two-point response from being counted as interaction
when all connected higher-point sectors vanish.

## Gates

- [x] 0 -> 1 in-progress: finite packet and Gaussian baseline are explicit
- [x] 1 -> 2 fully-proven: finite-rank proof uses algebraic-matroid monotonicity and injectivity
- [x] 2 -> 3 formalized: exact module build and axiom audit pass
- [ ] 3 -> 4 publication-ready: not a standalone result; infrastructure for the open QFT theorem

## Formal statement

The module
`formal/GaloisForLFunctions/HTGeometry/WickKolchinProfile.lean` defines:

```text
connectedJetPacket
finiteConnectedKolchinRank
finiteWickReducedKolchinRank
```

and proves:

```text
finiteConnectedKolchinRank_gaussian_add_wickReduced
connectedJetPacket_eq_of_vanishes_off_gaussian
finiteWickReducedKolchinRank_eq_zero_of_vanishes_off_gaussian
transcendenceRank_image_algHom
finiteConnectedKolchinRank_map_algHom
finiteWickReducedKolchinRank_map_algHom
```

The negative-control theorem assumes that all sectors outside the designated Gaussian family
vanish.  Erasing zero then makes the full and Gaussian finite jet packets equal, so their
transcendence ranks agree and the natural-number excess is zero.

For ambient-field invariance, an injective base-field algebra homomorphism preserves algebraic
independence.  The algebraic matroid in the target field therefore pulls back to the source
matroid, preserving the rank of every finite packet and hence the Wick-reduced difference.

## Exact boundary

This file does not define connected Wightman distributions, source probes, renormalization
schemes, or an asymptotic Kolchin polynomial.  It formalizes the finite algebraic skeleton only.
The new scientific core remains a probe- and scheme-invariant directed profile together with a
positive theorem for a rigorous interacting continuum QFT.

## Verification

- `lake build +GaloisForLFunctions.HTGeometry.WickKolchinProfile` -- PASS
- direct touched-file `lake env lean` -- PASS
- axiom audit of all capstone theorems -- only `propext`, `Classical.choice`, and `Quot.sound`

## Novelty gate

Finite transcendence rank, algebraic matroids, Gaussian connected-sector vanishing, and rank
invariance under embeddings are parent mathematics.  Their assembly here is necessary corpus
infrastructure, not a novelty claim.

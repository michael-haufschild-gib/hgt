# Universal-law-field Stage-2 → Stage-3 sweep (2026-08-09)

Working rule: take the **oldest card by mtime** in
`docs/drafts/pipeline/2-fully-proven/universal-law-field/`, formalize it unconditionally, then
`git mv` it to `3-formalized/universal-law-field/`, write a `-formalized.md` companion, add a row to
`2-fully-proven/universal-law-field/_LEAN-CERTIFICATION.md`, and append to
`docs/drafts/pipeline/_stage2-to-3-ledger.md`. All modules go into
`HTGeometry.UniversalLawField`.

## Certified so far (10 cards)

| ID | Lean module |
|---|---|
| ULF-CTX-1 | `HTGeometry.ConstitutiveParityContextuality` |
| ULF-IRR-1 | `HTGeometry.ConstitutiveIrreducibleInteraction` |
| ULF-TORS-1 | `HTGeometry.ConstitutiveDeterminantTorsion` |
| ULF-FILL-1 | `HTGeometry.ConstitutiveQuadraticFilling` |
| ULF-DOCT-1 | `HTGeometry.ConstitutiveDoctrineLattice` |
| ULF-ENDP-1 | `HTGeometry.ConstitutiveEndpointInsufficiency` |
| ULF-BULK-1 | `HTGeometry.ConstitutiveBulkBoundaryFusion` |
| ULF-MATCH-1 | `HTGeometry.ConstitutivePolyscopicMatching` |
| ULF-DGLU-1 | `HTGeometry.ConstitutiveDeterminantGluing` |
| ULF-FLUX-1 | `HTGeometry.ConstitutiveAbelianDeterminantFlux` |

`#print axioms` clean on every capstone (propext / Classical.choice / Quot.sound only).

## Reuse graph — READ THESE BEFORE STARTING A NEW CARD

Many remaining cards are corollaries or variants of the ten above.
- Parity/incidence over F₂: `ConstitutiveParityContextuality` (boundary `parityBoundary`, criterion,
  proper-face solvability, rank `|V|-1`, halving principle for counting).
- Oriented multiplicative version over any abelian `A`: `ConstitutiveAbelianDeterminantFlux`
  (`fluxBoundary`, `totalFlux`, exact sequence, torsor, proper-face, coefficient quotient).
  Sign specialization: `ConstitutiveDeterminantGluing` (`paritySign`, cycle-memory count).
- Based two-term complexes / determinant history / winding: `ConstitutiveDeterminantTorsion`.
- Minimal L∞ law, colour faces, arity truncation: `ConstitutiveIrreducibleInteraction`.
- Van Kampen area / Heisenberg / reduced words: `ConstitutiveQuadraticFilling`.
- Matching-map phases and diagrams: `ConstitutivePolyscopicMatching`.

## Findings / corrections

- **ULF-MATCH-1 §4.1 corrected.** The parity Čech diagram over the *subset poset* is
  reconstructible, not contextual: the poset of proper subsets contains the maximal faces `V\{v}`,
  and compatibility across two of them already forces every context equation. Contextual phase is
  certified instead by taking a proper face's shadow to be its satisfiability. Watch for the same
  over-claim elsewhere.
- **ULF-FLUX-1 scope.** `ker ∂_A ≅ A^{β₁}` (needs a spanning-tree cycle basis, absent from mathlib)
  is not certified; the torsor statement is, and the numeric β₁ count is certified over F₂ in
  ULF-DGLU-1.
- Infinity-categorical content (ULF-MATCH-1 Cor 2.4) is out of scope; the 0-truncated chart is
  certified.

## Standing environment notes

- The formal lint gate intermittently reports "owned module unreachable"/"stale generated file" for
  modules a **concurrent agent** is mid-editing (ConstraintRelativity, ConstraintFrameRelativity,
  DerivedSelectionGeometry, RHTower Eigen*). Re-run `formal_tools.py index` then `lint`; do not
  chase them.
- Next card in the queue (oldest remaining):
  `even-moore-law-cell-effectivity-memory-and-positive-topology-collapse-law.md`.

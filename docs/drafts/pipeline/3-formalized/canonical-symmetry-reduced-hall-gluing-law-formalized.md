# Canonical symmetry-reduced Hall gluing law — Lean certificate

- **ID:** `canonical-symmetry-reduced-hall-gluing-law-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `canonical-symmetry-reduced-hall-gluing-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Capstones

- `GaloisForLFunctions.HTGeometry.linearFamilyDefect_supermodular` — deficiency is supermodular on
  the subspace lattice.
- `GaloisForLFunctions.HTGeometry.linearFamilyGreatestMaximizer` with
  `eq_linearFamilyGreatestMaximizer` — the unique largest maximum-defect subspace, as a term.
- `GaloisForLFunctions.HTGeometry.linearFamilyHall_iff_greatestMaximizer_defect_eq_zero` — the
  all-subspaces Hall condition is one scalar equation.
- `GaloisForLFunctions.HTGeometry.linearFamilyGreatestMaximizer_map_eq_of_spanCovariant` — it is
  fixed by every span-preserving symmetry, including continuous mixing of the generators.
- `GaloisForLFunctions.HTGeometry.bipartiteHall_overlapCompensation_finrank` — the gluing law.

Axiom audit: `[propext, Classical.choice, Quot.sound]`.

## What was already closed

`LinearFamilyDefectSupermodularity.lean` had supermodularity, existence and uniqueness of the
greatest maximizer, the one-equation Hall criterion, and all three covariance statements.
`BipartiteHallGluing.lean` had the overlap-compensated mixed-layer rank theorem.

The supermodularity proof is the card's: `F(U+V) = F(U)+F(V)` and `F(U∩V) ⊆ F(U)∩F(V)` with rank
modularity.  Uniqueness then follows exactly as described — both `U+V` and `U∩V` are maximizers, and
maximal dimension forces `V ⊆ U`.

## What the assembly needed

The card's headline is an assertion about *the* largest maximum-defect subspace.  The corpus proved
it exists and is unique but never named it, so all three invariance statements were phrased as
"if `U` is greatest, then `g U = U`".

`HTGeometry/LinearFamilyGreatestMaximizer.lean` names it and restates them with the premise
discharged:

- `linearFamilyGreatestMaximizer_map_eq_of_invariant`;
- `linearFamilyGreatestMaximizer_map_eq_of_covariant`;
- `linearFamilyGreatestMaximizer_map_eq_of_spanCovariant`.

The third is the one the card singles out — "This covers continuous mixing of Pauli generators, not
only permutations" — and it is the only one needing a field rather than a division ring.

## Surviving frontier, updated

The card's frontier names two concrete tasks: the product-Clifford reducing decomposition of the
canonical maximizer, and the graded visible quotient detector.  Both are closed —
`global-product-clifford-twirl-range-law` and `aggregate-pauli-visible-quotient-detector-law` — and
their assembly into a Hall inequality for the canonical obstruction is
`visible-kernel-recovery-hall-law`.

The card's gate 3 → 4 is untouched: publication readiness still waits on the concrete local-Pauli
span covariance and reverse-overlap hypotheses in their own terms.

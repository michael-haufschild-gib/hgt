# One-ninth overlap throughout edge and Hodge theory

- **ID:** one-ninth-exponent-through-edge-and-hodge-theory
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/review-0111/obstacles-summary.md`, A4.
- **Statement:** Replace the obsolete `α<1/59` restriction by `α<1/9` in
  the tilted-spline edge, crossing, width threshold, limit-floor, star-positivity,
  and gluing results; use the same stronger base regime for Liouville transport.

## Proof [PROVED HERE]

The unconditional complete-matrix positivity and spectral-floor theorems below
`1/9` supply exactly the inputs previously taken from the `1/59` theorem.
An initial interval of positive forms bounds the first-failure edge from below.
Continuity gives a zero mode at a finite first failure. The width conversion
uses `N=ceil((log(1/w))^α/(2w))`. Star embedding preserves the complete energy
at the lower horizon. The conductor limit and RH receivers are unchanged.
The Liouville transport starts at overlap one, certified by exponent `1/10`.

## Lean

Direct audits passed for all seven updated leaves:

- `EdgeHodgeTheory/TheEdgeOfTheCompleteWeilFamily.lean`: lower edge, divergence, and edge window.
- `EdgeHodgeTheory/TheEdgeIsACrossing.lean`: zero mode at the first failure.
- `EdgeHodgeTheory/TheEdgeIsWhereTheWindowOpens.lean`: width-coordinate threshold.
- `EdgeHodgeTheory/TheLimitStructure.lean`: inherited polynomial floor.
- `HodgeTheoryWithoutVarieties/StarsOfTheCompleteWeilFamily.lean`: star positivity.
- `HodgeTheoryWithoutVarieties/TheLefschetzCandidates.lean`: gluing failure with positive deep stars.
- `HodgeTheoryWithoutVarieties/TheLiouvilleProperty.lean`: Liouville transport from overlap one.

The audited capstones use only `propext`, `Classical.choice`, and `Quot.sound`.
Existing umbrellas include every leaf. The stronger edge inputs are supplied by
the audited `EdgeHodgeTheory/EdgeBelowOneNinth.lean`.

## Gates

- [x] Dependency-closed paper proof using the formalized one-ninth floor.
- [x] Updated source statements, direct leaf checks, and transitive axiom audits.

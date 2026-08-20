# The G–U structure/admission split law — Lean certification

- **ID:** ULF-MECH-4
- **Lean module:** `GaloisForLFunctions.HTGeometry.GUStructureAdmissionSplit` (new)
- **Status:** `[LEAN-CERTIFIED (clause ii)] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS]`

## What is certified, and what is cited

The card's Law has two clauses.

**Clause (i)** — the two structural halves are equivalent presentations under the classical
Krein/de Branges correspondence — is *cited classical mathematics* (Krein; de Branges; Akhiezer),
as the card itself states ("(i) is the classical correspondence … no arithmetic content is
claimed").  It is not restated as a Lean theorem: the correspondence is a body of classical theory
absent from mathlib, and the card asserts it as a citation rather than proving it.

**Clause (ii)** — the new content — is the non-transport statement, and it is now certified
unconditionally.

| Card content | Lean |
|---|---|
| "admission is not a function of the structural data" | `DeterminedBy`, `not_determinedBy_of_witness` |
| "no functor along the structural correspondence can transport it" | `not_transports_of_not_determinedBy` |
| "structurally admissible data fails route admission" | `not_structure_implies_admission` |
| **U-side witness** — the current Hankel face leaves the first extension class free | `crossingSign_not_determinedBy_hankelFace`, built on `HTGeometry.exists_momentSequence_same_face_monicRemainder_eq` |
| **U-side port orientation** — the Christoffel forward/backward imbalance is likewise free | `portOrientation_not_determinedBy_hankelFace`, built on `HTGeometry.exists_momentSequence_same_face_christoffelPortDifference_eq` |
| **G-side witness** — one-angle holomorphically gauged entire limits are impossible | `gaugeStructure_does_not_give_routeAdmission` = `RHTower.not_suzukiHolomorphicGaugeCharacteristicLimitWall` |
| the split law itself | `guStructureAdmissionSplit_capstone` |

The capstone quantifies over **every** transported structure type `S'` and **every** transport map
`e`, which is exactly the card's "any claimed G-to-U (or U-to-G) transfer that does not explicitly
transport admission data is pre-refuted".

## Verification (2026-08-20)

The module elaborates from the tree with 0 errors; all 7 public declarations report only `propext`,
`Classical.choice`, `Quot.sound`.  It is imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

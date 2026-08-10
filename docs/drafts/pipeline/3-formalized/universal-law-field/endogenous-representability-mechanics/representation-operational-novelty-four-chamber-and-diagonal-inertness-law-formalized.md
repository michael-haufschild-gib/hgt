# Representation--execution exchange -- Lean certification

- **ID:** ULF-REE-1
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/endogenous-representability-mechanics/representation-operational-novelty-four-chamber-and-diagonal-inertness-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveRepresentationExecutionExchange`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [MECHANISM NOT OBJECT]
  [FOUR CHAMBERS] [DIAGONAL FEEDBACK NO-GO] [NOT RH]

## Certified mechanism

The formalization separates two logically independent grades of law birth:

- `ReporterRepresented E c`: challenge `c` is already one evaluator row;
- `ReporterOperationallyEffective E c`: `c` fails to descend through complete row semantics.

`operationallyEffective_iff_fibre_split` proves that effectiveness is exactly separation of two
states in one row-profile fibre. `operationallyEffective_iff_invisible_intervention` proves the
equivalent execution law: adjoining the challenge excludes an intervention which preserved every
old row profile.

`antiDiagonal_operationallyEffective_iff` classifies the anti-diagonal: it is effective exactly
when equal rows have unequal diagonal values. `antiDiagonal_not_represented` retains the exact
diagonal nonrepresentation theorem while separating it from semantic novelty.

`four_representation_execution_chambers` realizes all four combinations on two-state evaluators.
The projection evaluator supplies represented/effective and unrepresented/effective challenges;
the strict-order evaluator supplies represented/inert and unrepresented/inert challenges.

`finiteDiagonal_unrepresented_inert_no_contraction` proves for every finite strict-order stage that
the row profile is injective, the anti-diagonal is absent, the anti-diagonal is nevertheless
operationally inert, and adjoining it cannot contract the invisible-intervention doctrine.
`representationExecutionExchange_closed` combines the four chambers and the entire finite tower in
one unconditional theorem.

## Verification

Foreground verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveRepresentationExecutionExchange.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveRepresentationExecutionExchange
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Leaf build completes 8,666 jobs. Umbrella build completes 11,582 jobs. Axiom prints on the two
exchange criteria, anti-diagonal classification, four-chamber theorem, finite-stage theorem, and
closed capstone report exactly `propext`, `Classical.choice`, and `Quot.sound`. The module contains
no computation certificate, `sorry`, `admit`, project axiom, `opaque`, or `unsafe` declaration.

## Field boundary

This certifies a route-independent exchange law, not the recursive field dynamics. A complete
feedback theorem must still show how an operational contraction changes legal execution and
source-generates the next challenge. Representer birth alone cannot close that cycle.

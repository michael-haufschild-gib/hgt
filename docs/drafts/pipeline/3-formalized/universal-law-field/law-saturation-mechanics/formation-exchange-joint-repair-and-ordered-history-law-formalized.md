# Formation exchange and joint repair — Lean certification

- **ID:** ULF-LSM-3
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveFormationExchange`
- **Source:**
  `formal/GaloisForLFunctions/HTGeometry/ConstitutiveFormationExchange.lean`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

- `ConstitutiveFormation` — extensive, monotone, idempotent law formation;
- `constitutiveJointRepair_contains`;
- `constitutiveJointRepair_fixed`;
- `constitutiveJointRepair_least`;
- `everyFormationSchedule_below_jointRepair`;
- `commutingFormations_jointRepair`;
- `commutingFormations_orderIndependent`;
- `formations_commute_iff_twoOrders_are_jointRepair`;
- `failedExchange_is_orderedHistory`;
- `pairwiseCommutingThree_jointRepair`;
- `pairwiseCommutingThree_noScheduleDefect`;
- `constitutiveFormationExchangeMechanism_closed`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveFormationExchange.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveFormationExchange
```

Both passed in foreground. `#print axioms` on fixedness, schedule boundedness, exchange equivalence,
failed exchange, and the capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, project axiom, opaque theorem, unsafe declaration, or computation proof occurs.

## Field consequence

This is the exact strict-formation mechanism law. Commutation is equivalent to lossless order
exchange; noncommutation is ordered formation history; joint repair remains canonical independently
of schedule. Pairwise commuting triples have no schedule defect. The next field gate therefore
requires weak/noninvertible exchange, partial admission, extension carry, or non-idempotent history.

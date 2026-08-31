# Locally bounded carry properness, compact recurrence, and character selection -- Lean certification

- **Paper theorem:** ULF-TAFM-9
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.CompactAddGroupMetricReturnLaw` and
  `GaloisForLFunctions.HTGeometry.TopologicallyAdmittedCarryPropernessSelection`
- **Status:** formalized

## Certified content

The modules prove:

1. finite-cover positive return for natural multiples in a translation-invariant additive
   extended pseudometric group;
2. compact covering-number return;
3. cofinally large return times in one fixed phase ball;
4. a real additive character locally bounded through compact phase is zero, without continuity or
   dense image;
5. exact linear current lower bound on carry traffic under natural multiplication;
6. abstract local-traffic selection and cofinal-return blow-up;
7. a bundled compensated-lift fibre with its own measurable carrier, invariant probability law,
   observer, integrable potential, and integrable carry;
8. current domination by absolute `L¹` carry traffic from exact invariant recovery; and
9. adaptive-fibre selection and cofinal linear traffic blow-up when every source element chooses a
   separate fibre.

No Xi zero, RH hypothesis, divisor-fitted gauge, continuity premise, density premise, or common
potential occurs.

## Verification

- Scratch elaboration of additive recurrence and selection kernels -- pass.
- Project-path elaboration of both modules -- pass.
- Missing dependency `.olean` built only for the additive recurrence leaf.
- Final targeted selection leaf audit -- pass (`8703/8703`).
- Batched scratch `#print axioms` audit on ten significant declarations reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Both modules are imported by `HTGeometry.UniversalLawField`; umbrella is not built.

No full project, theorem-area, or umbrella build is run.

## Selection boundary

This strictly weakens the former source obligation. Componentwise zero carry or one global
integrable potential is unnecessary. It is enough to derive one uniform `L¹` traffic ceiling for
all source words whose compact phase lies in a fixed identity ball. Off-neutrality then predicts
linear traffic divergence on cofinally large near-identity words. Establishing that ceiling from
the literal divisor-independent prime/theta formation law remains the RH-bearing producer.

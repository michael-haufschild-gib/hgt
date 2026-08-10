# Mutational visible recurrence, open lineage, and conserved linearization -- Lean certification

- **ID:** ULF-SEGM-1
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/structured-endogenous-genesis-mechanics/mutational-visible-recurrence-open-lineage-and-conserved-linearization-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveMutationalGenesis`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [STRUCTURED ENDOGENOUS GENESIS]
  [CLASSICAL CLUSTER CALIBRATION] [NOT RH]

## Certified declarations

- `mutationalLineage`, its initial values, and `mutationalLineage_recurrence`;
- `mutationalLineage_cassini` and `mutationalLineage_exchange`;
- `mutationalLineage_certificate` and `mutationalCertificate_transport`;
- `mutationalExchange_certificate_forces_linearization`;
- `mutationalLineage_positive_increasing`, `mutationalLineage_more_than_double`, and
  `mutationalLineage_strictMono`;
- `mutationalLineage_index_lower` and `mutationalLineage_unbounded_witness`;
- `mutationalLineage_has_no_positive_period`;
- `visibleMutationRule_succ`, `visibleMutationRule_period_two`, and
  `visibleMutationRule_not_period_one`;
- `constitutiveMutationalGenesisMechanism_closed`.

## Exact content

The local nonlinear exchange

```text
x (n+2) * x n = x (n+1)^2 + 1
```

and the denominator-free certificate

```text
x n^2 + x (n+1)^2 + 1 = 3 * x n * x (n+1)
```

are both certified from the integer recurrence `x (n+2)=3*x (n+1)-x n`. Conversely, a local
exchange triple carrying certificate value three has the forced linear successor whenever its
first entry is nonzero. Thus linearization is a theorem, not a second fitted dynamics.

The semantic lineage is positive, strictly increasing, more than doubles after the first mutation,
crosses every natural threshold, and has no positive period. The visible compatibility sign
reverses each step and has exact period two. Lean therefore certifies recurrent observed rulebook
plus open, source-predicted semantic lineage in one fixed process.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveMutationalGenesis.lean
scripts/formal_tools.py lint
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

The final umbrella build passes `11,433` jobs. `/tmp` axiom audit on all load-bearing declarations
reports only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, custom `axiom`,
`opaque`, `unsafe`, or numerical certificate is used.

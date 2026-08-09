# Alternating unary-law saturation horizon — Lean certification

- **ID:** ULF-LSM-1
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/law-saturation-mechanics/alternating-unary-law-saturation-horizon-and-finite-observer-stabilization-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveLawSaturation`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified mechanism

`ObserverRel` is the explicit family of bit-forgetting observer equivalences. `evenLaw` and
`oddLaw` are source operations. `evenRepair` and `oddRepair` are their forced distinction closures.

Theorems `evenLaw_preserves_iff` and `oddLaw_preserves_iff` prove executable descent exactly: a
source law preserves an observer equivalence iff its repair closure is fixed. Theorems
`evenRepair_least` and `oddRepair_least` prove universal minimality of the repair.

The capstone `lawSaturationMechanism_closed` bundles:

- idempotence of both repairs;
- exact source-law preservation criteria;
- least executable repair;
- noncommutation at the initial observer;
- \(r\)-sweep state \(P_{2r}\);
- failure of every finite stage to be common-fixed;
- uniqueness of the common fixed point above level zero;
- exact coordinate-reporter stabilization;
- strict global history;
- exact directed repair depth: level $j$ is reachable by a word of length $j$, and every word
  reaching it has length at least $j$.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveLawSaturation.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveLawSaturation
lake env lean /tmp/ConstitutiveLawSaturationAxioms.lean
../scripts/formal_tools.py lint --check-generated
```

All checks passed. Axiom output for the capstone contains only Lean/mathlib foundations `propext`,
`Classical.choice`, and `Quot.sound`. No project axiom, theorem premise, `sorry`, `admit`, `opaque`,
`unsafe`, or computation certificate is used.

## Exact field consequence

Operation admission can generate an ordered, unbounded repair history even when each primitive
repair is idempotent and every finite reporter stabilizes. This is a certified mechanism-level
calibration, not a route result and not a proof of whole-corpus universality.

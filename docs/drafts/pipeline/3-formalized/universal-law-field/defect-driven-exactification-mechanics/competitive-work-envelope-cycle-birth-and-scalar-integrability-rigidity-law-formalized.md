# Competitive work envelope and selection-induced history -- Lean certification

- **ID:** ULF-DDE-2A
- **Stage:** 3-formalized
- **Paper source:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/defect-driven-exactification-mechanics/competitive-work-envelope-cycle-birth-and-scalar-integrability-rigidity-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveCompetitiveWorkHistory`
- **Status:** [LEAN-PROVED] [UMBRELLA-WIRED] [NO SORRY] [NO ADDED AXIOMS]

## Certified declarations

- `constitutiveExactWork_reverse`;
- `constitutiveExactWork_add_const`;
- `constitutiveExactWork_dominance_rigidity`;
- `constitutiveStrengthening_scalarIntegrable_iff_eq`;
- `constitutiveConjunctiveWork_twoCycle`;
- `constitutiveConjunctiveWork_positive_twoCycle`;
- `constitutiveConjunctiveWork_scalarIntegrable_iff`;
- `constitutiveConjunctiveWork_not_scalarIntegrable`;
- `constitutiveExactWork_eq_iff_gaugeAt`;
- `constitutiveConjunctiveWork_scalarIntegrable_iff_gaugeAt`;
- `constitutiveDisjunctiveWork_scalarIntegrable_left`;
- `constitutiveDisjunctiveWork_scalarIntegrable_right`;
- `constitutiveMandatorySelectionCreatesHistory_iff`.

## Verification

- direct source elaboration passed;
- final foreground umbrella build
  `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` passed 11,417 jobs;
- forbidden-token scan found no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or
  `native_decide`;
- `#print axioms` on all capstones reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Certified field law

For arbitrary state type, mandatory pointwise composition of two scalar-exact directed work laws
is scalar-integrable exactly when their potentials differ by one additive gauge constant. Every
disagreement produces a strictly positive two-step cycle. Permissive pointwise minimum remains
scalar-integrable. The theorem formally certifies a mechanism by which selection among exact laws
creates directed history.

## Scope

Lean proves algebraic mechanism. It does not assert a minimal-memory lift, decide which composition
rule is legal in an application, construct source responses, or imply RH.

## Log

- 2026-08-09 -- theorem translated exactly; direct, umbrella, forbidden-token, and axiom audits
  passed.

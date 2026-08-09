# Exact polarity revision collapse -- Lean certification

- **ID:** ULF-RLM-12
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/exact-polarity-revision-collapse-and-endogenous-genesis-boundary-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutivePolarityRevision`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [MECHANISM BOUNDARY] [NOT RH]

## Certified declarations

- `constitutiveRulePolar`, `constitutiveTestPolar`;
- `constitutiveRulePolar_antitone`, `constitutiveTestPolar_antitone`;
- `constitutiveRuleClosure`, `constitutiveTestClosure`;
- `constitutiveRuleClosure_extensive`, `constitutiveTestClosure_extensive`;
- `constitutiveRulePolar_ruleClosure`, `constitutiveTestPolar_testClosure`;
- `constitutiveRuleClosure_idempotent`, `constitutiveTestClosure_idempotent`;
- `constitutiveSerialRevision`, `constitutiveParallelRevision`;
- `constitutiveSerialRevision_idempotent`;
- `constitutiveParallelRevision_sq`, `constitutiveParallelRevision_cube`;
- `constitutiveParallelRevision_fixed_iff`;
- `constitutiveExactPolarityRevisionMechanism_closed`.

## Exact content

Lean proves that the two polars induced by any fixed compatibility relation are antitone, their
double polars are extensive and idempotent, and triple polarity collapses. Exact serial mutual
revision is idempotent. Exact synchronous revision satisfies `P^2=(c_X,c_Y)` and `P^3=P`; every
post-first state is therefore fixed or two-periodic. Fixed states are exactly mutually polar
rule--test concepts.

This closes the mechanism no-go: fixed exact Pol--Inv feedback cannot generate open law history.
Any prolonged Reflexive Law Mechanics model must change compatibility, admission, resource horizon,
transport, or retained lineage.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutivePolarityRevision.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Final umbrella build completed 11,410 jobs. The axiom audit on significant declarations and the
closed capstone reports only `propext` and `Quot.sound`. No `sorry`, `admit`, new axiom, `opaque`,
`unsafe`, `native_decide`, or computational certificate is used.

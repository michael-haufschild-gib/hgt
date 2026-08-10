# Terminating execution, open conservative completion, and critical heredity law

- **ID:** ULF-ECMPL-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-certified)
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveCriticalCompletionMechanics`
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/endogenous-completion-mechanics/terminating-execution-open-conservative-completion-and-critical-heredity-law.md`

## Certified mechanism

For the rules `a b^n a -> b^n a`, finite stage `N>=1` satisfies simultaneously:

1. every rewrite decreases the number of `a` letters by exactly one;
2. execution is well-founded;
3. the marked overlap reaches distinct normal forms `a b^(N+1) a` and `b^(N+1) a`;
4. the stage is nonconfluent;
5. the missing rule is semantically generated at the old stage;
6. adjoining it leaves generated equivalence unchanged;
7. the rule is strictly absent before repair and present after repair;
8. the repaired stage inherits the next nonconfluence witness.

Capstone declaration:
`ConstitutiveCriticalCompletionMechanics.endogenous_completion_mechanism`.

## Audit

- direct leaf elaboration: passed;
- `UniversalLawField` umbrella build: passed, 11,584 jobs;
- axiom print: `propext`, `Classical.choice`, `Quot.sound` only;
- no `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declarations;
- repository lint found no defect in this module; its nonzero exit came from four unrelated
  currently unwired `RHTower` modules.

## Meaning

This certifies one endogenous law-generation mechanism rather than an RH route: failure determines
a semantically conservative executable repair, and the repair changes the overlap language that
produces the next failure.  It does not yet certify a universal abstraction or a second
non-rewriting realization.

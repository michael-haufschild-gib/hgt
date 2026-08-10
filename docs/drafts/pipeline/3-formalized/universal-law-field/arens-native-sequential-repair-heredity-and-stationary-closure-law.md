# Arens native sequential repair, heredity, and stationary closure law

- **ID:** ULF-ECMPL-TOPO-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-certified)
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveSequentialRepairHeredity`
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/endogenous-completion-mechanics/arens-native-sequential-repair-heredity-and-stationary-closure-law.md`

## Certified mechanism

Lean constructs the actual Arens two-storey topology and proves:

1. each leaf row converges to its branch point;
2. no leaf-valued sequence converges to the root;
3. the branch sequence converges to the root;
4. first sequential closure is exactly leaves plus branches;
5. second sequential closure is the whole space;
6. ordinary closure is already the whole space at stage zero and remains so after first repair;
7. repair layers are exactly branches and then the singleton root; and
8. the second repair witness lies entirely in the first repair layer.

Capstone declaration:
`ConstitutiveSequentialRepairHeredity.native_sequential_repair_mechanism`.

## Audit

- direct leaf elaboration: passed;
- `UniversalLawField` umbrella build: passed, 11,585 jobs;
- axiom print: `propext`, `Classical.choice`, `Quot.sound` only;
- no `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declarations.

## Meaning

This is the second exact endogenous-completion laboratory and the first outside rewriting. One
native repair operation generates successive legal layers even though an idempotent semantic
observer already reports completion. It certifies repair heredity and formation rank, not a
universal abstraction, RH route, selection law, coercivity theorem, or carrier-existence theorem.

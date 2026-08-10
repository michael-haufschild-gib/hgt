# Fixed-point defect, ternary genesis, and convex repair law — formalized

- **ID:** ULF-EAG-1
- **Stage:** 3-formalized
- **Paper source:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/equivariant-arity-genesis-mechanics/fixed-point-defect-ternary-genesis-and-convex-repair-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveEquivariantArityGenesis`
- **Status:** [LEAN-CERTIFIED] [NO SORRY] [NO ADDED AXIOMS] [NOT RH]

## Certified mechanism

The module proves, as closed propositions:

1. equivariant maps transport fixed source points to fixed target points;
2. no deterministic binary reporter preserves the failure-record swap;
3. every equivariant separator has three distinct image values;
4. the ternary reporter attains the lower bound;
5. rational convexification is equivariant and resolves the pair;
6. `1 / 2` is the unique rational fixed mixture;
7. an oriented binary reporter resolves the pair but breaks swap equivariance.

`equivariantArityGenesisMechanism_closed` packages deterministic obstruction, ternary repair,
convex repair, fixed-mixture uniqueness, and oriented separation in one closed theorem.

## Verification

- direct foreground elaboration of the new module: passed;
- direct foreground elaboration of the Universal Law Field umbrella: passed;
- formal lint: passed with no diagnostics;
- `#print axioms`: only standard mathlib foundations (`propext`, `Classical.choice`, `Quot.sound`)
  where rational normalization is used; the general fixed-point and three-image theorems use no
  axioms;
- final `11,435`-job Universal Law Field umbrella build: passed.  Reported linter messages are
  pre-existing and outside this module.

# Formalization record: ULF-AMCC-1

- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveAdaptiveCost`
- **Source:** `formal/GaloisForLFunctions/HTGeometry/ConstitutiveAdaptiveCost.lean`
- **Certified content:** exact transcript mimicry; canonical mimicking support contained in every
  mimic; minimization of every natural-valued additive coordinate cost; exact prefix trace and
  canonical support; exact minimum support cardinality and weighted cost; general coercive-weight
  infinite-action theorem; unbounded unit-cardinality cost.
- **Proof policy:** closed significant declarations; no `sorry`, `admit`, project postulate, unsafe
  declaration, or computation proof. Axiom print contains only standard Lean/mathlib foundations.
- **Verification:** dedicated umbrella build
  `lake build +GaloisForLFunctions.HTGeometry.UniversalLawField` passed with 3387 jobs.

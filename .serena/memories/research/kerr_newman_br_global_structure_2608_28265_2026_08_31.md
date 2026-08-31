# arXiv:2608.28265 corpus formalization (2026-08-31)

Paper: Ovcharenko, *Global structure of Kerr-Newman-BR spacetime* (arXiv:2608.28265v1). No named theorem/lemma environments; formalization extracted theorem-shaped identities and corollaries from displayed formulas.

Modules:
- `formal/GaloisForLFunctions/HTGeometry/KerrNewmanBRGlobalStructure.lean`: 60 theorems, 23 definitions.
- `formal/GaloisForLFunctions/HTGeometry/KerrNewmanBRCorpusApplications.lean`: 22 theorems, 5 definitions.
- Both imported by `formal/GaloisForLFunctions/HTGeometry.lean`.

Lean-proved content:
- Schwarzschild-BR radial weight as a strict-positive sum of squares; exact horizon and conformal-zero classifications; reciprocal clearing and C-infinity seam potentials; Weyl-flat surface classification.
- Generic Kerr-Newman-BR positive radial dressing, invariance of horizon zero locus under dressing, completed-square/discriminant identities, ring singularity classification, reciprocal rho-squared >= 1, reciprocal polynomial clearing, seam/equator/polar identities.
- Kruskal hyperbolic invariant, arctan compactification inversion/null bounds, reflection parity.
- Corpus bridges: existing Kerr-Newman Sigma/Delta/stationary-limit zero loci, metric coefficient and raw/BZ-dressed Killing-block determinants, Vaidya horizon polynomial/factorization, postselected-qubit infinity-germ parity.

Audit:
- `lake env lean` passed for both files.
- `lake build GaloisForLFunctions.HTGeometry.KerrNewmanBRGlobalStructure` passed.
- `lake build GaloisForLFunctions.HTGeometry.KerrNewmanBRCorpusApplications` passed.
- Scoped forbidden-token scan found no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.
- Representative `#print axioms` results used only standard Lean foundations: `propext`, `Classical.choice`, `Quot.sound`.
- No stale `lake`/`lean` process.
- Global `scripts/formal_tools.py lint` still fails on unrelated pre-existing umbrella-unreachable modules; neither new module is reported unreachable.

Interpretation: reciprocal radius is a reusable algebraic compactification/gluing device. Strictly positive dressing factors preserve horizon sets; polynomialized seam data excludes the Kerr ring at reciprocal infinity and transports cleanly to determinant, Vaidya, and rational-dynamics formulas. These are literature/corpus bridges, not a novelty claim.
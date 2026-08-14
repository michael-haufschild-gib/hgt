# Nested-observer hierarchical maximal-coupling face law — formalized

- **ID:** ULF-FKT-HMCF-1
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveHierarchicalMaximalCoupling` and
  `GaloisForLFunctions.HTGeometry.ConstitutiveHierarchicalMaximalCouplingChain`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN 4 FORMALIZED] [EXACT PAPER SURFACE] [NOT RH]

## Certified theorem surface

For finite nonnegative profiles of equal mass and any finite sequence of observer maps whose
equivalence relations are nested, Lean recursively constructs residual profile pairs, inserts the
maximal within-block product plan at each level, and completes the remaining marginals with a
terminal product plan. It proves:

- exact row and column marginals at every recursive stage;
- preservation of the one-sided residual invariant through every later level;
- later insertions and terminal completion cannot recreate earlier agreement;
- one coupling saturates every observer capacity simultaneously;
- capacity monotonicity under coarsening;
- literal pair mass in each collision stratum `E_j \ E_i` equals `A_j - A_i`;
- terminal mass outside `E_i` equals total profile mass minus `A_i`, hence `1 - A_i` for
  probability profiles;
- consensus couplings form a nonempty set exactly equal to the maximizers of the summed linear
  agreement objective, which is the paper's exposed-face statement;
- observer capacity is exactly `1 - finiteProfileTotalVariation` for probability profiles;
- the two crossing partitions of a four-atom space have disjoint maximal-coupling faces.

The countermodel is proved by exact constructor cases and marginal/collision-mass identities. It
uses no evaluator, numerical experiment, or computed certificate.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveHierarchicalMaximalCouplingChain.lean`
  — passed without warnings.
- `lake build GaloisForLFunctions.HTGeometry.ConstitutiveHierarchicalMaximalCouplingChain` — passed,
  8,658 jobs.
- Axiom audit on arbitrary-chain existence, collision strata, exposed face, total-variation
  identity, and incompatible-partition capstone — only `propext`, `Classical.choice`, and
  `Quot.sound`.

No `sorry`, `admit`, added axiom, `opaque`, or `unsafe` declaration is used.

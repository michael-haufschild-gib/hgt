Completed and promoted two exact Stage-2 cards.

Lean:
- formal/GaloisForLFunctions/HTGeometry/BernsteinWidder.lean
  - Defines CompletelyMonotoneOn.
  - Proves exact Bernstein–Widder existence on [0,∞): exists_finiteLaplaceMeasure_of_completelyMonotoneOn.
  - Proves converse via finiteRealLaplace and completelyMonotoneOn_finiteRealLaplace.
- formal/GaloisForLFunctions/HTGeometry/ReservoirDensityCompleteMonotonicityMarkovEquivalence.lean
  - Defines exact lower-supported Laplace, shifted CM, compact Markov reservoir predicates.
  - Proves lowerSupportedLaplaceProfile_iff_shiftedCompletelyMonotoneProfile.
  - Proves compactMarkovReservoirProfile_iff_lowerSupportedLaplaceProfile.
  - Proves compactMarkovReservoirProfile_iff_shiftedCompletelyMonotoneProfile.
- Wired both imports into formal/GaloisForLFunctions/HTGeometry.lean.

Verification:
- Exact leaf builds passed for both modules.
- Axiom audit of new capstones: only propext, Classical.choice, Quot.sound.
- git diff --check passed.
- Formal lint reports only unrelated shared-worktree unreachable modules/large-file warnings; no issue in these modules.
- Temporary scratch files deleted. Do not re-audit or rebuild these modules.

Promoted cards:
- reservoir-density-complete-monotonicity-markov-equivalence.md
- infinite-half-turn-frequency-source-admissibility-split.md
from Stage 2 to corresponding Stage 3 paths.

Continue recursive Stage-2 sweep. Use scripts/formal_tools.py research for all Lean corpus searches; never rg. Run only targeted leaf checks/builds and audit only newly created declarations. Preserve unrelated shared-worktree changes.
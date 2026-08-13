Route R producer no-go strengthened beyond absolute summability.

Added and umbrella-wired `formal/GaloisForLFunctions/RHTower/RouteRNormConvergentCalkinCoefficientRigidity.lean`.

Lean theorems:
- `matrixEntry_eq_zero_of_rectangularEvenDilationGramCombination_tendsto_compact`: for coherent all-prime coefficient matrix A, if rectangular Sonin Gram sections converge in operator norm to a compact K, each fixed off-diagonal A(i,j)=0. Proof uses finite shell coefficient lower bound at all N >= max(i,j)+1, then `ge_of_tendsto`.
- `coefficients_eq_zero_of_rectangularEvenDilationGramCombination_tendsto_compact`: with zero diagonal, A=0.
- `no_compact_normLimit_rectangularEvenDilationGramCombination_of_entry_ne_zero`: one retained nonzero off-diagonal coefficient forbids every compact operator-norm limit.

No summability hypothesis. This kills conditional/reordered coherent norm-convergent tails, strengthening `coefficients_eq_zero_of_summableEvenDilationGramAggregate_isCompact`.

Verification: `lake env lean` green; targeted `lake build GaloisForLFunctions.RHTower.RouteRNormConvergentCalkinCoefficientRigidity` green; axiom audit only `[propext, Classical.choice, Quot.sound]`; diff check green; no forbidden declarations. Cards C39/prequotient updated.

Research effect: surviving compactness producer must be genuinely non-operator-norm-convergent (e.g. singular/cutoff renormalization), in addition to non-corona. Route R remains active; do not claim RH/dead end.
# Bounded recovery histories do not control moments

Status: RETIRED — exact obstruction and adaptive positive survivor formalized.

## Rejected receiver

Infer signed-potential summability, or either one-sided local moment, solely from bounded m=2 probe data on the injective recovery mesh L_n=(log(n+1)−log2)/2, n≥2.

## Exact obstruction

`RHTower.exists_bounded_recovery_with_divergent_excess_and_deficit` constructs coefficients with |Q(L_n)|=1 for every n≥2, while excess, deficit, and signed potential series at log2 are all nonsummable.

The stronger pointwise theorem `RHTower.exists_antipodal_recovery_with_large_terms` gives |weilDeviation λ n|P_log2(n)≥1/2 at every n≥2. It starts from von Mangoldt and chooses each target opposite the current sample. Positive triangular diagonals allow exact correction; the full-kernel bound forces the nonvanishing potential terms. Cofinality and the existing one-sided divergence laws rule out finite excess and deficit moments.

## Strongest positive survivor

`RHTower.weilLogShiftRecoveryAdaptive_probe` realizes every state-dependent target policy exactly. Its state is the final earlier coefficient prefix with the untouched baseline tail. `weilLogShiftRecoveryAdaptive_head` preserves invisible coordinates, and `continuous_weilLogShiftRecoveryAdaptive_height` gives continuous dependence for fixed target histories. The existing coefficient/history homeomorphism now uses this general construction.

This is a constructive adaptive realization theorem, beyond a negative counterexample. Paper proof and exact Lean theorem are dependency-closed; only the local Lean corpus was used. Product-topology recoverability remains exact while bounded histories fail to control weighted moment convergence.

Sources: `WeilLogShiftRecoveryAdaptive.lean`, `WeilLogShiftBoundedRecoveryNoGo.lean`, and the refactored `WeilLogShiftRecoveryHomeomorphism.lean`. All three leaves compile; all 21 public declarations use only `[propext, Classical.choice, Quot.sound]`. Imports and index verified. Global lint's two unrelated unwired modules are recorded in [the formalized card](../3-formalized/weil-logshift-bounded-recovery-no-go.md).

No claim about intervening real cutoffs, external novelty, all probe indices simultaneously, or RH.

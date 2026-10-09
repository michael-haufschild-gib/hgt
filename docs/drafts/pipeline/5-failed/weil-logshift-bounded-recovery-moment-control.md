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

Original certificate: `WeilLogShiftRecoveryAdaptive.lean`, `WeilLogShiftBoundedRecoveryNoGo.lean`, and the refactored `WeilLogShiftRecoveryHomeomorphism.lean` compiled; all 21 then-public declarations used only `[propext, Classical.choice, Quot.sound]`. Imports and index were verified; that lint snapshot is recorded in [the formalized card](../3-formalized/weil-logshift-bounded-recovery-no-go.md).

## Stronger obstruction and positive classification

`dense_and_residual_weilLogShiftBoundedOuterDivergence` now makes failure of all three moments at every |y|≥log 2 generic inside the bounded-history cube [-1,1]^ℕ. Any convergent outer moment is a meagre exception there.

The origin follow-up is now stronger: `dense_and_residual_weilLogShiftBoundedNowhereBounded` proves that, on one dense residual subset of the unit product cube, absolute moment terms are unbounded in every tail at every real shift. Even eventual boundedness at one history-dependent shift is meagre; so is any summable signed moment. The two new leaves `WeilLogShiftKernelTailOrder` and `WeilLogShiftBoundedOriginGenericity` compiled successfully. Verification is tracked by the formalized `weil-logshift-bounded-origin-genericity.md` card.

Positive survivor: strict outward shifts eventually dominate every fixed multiple of an inner paired kernel; the origin inverse diagonal tends to infinity; every finite bounded prefix extends to a bounded history whose absolute origin terms tend to infinity. Open tail excursions turn these explicit witnesses into the product-topology residual all-shift statement. It does not prove one-sided origin divergence.

Uniform-small-error rescue is also retired: `WeilLogShiftUniformBallPerturbation` and `WeilLogShiftUniformBallGenericity` prove nowhere bounded absolute moment terms on a dense residual subset of every positive-radius closed supremum ball around any bounded history. Every bounded center admits arbitrarily small uniform perturbations with this divergence. Positive survivor: two opposite, ball-preserving coordinate perturbations have moment difference exactly `2 * delta * r * diagonal`, while remaining within `2 * delta * r` of the original history. Affine baseline cancellation makes this estimate independent of the center. The formalized `weil-logshift-uniform-ball-genericity.md` card records verification; full real-cutoff control remains separate.

Subcritical exponential precision is also insufficient: for every 0<=sigma<4-pi, every epsilon>0 and every bounded center, the new exponential-precision leaves give a bounded perturbation obeying |error(k)|<=epsilon exp(-sigma(k+2)) at every coordinate while its absolute moment terms are unbounded in every tail at every real shift. Bad unit-ball error parameters are dense residual; eventual boundedness or signed summability at any shift is meagre. Positive survivors: an origin diagonal lower envelope above every rate below 4-pi, a divergent exponentially damped diagonal, an exact affine response factorization, and a reusable ball-preserving affine perturbation criterion. All affected leaves compiled; `weil-logshift-exponential-precision.md` records the full audit. No conclusion at or above 4-pi, no optimality claim, and no one-sided origin or full-cutoff claim. The next conjecture tests one fixed inverse-response column.

The strengthened positive survivor is exact finite-prefix antipodal extension, together with `weilLogShiftBoundedHistory_summability_equivalences`: for every cube element, signed summability at log 2 is equivalent to either one-sided summability. Thus the missing local moment condition is substantive, and either one-sided condition suffices within the bounded cube. Paper proofs are closed and exact Lean statements verified. All 35 public declarations across the three touched leaves have standard-axiom audits; current verification and lint limitations are in [the bounded-cube card](../3-formalized/weil-logshift-bounded-cube-genericity.md).

## Exact amplification and diagonal survivor

The antipodal proof now exposes the exact invariant `w_nn|λ_n−Λ_n| = 1+|Q_n(prefix)|`, not only a lower bound. Every finite bounded history prefix admits one extension whose absolute weighted moments dominate every positive inverse diagonal simultaneously for all real shifts. Therefore universal bounded-history moment summability forces diagonal summability, and histories failing at every shift outside that diagonal domain form a dense set. Each diagonal term at log 2 is at least 1/2, so this obstruction is nonvacuous.

These positive quantitative and topological statements have closed paper proofs and exact Lean formalizations. Both touched leaves compile; all fourteen public declarations have exactly the standard axiom set. See [the diagonal-obstruction card](../3-formalized/weil-logshift-diagonal-obstruction.md) for statements and verification. Diagonal summability has not been shown sufficient. The subsequent smooth-edge result below settles the formerly open origin obstruction.

## Interior rescue also retired: signed moments at every shift

The proposed rescue—bounded recovery histories might force signed moment summability at an interior shift, especially the origin—is now refuted. `not_weilLogShiftBoundedMomentSummable y` holds for every real y. More strongly, `exists_weilLogShiftBoundedHistory_prefix_nowhere_summable` preserves any finite bounded prefix while supplying one extension whose signed moments diverge at every real shift. Such histories are dense in the unit cube, and `unbounded_weilLogShiftRecoveryMatrixBudget y C` exceeds every proposed finite-matrix bound at every shift.

The strongest new positive survivor is quantitative: for overlap width at most 1/r, the facing smooth cutoff edges suppress the truncated autocorrelation by `exp(4−4r)`. The actual recovery overlap is at most 1/n, so `sqrt(n)w_nn ≤ 2 exp(4−4n)P_log2(n)`. Existing strict-rate kernel bounds and π<4 yield positive c,γ with origin inverse diagonal at least `c exp(γ(k+2))` eventually. This identifies a concrete source of instability, beyond the negative counterexample.

Paper proof is dependency-closed. Exact Lean statements in `WeilLogShiftSmoothEdgeBound.lean` and `WeilLogShiftOriginDiagonalDivergence.lean` compile without diagnostics. The formalized smooth-edge card records complete axiom and integration checks. These new conclusions concern signed moments; no claim that every bounded history diverges, or that one-sided origin moments fail generically, is made.

No claim about intervening real cutoffs, external novelty, all probe indices simultaneously, or RH.

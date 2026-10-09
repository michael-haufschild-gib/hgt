# Bounded recovery mesh versus local moments — verified progress

Only local Lean corpus used; no web or external papers. User source restriction also persisted in `mem:instructions/corpus-only-research`.

## Exact new results
`formal/GaloisForLFunctions/RHTower/WeilLogShiftRecoveryAdaptive.lean` imports CutoffReconstruction. Two definitions: `weilLogShiftRecoveryPrefix base lam n j := if j<n then lam j else base j`, and `weilLogShiftRecoveryAdaptive base target`. Target has type `ℕ → (ℕ → ℝ) → ℝ`.
- `weilLogShiftRecoveryAdaptive_head`: indices0,1 retain base.
- `weilLogShiftRecoveryAdaptive_probe base target k`: sample at k+2 equals `target k (Prefix base (Adaptive base target) (k+2))`. Policy may inspect any part of this state; no extra causality premise.
- `continuous_weilLogShiftRecoveryAdaptive_height base`: fixed-height policies `(fun k _ => height k)` depend continuously on height.
The existing `weilLogShiftRecoveryProbe_affine` and `continuous_weilLogShiftRecoveryProbe` moved here unchanged. Homeomorphism now specializes this builder; all existing public names/statements remain available (10 declared in Homeomorphism +2 moved).

`formal/GaloisForLFunctions/RHTower/WeilLogShiftBoundedRecoveryNoGo.lean` imports Adaptive, four public theorems:
1. `tendsto_weilLogShiftRecoveryCutoff`: L_n tends to +infinity.
2. `weilLogShiftRecoveryWeight_diagonal_le n hn`: w_nn ≤ 2*pairedLogKernel(log2,n)/sqrt n for n≥2.
3. `exists_antipodal_recovery_with_large_terms`: exists λ with |Qλ(L_n)|=1 and |weilDeviation λ n|*P_log2(n)≥1/2 for every n≥2.
4. `exists_bounded_recovery_with_divergent_excess_and_deficit`: exists λ with all visible mesh samples absolute value1, but excess, deficit, and signed potential series at log2 all nonsummable.

## Mechanism
Start from Λ; at step n choose +1 when current Q_n≤0, otherwise −1. Probe correction has magnitude≥1. Previous coefficients finalized, nth baseline still Λn, later coefficients untouched. Positive diagonal realizes target exactly. Its upper bound forces absolute potential term≥1/2. Signed summability contradicts term→0. Finite excess would force actual Q(L)→−∞; finite deficit forces +∞. Cofinal bounded mesh contradicts both.
Positive survivor is exact adaptive triangular realization, not a restated negative fact. No statement about boundedness between mesh samples or an RH proof.

## Verification and state
All three leaves compiled/exported via `lake --old env lean ... -o ...`, final exit0/no diagnostics. All21 public declarations across them have exactly `[propext, Classical.choice, Quot.sound]` in /tmp axiom check. Nine new declarations plus all12 prior API declarations. Index refreshed, all21 unique API rows checked; umbrella wired. Scoped whitespace/conflict and git diff checks passed.
Current global lint exit1 ONLY two unrelated unwired modules: `RHTower.LeeYangSplitCountDifference` and `RHTower.PaperSuzukiCayleyReconstruction`. Supersedes prior one-module and seven-module snapshots; leave unrelated files alone.
Cards: `docs/drafts/pipeline/3-formalized/weil-logshift-bounded-recovery-no-go.md` and `5-failed/weil-logshift-bounded-recovery-moment-control.md`. Prior homeomorphism card updated from conjectured to proved; integer-mesh failure card links stronger result.
Lean parser reserves `prefix`; use `stateAt` for local binding. Scratch API `have := @polymorphicName` needs explicit concrete type args to resolve universe levels. Axiom output can wrap across lines; parse bracket contents with whitespace normalization.

## Frontier
Boundedness along the entire positive real cutoff axis remains unresolved. Next corpus-only audit should determine whether additional real-cutoff regularity forces a one-sided moment hypothesis or admits a different counterexample. Do not infer either outcome from this theorem. Goal remains ACTIVE; this is verified progress, not completion.


## Verified finite-data follow-up
See `mem:research/weil-logshift-recovery-domain-density-2026-10-09`: arbitrary finite recovery histories coexist with every open/closed symmetric domain and finite total excess; every realizable signed/excess/deficit moment profile is dense in product-history space. Eleven new declarations compiled and standard-axiom audited. This does not settle boundedness at all real cutoffs. New lint snapshot has only unrelated PaperSuzukiCarrierNullSets and PaperSuzukiCayleySynthesis unwired.

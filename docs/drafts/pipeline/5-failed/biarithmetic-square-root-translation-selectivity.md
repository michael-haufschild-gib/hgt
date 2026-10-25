# Square-root-energy translations cannot supply a nontrivial source action

- **ID:** biarithmetic-square-root-translation-selectivity
- **Stage:** 5-failed
- **Type:** FALSIFIED (nontrivial-survival proposal); THEOREM (positive source bounds)
- **Source:** ../../../reports/review-2410/opus.md, Mechanism A and A4
- **Statement:** For the actual damped Möbius receiver on escape, every raw translation with bounded squared length divided by receiver energy has zero normalized displacement. The stronger source-power thresholds and exact origin decomposition are formalized in ADR.

## Exact scope of the obstruction

The report proposes translations of length comparable to `T^(alpha/2)` when
receiver energy is comparable to `T^alpha`. These have bounded `k^2/E`.
ADR's `admits_or_squareRoot_successors_disappear` proves that their normalized
raw displacement tends to zero whenever the receiver escapes. Thus this scale
cannot retain the new additive information sought by the proposal.

The bare existence-and-covariance wording of A4 is not disproved: an identity
translation action can satisfy it. What fails is extracting a nontrivial action,
and therefore arithmetic selectivity, merely from the necessary scale condition
`k^2` comparable to `E`. No claim is made that escape actually occurs.

Raw translations, recentered translations, and resetting only the origin are
different operations. This card concerns the first two precise ADR definitions.

## Strongest positive survivor

Put `a=1-epsilon`, with actual subcritical damping `0<epsilon<1/2`. The proved
Vinogradov--Korobov source estimate implies `A(n)=o(n^a)`. Its increment interval
gives the exact additive-defect envelope

`|A(n+k)-A(n)-A(k)| <= min(n,k)`.

The complete pronic cost of this envelope is `2k-H_k`. Splitting at `n=k`,
combining this cap with the source power bound, and summing the decreasing tail
give, for every `delta>0`, a constant independent of `k,T` such that

`||A(.+k)-A(.)-A(k)||_T^2 <= delta k^a+C_delta`.

The exact origin decomposition gives

`||A(.+k)-A(.)||_T^2 <= 4k+2 A(k)^2`,

and hence the uniform bound `delta k^(2a)+B_delta`. Division by escaping
receiver energy shows that even bounded `k^a/E` for recentered translations,
or bounded `k^(2a)/E` for raw translations, forces zero normalized displacement.
Bounded translations are included through the additive constants; no divergence
of `k(T)` is assumed.

The new information is a source-defined hierarchy of invisible translation
scales, together with the separate origin trace. A nontrivial limit must escape
these rate classes. These are necessary conditions, not an existence theorem or
an optimality claim for the remaining scales.

## Lean and closure audit

The exact square-root obstruction and origin decomposition are in
`ArithmeticDefectRigidity/TheOriginTraceControlsMovingSuccessors.lean`:
`admits_or_squareRoot_successors_disappear`,
`pronicNorm_receiverAdditiveDefect_sq_le_cost`, and
`successorDisplacementEnergy_le_origin_trace`.

The stronger positive source theorem is in
`ArithmeticDefectRigidity/TheSourcePowerSavingControlsMovingSuccessors.lean`:
`receiver_div_sublinear_power_tendsto_zero`,
`exists_uniform_subpower_recentered_budget`,
`exists_uniform_subpower_successor_budget`,
`admits_or_sourcePower_recentered_successors_disappear`, and
`admits_or_sourcePower_successors_disappear`.

The source statements and proofs were inspected. The owning programme records
direct source checks and transitive audits using only `propext`,
`Classical.choice`, and `Quot.sound` in
[its stage-3 card](../3-formalized/the-source-power-saving-enlarges-the-invisible-translation-scale.md).
The positive survivor is reused without duplicating its implementation.

- [x] Exact killing statement separated from bare A4 existence.
- [x] Dependency-closed paper proof and stronger positive source bounds.
- [x] Exact survivor formalized and audited by its owning programme.
- [ ] Construct a nontrivial source translation at a larger scale, or classify its absence.

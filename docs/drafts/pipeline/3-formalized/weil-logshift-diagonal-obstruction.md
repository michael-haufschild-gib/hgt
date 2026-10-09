# Exact antipodal gain and the diagonal summability obstruction

- **ID:** weil-logshift-diagonal-obstruction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** local Lean corpus only: adaptive antipodal recovery, finite response matrix, bounded-history receiver.
- **Target:** Expose the exact antipodal amplification identity; construct bounded histories preserving any finite prefix whose absolute moments dominate every weighted inverse diagonal simultaneously. Deduce a necessary diagonal summability condition and dense simultaneous counterexamples outside that diagonal domain.

## Dependency-closed paper proof

In the existing adaptive construction, the next target is +1 when the current probe q≤0 and −1 otherwise. Hence the correction has absolute probe size exactly 1+|q|. Triangular first-difference gives

`w_nn |λ_n−Λ_n| = 1 + |Q_n(prefix(Λ,λ,n))|`.

Since w_nn and sqrt(n) are positive, every weighted absolute deviation is at least `P_y(n)/(sqrt(n)*w_nn)`, the exact response-matrix diagonal. The policy is independent of y, so a single history dominates all diagonals simultaneously. A prescribed bounded prefix is retained; all later history values are ±1.

If that history has a summable moment at y, its absolute terms are summable. Removing finitely many terms and comparing with the positive diagonal proves diagonal summability. Thus every finite bounded prefix admits a single history with nonsummable moments at every shift whose diagonal series is nonsummable. Such extensions converge coordinatewise to any target history as the retained prefix grows, so this simultaneous obstruction set is dense.

In particular, universal unit-cube moment summability forces diagonal summability. This is necessary only: no sufficiency or interior threshold is inferred. The exact gain also exposes the earlier-prefix probe as the amplification term beyond the bare diagonal.

The existing diagonal/full-kernel comparison gives each diagonal term at log 2 at least 1/2, so its series is nonsummable. This verifies that the simultaneous obstruction is nonvacuous.

## Plan and gates

1. [x] Corpus search and installed Lean API checks.
2. [x] Factor exact gain from the existing antipodal proof; retain all previous public statements and avoid duplicating the adaptive builder.
3. [x] Formalize simultaneous diagonal domination, summability descent, and dense prefix-preserving obstruction histories.
4. [x] Compile touched leaves, audit all public declarations, wire umbrella, refresh index, run lint.
5. [x] Update memory and clean scratch.

## Formal results

`WeilLogShiftBoundedRecoveryNoGo.lean` now has seven public theorems and 191 lines. Added `exists_antipodal_recovery_after_prefix_with_gain`, preserving arbitrary finite sample prefixes with all later samples ±1 and exact gain `w_nn|λ_n−Λ_n| = 1+|Q_n(prefix)|`. Original `exists_antipodal_recovery_after_prefix` specializes this stronger result; all six previous public statements remain unchanged.

New leaf `formal/GaloisForLFunctions/RHTower/WeilLogShiftDiagonalObstruction.lean`, 162 lines, seven public declarations (one definition, six theorems):

- `half_le_weilLogShiftRecoveryMomentResponse_log_two`: each positive diagonal term at log 2 is at least 1/2.
- `not_summable_weilLogShiftRecoveryDiagonal_log_two`: diagonal nonsummability at log 2.
- `exists_weilLogShiftBoundedHistory_prefix_diagonal_minorant`: every finite bounded history prefix extends to one history whose later samples have magnitude one and whose absolute moment terms dominate all weighted diagonal terms simultaneously for every real shift.
- `weilLogShiftBoundedMomentSummable_diagonal`: universal bounded-history moment summability implies diagonal summability.
- `WeilLogShiftDiagonalObstruction`: the same history fails at every shift with a nonsummable diagonal series.
- `exists_weilLogShiftBoundedHistory_prefix_diagonal_obstruction`: simultaneous obstruction after every prescribed finite bounded prefix.
- `dense_weilLogShiftDiagonalObstruction`: this simultaneous obstruction set is dense in the bounded product cube.

## Verification

- Both touched leaves compile/export using `lake --old env lean <leaf> -o <olean>`, exit 0 and no diagnostics, each on its first compilation. No subsequent source edits.
- All fourteen public declarations across both leaves have exactly `[propext, Classical.choice, Quot.sound]`; exhaustive scratch axiom audit exit 0 and full name coverage checked.
- Eight new public declarations; six previous public statements retained.
- Both umbrella imports unique; index refresh exit 0; all fourteen API rows unique and in the correct modules.
- Scoped whitespace/conflict and `git diff --check` checks passed.
- Global lint exit 1 on ten unrelated unwired `HTGeometry` modules: `BandKernelOperators`, `CircleSymbolGroupCStar`, `ConeCrossedProductFaithful`, `ConeKernelCrossedProduct`, `PaperStableCoordinate.ZeroFiber`, `PaperStableCoordinate.ZeroFiberExact`, `PaperStableCoordinate.ZeroFiberSpecialization`, `PaperStableCoordinate.ZeroFiberTransport`, `QKrawtchoukCompanionDeterminacy`, `RealGroupCStarFaithful`. No diagnostics name touched leaves; none of those modules was changed.
- No new analytic assumptions/axioms/gaps, experiments, raised limits, web searches, external papers, full builds, commits, or subagents.

## Next analytic target

The smooth-edge target is now proved in `WeilLogShiftSmoothEdgeBound` and `WeilLogShiftOriginDiagonalDivergence`: the `exp(4−4n)` cutoff loss forces a positive exponential lower envelope for the origin inverse diagonal. Universal bounded-history signed summability fails at every real shift, and dense simultaneous counterexamples preserve every finite bounded prefix. The follow-up `WeilLogShiftBoundedOriginGenericity` now proves dense residual unbounded absolute terms at every real shift in the unit product cube; `WeilLogShiftKernelTailOrder` supplies outward transfer. One-sided origin moments and full real-cutoff boundedness remain separate questions.

## Limits

The subsequent smooth-edge result refutes universal signed convergence at every real shift, including the interior and origin. This diagonal-obstruction theorem alone did not do so. Neither diagonal summability nor an entrywise absolute matrix bound has been shown equivalent to the exact finite-sign matrix receiver. No new analytic assumptions/axioms, numerical experiments, web searches, papers, or subagents.

## Log

- 2026-10-09 — previous turn classified verified progress. Existing antipodal proof exposes an exact `1+|q|` gain before its coarser diagonal/kernel comparison. New target preserves that information and transfers it to all real shifts simultaneously.
- 2026-10-09 — direct lexical search returned 579 hits, 274 eligible; inspected adaptive and diagonal results. Exact gain factored into existing bounded-recovery leaf without changing previous public statements. New diagonal-obstruction leaf drafted, including nonvacuity at log 2. Parent leaf compilation running; initial comparison/tail/topology API scratch passed, supplemental APIs pending parent completion.
- 2026-10-09 — both final touched leaves compile/export with exit 0 and no diagnostics on their first compilations. Exact gain, simultaneous diagonal domination, necessary summability, dense obstruction set, and nonsummability of the diagonal at log 2 are formalized. Umbrella wired; all fourteen public declarations prepared for axiom audit.
- 2026-10-09 — exhaustive fourteen-declaration axiom audit, import and index checks passed. Latest lint has only the ten unrelated wiring errors listed above. Next smooth-edge conjecture recorded from the actual local definitions, without asserting the unproved origin conclusion.
- 2026-10-09 — cross-session memory and failed-route positive survivor updated. All jobs terminal; eight owned scratch paths removed and absence verified. Goal remains active; next priority is the recorded smooth-edge origin conjecture.

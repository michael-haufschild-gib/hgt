# RH corpus refresh: clock/source frontier

Owner: this resumed research task. Fact audit, not an RH proof or a new theorem.
Reference cutoff: `e318fb81324a3a253982b526510bf8af9c856af0` (2026-09-21).

## Scope and verification

- The current ledger records 24 active routes, 37 candidates, 375 closed mechanisms,
  and no proof or disproof of RH. Read the route/candidate ledger and selected source
  proofs relevant to the paused clock/insertion route; this is not an exhaustive
  proof-body audit of the whole corpus.
- Relative to paused checkpoint `06ffc635e`, the formal-source delta through the
  reference cutoff has 222 changed files: 155 additions and 67 modifications.
  Concurrent working-tree research remains outside the committed audit.
- Applied `docs/meta/scientific-method.md` and `docs/meta/stroke-of-genius-method.md`:
  distinguish identities/receivers from produced arithmetic control; evaluate each
  obstruction against the whole route; retain positive survivors.
- Three deep searches tested copied/background cancellation, causal Volterra
  methods, and signed two-scale renewal. A targeted hybrid OR search used
  `ProcessedCore PrimeOnlyPolar renewal`. Search results reported `partial: false`,
  but compiler coverage includes pending, stale and error snapshots. Search is
  discovery evidence, not completeness, novelty, or kernel verification.
- Separate `lake env lean /tmp/...lean` import/axiom probes passed for ten selected
  declarations in the insertion, processed-core, completed-slope, wall-transport,
  renewal-packet and prime-power-reduction modules. All ten report only `propext`, `Classical.choice`,
  `Quot.sound`. These are cached-dependency audits, not fresh full-source builds.
- A combined import probe failed on duplicate `RHTower.xiZeroSet`, declared in both
  `HedenmalmInfiniteOrientationSingularities.lean:25` and
  `WeilLagFunctionCriterion.lean:47`. Separate successes do not establish that the
  combined branches compose in one Lean environment.
- The ledger footer still mentions a 72-file delta, Q's `1047/100` band and open SQB
  bounded-core compactness. Its updated route entries supersede those statements.

## Paused work already superseded

Source: [inherited insertion producer](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorInheritedPrimeInsertionProducer.lean).

- `exists_mobiusDivisorClockDelayedInsertionProducer` already distinguishes a
  favorable marginal insertion from net repayment of an inherited debt.
- `exists_mobiusDivisorClockDelayedHalfRepaymentDeadline` and
  `exists_mobiusDivisorClockDelayedHalfRepaymentCardinality` strengthen that result:
  repayment after admission time `τ` requires helper half-weight exceeding
  `η exp(τ/2)` and helper count exceeding `η exp τ`, for the produced `η > 0`.
  A fixed positive half-weight budget `W` therefore imposes the deadline
  `τ < 2 log(W/η)` on half-repayment.
- Positive survivor: actual arbitrarily late packets with favorable marginal
  insertion and preserved early fibres still exist. The theorem does not turn
  them into repayment or an exhaustive history with one global budget.
- Whole-route consequence: repeating the old delayed-helper construction cannot
  supply the missing changing-core budget. The stronger deadline is already proved.

## Actual insertion obstruction: signed cross-scale cancellation

Sources: [processed-core homothety](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorArityHeadProcessedCoreHomothety.lean),
[prime-fibre homothety](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorPrimeFibreHomothety.lean),
[two-channel dissipation](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorArityHeadTwoChannelDissipation.lean).

- Processed-core parity orientation makes each coordinate an unsigned channel or
  zero. This is a precise even/odd decomposition, not positivity of their difference.
- For prime `p > N`, inserting `p` copies the old processed coordinate at cutoff
  `N` into cutoff `pN` with factor `-√p`; parity orientation changes this to `+√p`.
  Nonnegative diagonal weights satisfying `w(insert p A) = w(A)` consequently
  have copied square mass equal to `p` times the old square mass. The remaining
  `p`-free background survives unchanged at the larger cutoff.
- Scope correction: this excludes raw copy-compatible diagonal contraction when
  old weighted mass is positive. It does **not** alone exclude a `C M²` budget:
  the cutoff changes from `N` to `pN`, so its squared normalization changes by
  `p²`. Nor does it cover every prime/cutoff regime or every possible weight.
- The actual unprocessed energy identity is already proved (prime `p > N`,
  `N ≥ 2`, fresh `p`):

  `E_(pN)(P ∪ {p}) - E_(pN)(P) = -2√p Σ_R F_(pN,P,R) F_(N,P,R)`.

  Thus the missing producer concerns signed mixed products of the actual small
  field and the actual new background, not another copy identity.
- Two-channel blocks have actual dissipative insertion laws under their stated
  dominance conditions. Finite-family reserve producers can simultaneously fund
  finitely many positive debts, including a common eventual cutoff tail. Neither
  result supplies a bound uniform over an exhaustive changing family.
- The exact cutoff-increment formula retains a mixed defect term and a squared
  defect term. In the diagonal mixed term the Möbius signs occur twice and cancel;
  unsigned defect covariance is not the same resource as history parity cancellation.
- Whole-route consequence: global proof must control changing-core signed mixed
  terms and cutoff entrance costs together. A fixed-core reserve or raw diagonal
  no-go does not decide that problem.

## Explicit logarithmic-clock target

Sources: [canonical clock](../../../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiCriticalPrimeOnlyPolarCanonicalClock.lean),
[wall transport](../../../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiCriticalPrimeOnlyPolarWallTransport.lean),
[completed slope](../../../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiCriticalPrimePolarCompletedSlope.lean),
[RH equivalence](../../../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiCriticalProperPrimePowerReduction.lean).

- Let `A(H)` be the literal valuation-one prime-minus-polar action and let `T_N`
  be `ccmFUCriticalPrimeOnlyPolarSlopeAction N`. At `N = floor(exp H)`, the exact
  clock-cell law is `A(H) = S_N - T_N/H`. Entering cells have zero weight at their
  admission wall; there is no missing jump term.
- For `N ≥ 3`, the proved causal transport law is

  `A(log N) = A(log 3) + Σ_(3 ≤ k < N) T_k (1/log k - 1/log(k+1))`.

- `ccmFUCriticalPrimeOnlyPolarAction_eq_neg_transform_add_sourceFree_sub_proper`
  identifies `A(H)` with minus the completed Suzuki triangular-curvature
  transform plus a uniformly bounded source-free action minus a uniformly bounded
  proper-prime-power action (`H ≥ 2`).
- Exact remaining gate:

  `(∃ C ≥ 0, ∀ H ≥ 2, |A(H)| ≤ C) ↔ RiemannHypothesis`.

  The equivalence is proved; its left side is not produced. Absolute variation
  of the literal prime-only sector diverges, so discarding signs cannot supply it.
- Whole-route consequence: the required relationship to time is already literal,
  through logarithmic admission times and inherited slopes. Another clock carrier
  adds nothing. The hard obstacle is uniform **signed source cancellation** in
  the accumulated slopes/curvature, including between integer walls.

## Other routes that change the choice of attack

| Source/front | Established advance or obstruction | Remaining producer / implication |
| --- | --- | --- |
| E: `MobiusRenewalPacketEnergy` | Exact positive-weight expansion of finite Gamma-Hankel energy into squares of literal Möbius renewal packets. | Uniform aggregate packet control as the exponent approaches the boundary remains open. |
| E: `MobiusPacketDifferenceSign` | Neither complete-monotonicity orientation works; actual first packet squares eventually increase just above the boundary exponent. | Packetwise monotone contraction is unavailable; an aggregate cancellation law would need more structure. |
| EDQ: `EulerDeletionResidueMartingaleDriftNoGo` | Innovations converge strongly in L², but predictable drift does not and is not uniformly integrable; fixed prefixes miss tail mass. | Do not infer full-source convergence from innovation convergence or a Vitali shortcut. |
| EDQ: `EulerDeletionTerminalCoefficientCollapse` | Common geometric resolvent cancels from the terminal source coefficient. | The signed Möbius source and normalized residual correlation remain; denominator-only control cannot replace them. |
| EDQ: `EulerDeletionLogPrimeForcing` | Exact compensated renewal includes von Mangoldt/harmonic forcing with squared norm comparable to the cutoff. | Forcing cannot be dropped as a subpower remainder. |
| SP-E/P: `SPEQuantileRieszPrimePowerHistoryVariance` | Prime-power curvature history equals matched-centroid variance minus quantile-centroid variance; translation gauge leaves history unchanged. | Actual cofinal variance ordering is still required. |
| O: canonical ground remainder | Exact numerical-range identity; the lower wall is the relevant positivity condition, not norm contraction. | Actual arithmetic lower-wall production remains open. |
| Q (ledger statement audit) | Source passivity band advanced to `0 < Re z ≤ 218/25` in the stated pole-free upper strip. | Full-strip cofinal extension remains open; finite-band success is not RH. |
| SQB (ledger statement audit) | Rellich compactness and Friedrichs compact resolvent now closed. | Literal Maass-operator identification/dense smooth core, Satake, and lifting remain. |
| U (ledger statement audit) | Finite adjacent-history source budget closed. | No-escape/coercivity across an infinite moving frontier remains. |
| D2 (ledger statement audit) | KMS parity agrees but imaginary slope fails; universal incidence correction is singular. | Separate passive completions do not replace joint source cancellation. |

## External method screening

- Broad 2026 arXiv searches used `interlacing` and `hysteresis`, after the corpus
  review. Abstracts inspected: [coordinator-polynomial interlacing](https://arxiv.org/abs/2608.11012)
  (11 August 2026) and [dynamical-thermal hysteresis](https://arxiv.org/abs/2603.24007)
  (25 March 2026). Neither abstract supplies a verified arithmetic cancellation
  lemma for the literal source above. No theorem or applicability claim is imported
  from those papers; full-paper method transfer remains untested.

## Research consequence

The resumed target is source-level signed cancellation under changing cutoff/core,
with the exact logarithmic-wall action as the RH-bearing test. Existing decomposition,
transport, finite-family repair and packet identities are inputs, not missing work.
This refresh closes no new mathematical gate: it prevents repeating superseded work
and corrects an overbroad interpretation of the diagonal obstruction. The next proof
attempt must produce control of the actual mixed-source/history term, or an explicit
obstruction to that proposed control with a positive survivor; another equivalence,
carrier, or delayed-helper construction would not advance the route.

# FU: cutoff drift and completed critical action

Status: investigation; no closure claimed.

Objective: discharge cutoff drift and completed critical action for the actual
arithmetic source, following the closed paid prime-exhaustion construction.
No assumed energy budget, RH equivalence, receiver, or estimate-only result
counts as completion. No external searches or numerical experiments.

Plan:
1. Recover exact drift and completion obligations from current Lean statements,
   including existing obstruction and rigidity theorems.
2. Conjecture, attack, and revise structural mechanisms using the whole corpus.
3. Finish a dependency-closed paper proof before new Lean formalization.
4. Audit leaf modules and axioms, wire finished modules, run formal lint, and
   clean scratch artifacts. Never build an umbrella.

Starting fact: `exists_mobiusDivisorPaidPrimeExhaustion` provides one inherited
prime-exhaustive history with every insertion prefix paid at its own integer
cutoff. It supplies neither inter-cutoff transport nor completed critical action.

## Exact obligations recovered from Lean

Write `W(M,P) = mobiusDivisorFiniteClockEnergy 1 M P` and
`H(M) = sum_{1 <= d <= M} mobiusDivisorDilationChannel M d`.

- `MobiusDivisorPaidPrimeExhaustion.exists_mobiusDivisorPaidPrimeExhaustion`
  pays insertion prefixes at `M_k = A*r_k`. It does not compare
  `W(M_{k+1},P_{k+1})` with `W(M_k,P_{k+1})`.
- `MobiusDivisorFiniteClockCountingCancellation` identifies
  `W(M, selectionPrimes M) = H(M)^2`. Offset zero gives zero instead and
  loses the completed head. This is an endpoint issue, not a missing
  pointwise convergence lemma.
- `MobiusDivisorTerminalClockOrder.exists_mobiusDivisorTerminalClockOrder`
  already controls every terminal insertion prefix by
  `max (W(M,P)) (H(M)^2)`. Removing this maximum by assuming the second
  endpoint bounded would assume the target.
- `MobiusDivisorCriticalClockProductTransport` already gives the exact
  causal delay `f_insert(t) = f_P(t) - f_P(t-log p)/sqrt p`, finite pairing
  transport, and density cancellation. Its remaining mixed correlation is
  signed and retains its earlier endpoint.

## Conjecture and attack ledger

1. **Fixed-core uniform clock control. FALSE, already formalized.**
   `tendsto_mobiusDivisorFiniteClockEnergy_div_sq_atTop` proves divergence
   for every finite prime core. Increasing a cutoff without controlling
   its source change cannot be free transport.
2. **Canonical square-root completion supplies the controller. FALSE,
   already formalized.** `criticalMovingSquareCore_energy_escape` and
   `tendsto_criticalMovingPrimeHead_pointwise_scaled` force negative
   excursions and unbounded normalized energy. The exact adaptive
   terminal transform retains the signed child correction; discarding
   that correction is invalid.
3. **Density cancellation makes each remaining correlation favorable.
   REJECTED.** The density identity includes the signed mixed term; it
   does not establish its sign. `exists_criticalAbelCompleteClockPairing_negative`
   refutes universal positivity at the actual finite critical cutoff.
   This does not by itself refute a cumulative signed payment law.
4. **Existing full-head completion closes critical energy. INSUFFICIENT.**
   `MobiusDivisorFullHeadCompletion` gives exact agreement on fixed
   compact intervals and inverse-cube linear convergence. Its weighted
   linear convergence does not provide uniform critical quadratic control.
5. **Corrected coarea removes the cost of completion. FALSE, already
   formalized.** `MobiusDivisorCorrectedCoareaOrderBarrier` forces a
   superquadratic intermediate corrected action in every complete order.
   `MobiusDivisorCorrectedCoareaMassBalance` explains the surviving signed
   mass and nonnegative variance exactly. Raw energy remains a different
   open target.
6. **Whole-ray finite-core energy controls the needed moving source.
   FALSE for the canonical cores.** `MobiusDivisorCanonicalBulkEnergy`
   proves escape beyond every fixed logarithmic controller. Replacing
   the finite physical cutoff by that whole-ray norm is not a repair.
7. **Finite graph energy closes accumulated cutoff drift. INSUFFICIENT.**
   `CCMFUSuzukiCompletedRieszGraphEnergy` already proves square-summable
   source-faithful radial increments, and explicitly leaves their partial
   sums uncontrolled. The missing summation cannot be supplied by
   Cauchy--Schwarz with an infinite clock length.
8. **The offset-one logarithmic reserve always leaves a payable successor.
   FALSE; closed scratch theorem audited in Lean.** At cutoff seven after
   processing 2 and 3, only prime 5 remains. Let `h` and `b` be its
   prime-free and prime-divisible signed sums. The corpus's analytic
   seven-channel box gives `h <= -103/1000` and
   `-65/1000 <= b <= -60/1000`. Its exact clock increment is
   `2*h*b - log(5)*b^2 = b*(2*h-log(5)*b)`. Since `log(5) <= 3`, the
   second factor is at most `-11/1000`, so the increment is strictly
   positive. This attacks monotone greedy continuation, not bounded
   cumulative continuation with a reserve.
   Exact audited statement:
   `mobiusDivisorFiniteClockEnergy 1 7 ((mobiusDivisorSelectionPrimes 7).erase 5)
     < mobiusDivisorFiniteClockEnergy 1 7 (mobiusDivisorSelectionPrimes 7)`.
   Source identifications use `mobiusDivisorSelectionFibre_one_remaining`
   and `mobiusDivisorFiniteClockEnergy_terminal`; completion uses
   `mobiusDivisorFiniteClockEnergy_complete` and
   `mobiusDivisorLastPrime_add_eq_total`.

The positive statement surviving this failed greedy conjecture is the
existing complete terminal-order theorem: every prefix can stay below the
larger of the initial clock energy and the actual completed head square.
It is already formalized. This investigation has not supplied an independent
controller for that completed square and does not retire route FU.

## Surviving investigation

The required new mechanism must control cumulative signed work at the
original cutoff, including any unavoidable positive insertion steps.
The exact terminal decomposition, causal delay law, compact agreement,
and endpoint-maximal terminal ordering already exist. Repackaging one of
them is not a structural contribution.

Investigate a source-specific admission-time law that couples cutoff work
to later insertion work without replacing the original critical head or
assuming its boundedness. No dependency-closed proof of such a law has
been obtained. No route is retired by this investigation.

## Search and verification status

Used documented `scripts/formal_tools.py research` commands, both
MobiusDivisor-filtered and whole-corpus searches, followed by direct Lean
source inspection. Some deep searches reported partial results or runtime
deadlines; compiler coverage included pending and stale entries. Candidate
retrieval is not treated as a proof audit. No web or numerical experiment
was used. No production Lean module has been added in this investigation.

Final scratch falsifier audit:
`lake --old env lean /tmp/fu3-clock-successor-audit.lean`, exit 0.
`#print axioms RHTower.fu3_clock_successor_falsifier` reported only
`[propext, Classical.choice, Quot.sound]`. No heartbeat override, admitted
premise, or evaluation command was used. Scratch files were removed after
the audit. No new module requires umbrella wiring; no umbrella was built.

**Task status: not solved.** No significant structural frontier advance is
claimed from these rejected candidates or from the scratch falsifier.

# CCM-FU clock-funding facts (own)

- `exists_mobiusDivisorUniformReserveHistory` gives a sparse, non-exhaustive
  changing core with one all-integer-cutoff quadratic budget. It does not
  insert an arbitrarily prescribed omitted prime.
- `mobiusDivisorSuccessorEnvelope_late_block_le_max_endpoints` controls every
  intermediate subset and every remaining successor of one late block by its
  two endpoints. Thus merger count is not an unavoidable additive envelope
  cost within a block.
- `not_mobiusDivisorSuccessorEnvelope_average_law` refutes uniform successor
  averaging; selection must be source-sensitive and deterministic.
- `exists_mobiusDivisorClockDelayedInsertionProducer` proves an even core has
  arbitrarily late prescribed-prime debts such that halving the debt after
  log-clock `tau` requires helper reciprocal mass bounded below away from zero
  and inverse-square-root mass greater than a positive constant times
  `exp (tau / 2)`. Its bounded-mass helpers still give only marginal
  contraction, not repayment.
- Therefore the current finite-packet budget
  `K = (9/25) * exp (4 * inverse-square-root-mass)` cannot be the global
  CCM-FU budget mechanism for a clock-delayed exhaustive order. A successful
  route needs a new cancellation-stable unbounded-mass relative-budget law,
  or a proof that no exhaustion can use delayed repayment.
- `mobiusDivisorCoprimeHead_prime_deletion` is now formally proved: deleting a
  fresh prime from a coprime head is exactly a signed two-scale clipped renewal
  of the enlarged-field head. Hence a changing core is not an uncontrolled
  dimension change. Remaining gap is a uniform source-specific signed cocycle
  bound for this renewal; no scalar reserve conclusion follows from the
  identity alone.
- `mobiusDivisorArityHeadEnergy_complete_history_balance` is now formally
  proved: at any complete prime history, terminal head square plus every
  nonempty copied-child square equals initial arity-plus-head energy plus the
  accumulated charge `J_q + 2 H F_{\{q\}}`. Thus the head is not external to
  the charge route. Remaining gaps are a literal-source bound for that coupled
  signed charge and the initial `O(M² log M)` arity cost; neither is removed by
  the accounting identity.
- `mobiusDivisorArityHeadEnergy_eq_pairs` and
  `mobiusDivisorArityHeadCharge_eq_pairs` are now formally proved. The completed
  energy has one signed source-pair kernel, with weight
  `|primeFactors(d) \ P| + 1_{primeFactors(d) \ P = ∅}` on equal residual
  labels; its insertion charge is the same kernel restricted to ordered pairs
  whose residual labels differ by exactly the inserted prime. Thus the open
  charge bound is an explicit adjacent-label Möbius divisor correlation, not an
  unspecified changing-field effect.
- `mobiusDivisorArityHeadCharge_empty_eq_prime_shift` is now formally proved
  and axiom-audited. At the empty core, squarefree source support collapses each
  adjacent residual-label pair uniquely to `e = p*d`; the exact surviving
  charge is the cutoff-truncated signed correlation weighted by
  `primeFactors(d).card + 1_{d=1}`. Therefore the immediate cancellation
  problem is a one-index truncated rank-weighted prime shift, not a residual
  label-pair problem. The cutoff `p*d ∈ mobiusDivisorSelectionIndices M` is
  essential and must remain in any analytic transform.
- `mobiusDivisorArityHeadEnergy_empty_eq_diagonal` is now formally proved and
  axiom-audited. The completed entrance cost is exactly
  `∑_{d∈I_M} (primeFactors(d).card + 1_{primeFactors(d)=∅}) C_d²`.
  It is therefore a positive source diagonal: Möbius signs have already
  squared away before the first insertion. Any route claiming to neutralize
  this entrance logarithm by signed charge cancellation confuses two distinct
  problems; a successful CCM-FU proof needs a sharper literal-channel amplitude
  estimate for this diagonal in addition to a signed prime-shift estimate.
- `MobiusDivisorWeightedCutoffDiagonal` is now formally proved and
  axiom-audited. For every fixed source weight, the literal channel-square
  diagonal has an exact cutoff successor law: a signed mixed Abel-source term
  plus the complete new-square remainder. Specializing the weight to
  `primeFactors(d).card + 1_{primeFactors(d)=∅}` identifies the completed
  entrance energy with the full-cutoff diagonal (nonsquarefree and terminal
  channels vanish) and gives its exact successor law. Thus the positive
  entrance obstruction is not an immutable initial constant: it is a
  cumulative signed cutoff-time correlation together with an explicit positive
  defect. Remaining problem is to control that correlation strongly enough
  against the defect, and to relate it if possible to the history prime-shift
  correlation.
- Expanding `mobiusDivisorDilationChannel_eq_moebius_unsigned` corrects the
  earlier sign diagnosis: in the cutoff successor mixed term, the source
  factor is `C_M(d) * (mu(d) * primeFreeDivisorDefect(M/d))`, so the two
  squarefree Möbius signs cancel.  In contrast, at the empty core a legal
  prime shift has exactly `C_M(d) * C_M(p*d) = -B_M(d) * B_M(p*d)`.  Thus
  the cutoff obstacle is unsigned defect covariance, while first-prime
  history charge has fixed negative orientation; neither can be explained by
  fluctuating Möbius signs.
- `MobiusDivisorArityHeadEmptyOrientation` is now formally proved in scratch
  and promoted.  `mobiusDivisorArityHeadCharge_empty_nonpos` states, without
  premises beyond primality, that every first insertion has nonpositive
  completed arity-head charge.  This local dissipation cannot be extrapolated
  to a complete history: nonempty processed cores retain multiple source
  indices per residual label.  The remaining CCM-FU hard problem is therefore
  precise—find a growing-core replacement orientation/cancellation law, and
  control the separate unsigned cutoff defect covariance.

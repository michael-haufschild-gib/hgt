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
- `exists_mobiusDivisorClockDelayedHalfRepaymentDeadline` is formally proved
  and axiom-audited.  For each source-produced persistent debt and every
  inverse-square-root helper budget `W`, delayed half repayment is impossible
  once `tau ≥ 2 * log (W / eta)`.  Thus bounded-mass preparation has an exact
  finite horizon; any exhaustive CCM-FU schedule must grow this mass or use a
  cancellation invariant not represented by delayed helper support.
- `exists_mobiusDivisorClockDelayedHalfRepaymentCardinality` is formally
  proved and axiom-audited.  Every half-repaying helper set whose primes begin
  after `tau` has cardinality strictly greater than `eta * exp tau`.  Thus the
  growing-mass alternative is necessarily exponentially collective; sparse
  delayed packets cannot be iterated into an exhaustive CCM-FU schedule.
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
- `MobiusDivisorArityHeadCoreDiagonal` is now formally proved and
  axiom-audited.  Every adjacent pair with the same processed prime core
  reconstructs to the literal shift `e = p*d`, so its channel product is a
  negative unsigned product.  The full nonempty-core charge has the exact
  decomposition `same-core diagonal + core-changing covariance`, and the
  diagonal is unconditionally nonpositive.  Thus the only unsigned-sign
  freedom in the arity-head route is the explicitly named covariance between
  *different* processed cores; a successful CCM-FU continuation must bound or
  cancel that term, not search for a new sign law on the diagonal.
- `MobiusDivisorArityHeadProcessedCoreFibre` is now formally proved and
  axiom-audited.  Every residual-label fibre is the exact finite sum of its
  processed-core coordinates.  Hence the remaining covariance has a canonical
  finite off-diagonal core-coordinate representation; its next viable attack
  is a source-derived bound or diagonalization of that operator, not further
  regrouping of residual labels.
- The same processed-core leaf proves a stricter fact: each
  `(processed core, residual label)` coordinate is either zero or exactly one
  literal channel at the product of those two prime sets.  Thus core-changing
  charge is a cutoff-masked signed Boolean-hypercube bilinear form in explicit
  channel values, rather than a many-to-many fibre correlation.  Any viable
  bound must exploit this Boolean sign/kernel structure or source cancellation
  across its vertices; generic fibre estimates cannot recover missing
  information.
- MobiusDivisorArityHeadProcessedCoreParity is now formally proved in scratch
  and promoted. For every legal adjacent source pair, its signed product is
  minus one to the sum of the core cardinalities times the unsigned product.
  Thus equal-parity core pairs are dissipative and opposite-parity core pairs
  are the only reinforcing terms. This does not bound the core-changing
  covariance: it identifies its exact positive bipartite sector. The next
  CCM-FU theorem must be a literal-source anti-correlation/coercivity law on
  that sector, jointly with the separate unsigned cutoff-defect covariance.
- MobiusDivisorArityHeadProcessedCoreOrientation is now formally proved in
  scratch and promoted. Multiplying a core/residual coordinate by the parity
  of both prime sets yields exactly one nonnegative unsigned literal channel,
  or zero. Hence every residual fibre is a difference of positive even-core
  and odd-core masses in its natural residual orientation. The unresolved
  CCM-FU statement is now a source anti-correlation/coercivity law for those
  two positive mass differences at adjacent residual labels; no unresolved
  Möbius sign remains inside a coordinate.
- MobiusDivisorArityHeadProcessedCoreSignedMeasure is now formally proved in
  scratch and promoted. The ordinary residual orientation is exactly the
  signed measure over canonical nonnegative core coordinates, with the sole
  coefficient given by processed-core parity. This is a strict structural
  reduction of the changing-core charge: the route no longer has a generic
  signed source sum, but an adjacent-label correlation of two explicit
  even-minus-odd positive measures. Proving its cofinal nonnegative
  correlation is the remaining CCM-FU charge barrier.
- `exists_mobiusDivisorFiniteDebtFamilyReserveProducer` is now formally
  proved and compiled. For every finite family of nonempty prime cores whose
  limiting fixed-core coefficient debts are strictly positive, one common
  fresh prime and arbitrarily distant fresh prime pairs decrease every debt
  by a common positive coefficient divided by the first pair prime. The proof
  takes finite minima of literal relative negative bands and prime-release
  constants; it is relative-debt control, not an absolute-energy surrogate.
  The common coefficient and its thresholds depend on the whole finite
  family. Therefore this does not overcome the clock-delayed obstruction or
  construct an exhaustive order; the exact remaining requirement is a
  cancellation-stable growth law for those constants as pending debt support
  increases.
- `exists_mobiusDivisorFiniteDebtFamilyTailReserveProducer` is now formally
  proved and compiled. The same common pair has one common eventual cutoff
  tail on which every family coordinate gains a positive quadratic reserve.
  This removes the limiting-coefficient-only gap for finite debt vectors. The
  eventual threshold is still obtained by a finite intersection and has no
  source-uniform control as the family grows, so it cannot yet be iterated to
  an exhaustive CCM-FU order.
- `exists_mobiusDivisor_prescribed_stream_repair` has the explicit prefix
  coefficient `C' = C + 2 * sqrt C * H + H^2 = (sqrt C + H)^2`, while its
  endpoint decreases the unnormalised successor envelope by one cutoff. This
  is an upper bound supplied by its construction, not a lower bound; it cannot
  itself prove that repeated repaired streams fail to have a uniform budget.
  The deep corpus search found no theorem upgrading this finite prescribed
  stream to an exhaustive CCM-FU order.
- `mobiusDivisorArityHeadCharge_nonpos_of_oriented_nonneg` is formally proved
  and axiom-audited. If all oriented residual fibres at a processed core are
  nonnegative, every completed arity-head charge is nonpositive: both the
  weighted adjacent residual correlation and the head--singleton term reverse
  sign under insertion. `exists_mobiusDivisorTwoChannelBlockArityHeadDissipation`
  specializes this to every fresh prime at the existing two-channel blocks,
  including nonempty cores. This is a genuine nonempty-core charge law, but
  those blocks remain sparse and do not furnish the required exhaustive,
  cancellation-stable global budget.
- `MobiusDivisorArityHeadProcessedCoreHomothety` is formally proved and
  axiom-audited. At cutoff `p*N`, processing prime `p` sends every old
  processed-core coordinate `(A,R)` to `(insert p A,R)` as exactly
  `-sqrt(p)` times its old value; in canonical core--residual orientation the
  transported mass is therefore `sqrt(p)` times the old nonnegative mass.
  Every old adjacent-label core-pair correlation is copied with the positive
  factor `p`. Hence prime dilation/renewal preserves the reinforcing
  opposite-parity sector rather than dissipating it. This closes the
  homothety-only repair strategy: any exhaustive CCM-FU budget must quantify
  cancellation from the new non-divisible background against the replicated
  sector; the transport identity alone cannot deliver that cancellation.
- The same axiom-audited leaf proves the stronger square-mass law: for every
  residual label, the total square mass over *all* processed-core coordinates
  after a fresh processed dilation is at least `p` times its former mass.  The
  `p`-containing core slice has exactly that mass, and the p-free slice is a
  sum of squares.  Hence no nonnegative processed-core energy, reserve, or
  Lyapunov functional can be the missing exhaustive CCM-FU budget.  The only
  remaining mechanism is a quantitatively source-specific cancellation in the
  signed residual quotient between that expanding copied slice and the new
  p-free background.
- `mobiusDivisorSelectionProcessedCoreFibre_weighted_square_mass_insert_mul_prime_le`
  is now formally proved, source-compiled and axiom-audited.  For every
  nonnegative processed-core diagonal weight invariant under the canonical
  copy `A ↦ insert p A`, its square functional expands by at least the factor
  `p` under fresh prime dilation.  Thus no copy-compatible positive diagonal
  metric can contract the carried CCM-FU debt; weights that compensate by
  `1/p` discard the replicated old debt rather than pay it.  Any viable global
  estimate must use genuinely off-diagonal signed background/copy
  cancellation, with constants stable as the core changes.
- `mobiusDivisorProcessedCoreChildCopyBilinear_eq_scale` is formally proved:
  every finite bilinear observer of the entire inherited processed-core copy
  sector, with arbitrary signed off-diagonal core weights and arbitrary two
  residual labels, is multiplied exactly by the fresh dilation prime `p`.
  This strictly strengthens pairwise and diagonal expansion.  Hence no
  copied-sector cancellation can pay inherited core-changing covariance; the
  only possible CCM-FU repayment is a quantitatively controlled cross term
  with the new `p`-free background.
- `mobiusDivisorSelectionProcessedCoreFibre_insert_pfree` and
  `mobiusDivisorSelectionProcessedCoreFibre_oriented_mass_insert_mul_prime`
  are now source-compiled and axiom-audited.  At cutoff `p*N`, every
  p-free processed-core coordinate is exactly its unprocessed value at the
  large cutoff, while every p-containing coordinate is the canonical
  `sqrt(p)` copy of the same old core at cutoff `N`.  Therefore the total
  canonical positive core mass splits exactly into the p-free large-cutoff
  background plus `sqrt(p)` times the small-cutoff mass.  The live
  cancellation problem is consequently not generic cross-core mixing: it is
  the alternating-parity quotient of these two aligned, same-core positive
  fields.  Any CCM-FU closure must prove a uniform source inequality for
  that two-scale quotient; positive mass accounting cannot supply it.
- `mobiusDivisorOrientedFibre_insert_mul_prime_renormalization` is now
  formally proved and axiom-audited. For every residual label omitting fresh
  prime `p`, its post-processing oriented coordinate is exactly the p-free
  background at cutoff `p*N` minus `sqrt(p)` times its old oriented
  coordinate at `N`. Its square retains the full signed cross-scale term.
  Vanishing is equivalent to exact equality of those two terms. Thus the
  CCM-FU source inequality has a necessary-and-sufficient coordinatewise
  target: establish stable background/copy matching (or its aggregate
  replacement) across an exhaustive prime order; diagonal mass cannot
  substitute for this cancellation.

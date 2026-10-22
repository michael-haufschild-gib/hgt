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
- `mobiusDivisorOrientedResidualEnergy_insert_mul_prime_eq_zero_rigid` is
  formally proved.  For every finite residual detector with strictly positive
  weights, zero post-insertion oriented energy forces
  `background R = sqrt p * old R` at every measured residual label `R`.
  Thus there is no aggregate or cross-label cancellation escape from the
  two-scale identity: a viable CCM-FU schedule must establish simultaneous
  pointwise matching on each residual family it uses.  The remaining open
  problem is whether the literal p-free source can satisfy those cofinal
  pointwise constraints while preserving, rather than renormalizing away,
  the inherited changing-core debt.
- At the unprocessed base core `P = ∅`, squarefree unique factorization makes
  residual labels source-atomic: pointwise matching would require the unit
  channel relation `C(p*N) = sqrt(p) * C(N)`.  This cannot be rejected by a
  scaling argument.  The proved exact mean
  `C(M) / sqrt(M) → log(2*pi)/2 - EulerGamma - 1/4` makes the relation
  leading-order resonant.  Therefore the live CCM-FU obstruction is a
  subleading, moving-endpoint defect in this channel relation.  A proof using
  only positive mass, homogeneity, or leading asymptotics cannot resolve it;
  it needs a new uniform nonvanishing/decorrelation law for that defect.
- A proposed fixed-core multiplicative cocycle for the unit mismatch
  `C(a*b*N)-sqrt(a*b)*C(N)` is an exact algebraic identity, but it does not
  advance the changing-core problem: after each dilation the processed core
  changes.  The literal two-prime source already expands that update as the
  full four-channel inclusion--exclusion block
  `a-b-c+e` (`mobiusDivisorSelectionEnergy_two_primes_eq_blocks`).  Hence a
  fixed-core cocycle would discard precisely the new background/copy terms
  whose signed covariance is open.  Do not promote that identity as a
  CCM-FU payment mechanism; any viable composition law must retain the
  changing processed-core field and its complete cross term.
- `UniformPrimeSubsetBooleanInversion` is now source-compiled and
  axiom-audited.  For every finite source and every packet `A`, the normalized
  Boolean difference of label energy is *exactly* the ordered source-pair sum
  restricted by `label(i) ∆ label(j) = A`; it is not merely an inclusion or a
  low-order approximation.  If each coefficient has its label parity, the
  unnormalized alternating Boolean energy is nonnegative in every finite
  order.  This is a strict all-order replacement for the prior isolated
  third-order sign calculation.
- `MobiusDivisorAllOrderBooleanSign` specializes that theorem to the literal
  Möbius divisor source at the original core: for every finite prime packet
  `A`, `mobiusDivisorEnergyBooleanAlternating M ∅ A ≥ 0`, equivalently the
  forward order-`A` interaction has sign `(-1)^A.card`.  The source check and
  an identical scratch axiom audit close the theorem without premises or
  nonstandard axioms.  This does **not** fund a changing core: the existing
  late-block transport adds `2 * signedBlockMass * matchingFibre` to each
  nonzero Boolean grade, whose sign is not controlled by original-core
  parity.  Therefore the CCM-FU hard barrier is now exact: prove a
  cancellation-stable bound on that transported matching-fibre term (or a
  stronger orientation invariant preserved by an exhaustive schedule), not
  another finite-order interaction identity.
- `UniformPrimeSubsetCompression` is now source-compiled and axiom-audited.
  Residualization is associative: processing `P ∪ B` is exactly the same as
  replacing the atomic source by its `P`-residual fibres and processing `B`.
  Therefore full residual-fibre parity orientation at *any* core controls all
  finite future Boolean grades at that core.  This converts the moving-core
  problem from a hierarchy of higher interactions into one concrete invariant:
  preservation of the oriented compressed residual source.
- The strengthened `MobiusDivisorAllOrderBooleanSign` leaf proves and its
  scratch audit closes the sharp late-block boundary.  If a legal late block
  still has nonnegative residual head, then every finite future Boolean grade
  has nonnegative alternating energy.  Since late-block parity was already
  known for every nonempty residual label, the head is the sole missing label
  in this all-order orientation argument.  Hence head crossing is not a
  technical first-order defect: it is precisely where the current
  orientation-based CCM-FU mechanism ceases to control the complete future
  interaction field.  The next hard problem is a quantitative,
  cancellation-stable head-crossing law compatible with exhaustive funding.

- `MobiusDivisorPrimeDilationBooleanJet` source-proves the exact all-order
  prime-dilation cocycle.  For every finite p-free residual detector and
  every finite Boolean packet disjoint from `p`, its post-processing jet is
  `J_background + p * J_old - 2 * sqrt(p) * J_cross`, with `J_cross` the
  literal detector-weighted background/copy pairing.  Thus replicated old
  data and diagonal energy cannot pay changing-core debt: cumulative signed
  control of this explicitly identified cross-jet family is a necessary
  CCM-FU target.  The leaf is wired into `RHTower.lean` and source-checked;
  its Olean/axiom audit remains pending because its exact target build tried
  to replay more than 8,776 unrelated dependencies and was stopped.

- `MobiusDivisorPrimeDilationBilinearCocycle` source-proves the directed
  finite residual Gram law.  Under a fresh processed dilation, every signed
  kernel is exactly its large-cutoff background Gram term plus `p` times its
  inherited Gram term minus both directed background/copy cross Grams.  Thus
  the core-changing charge cannot be reduced to a diagonal detector even at
  finite order: a CCM-FU payment theorem must bound the signed two-direction
  cross kernel itself.  The source check closed; the exact leaf build was
  stopped after replaying more than 8,750 unrelated dependencies, so Olean
  and axiom audit remain pending a non-broad cache path.

- Failed novelty check: the attempted raw core-changing parity-mass split was
  only a summed restatement of the existing processed-core parity law and
  signed-measure representation.  It was source-checked but deliberately not
  retained or wired.  The actual unsolved object remains the cofinal signed
  correlation of adjacent even-minus-odd core measures, together with the
  independent cutoff-defect covariance; a raw parity regrouping cannot pay it.

- Route T audit: the corpus already proves every-base prime supply in
  `(x, x + x^(71/100)]`, hence a `p^(171/100)` ordered gap-square prefix
  bound.  The critical mesh-energy receiver is proved only below exponent
  `3/2`; consequently that supply route misses its receiver by a real
  `21/100` exponent gap and cannot be promoted through the existing Abel
  argument.

- Route T no-go: the corpus proves
  `¬ (Summable residualUpperVariation(1/2) ∧ Summable primeGapCriticalEnergy)`
  and the corresponding positive-ray absolute-Borel/Tonelli obstruction.
  It also proves the lower-boundary residual Fourier kernel is absolutely
  convergent and `C∞`; neither fact yields the required continuation.  Any
  viable Route-T producer must therefore be a nonabsolute, source-specific
  continuation/cancellation law, not a stronger pointwise supply, an
  absolute variation estimate, or boundary smoothness.

- Route T small-shell closure: `MaynardOrderedPrimeGapSmallShell` proves
  `Σ_{shell(k,j)} gap² ≤ 8·2ʲ·2ᵏ` from literal disjoint occupancy and block
  containment alone.  Consequently every shell with
  `2ʲ ≤ 4·(2ᵏ)^(31/80)` has square mass at most
  `32·(2ᵏ)^(111/80)`.  Since `111/80 < 3/2`, all gap scales below the exact
  fixed-width packet threshold are subcritical without prime-density input.
  The remaining Route-T gap-moment obstruction is therefore confined to
  shells `2ʲ ≥ 4·(2ᵏ)^(31/80)`, precisely where the fixed-width packet width
  `H0 = 2ʲ/(4·2ᵏ)` is admissible (`H0 ≥ (2ᵏ)^(-49/80)`).

- Route T buffered-weld obstruction: `MaynardBufferedPhysicalSelectedCellNoGo`
  proves the exact interface deficit
  `1 - μB * (1 - (1 + ν)/2) = d / (2 + 3d) > 0`, where
  `μB = routeTPairedKernelBufferedMu`, `ν = routeTGapMomentNu`, and
  `d = maynardLongGlobalAmplitudeDeficit`. Hence there is no
  `0 < μ ≤ μB` and `α ≥ (1 + ν)/2` with the physical-slice phase
  `1 < μ * (1 - α)`. The available transition selected-cell theorem cannot
  weld to any buffered low shell even at its weakest threshold. The positive
  survivor is exact: every viable low-shell weld must prove a
  cancellation-preserving reciprocal paired bad-set estimate below
  `(1 + ν)/2`, or replace the physical phase inequality itself.

- Route T direct Guth--Maynard exclusion: at the explicit buffered physical
  witness `(μ, α) = (19/5, 18/25)`, one has `μ ≤ μB` and
  `1 < μ(1-α)`, while the unpolarized Guth--Maynard middle-term exponent
  `μ(18/5-4α)` is strictly larger than Route T's required second-alternative
  exponent `1 + μ(1+ν-2α)`.  This closed comparison is formalized by
  `routeT_buffered_guthMaynard_middleTerm_direct_noGo`.  Therefore the
  published three-term large-value bound cannot be composed verbatim with the
  buffered physical receiver; any use of cubic-trace technology must suppress
  that middle term by a genuinely paired correlation before the usual
  large-value count.

- Route T strengthened Guth--Maynard no-go:
  `routeT_guthMaynard_middleTerm_fails_physicalPhase` proves the preceding
  incompatibility on the whole physical phase, with no buffered-range
  restriction.  The exact excess is
  `mu * (3/5 - nu) + 2 * mu * (1 - alpha) - 1`; it is positive from
  `nu < 1/2`, `mu > 0`, and `1 < mu * (1-alpha)`.  Consequently no parameter
  choice within the physical receiver can make the ordinary unpolarized
  Guth--Maynard middle term fit Route T.  This removes parameter tuning as a
  possible weld and leaves only a pre-Gram polarised correlation law (or a
  different arithmetic receiver) as a live cubic-trace direction.

- Route T cubic-trace mechanism check: the CGL/Guth--Maynard matrix route is
  built from a positive Gram operator.  Replacing two normalized windows by
  their difference preserves linear pole cancellation but its Gram energy is
  the positive self-energy of the difference, so it does not inherit the
  linear zero-mode cancellation automatically.  A viable paired cubic-trace
  attack must therefore be polarised before Gram formation, with a new
  positivity/large-value mechanism; ordinary signed coefficient substitution
  is not the sought weld.

- Route T common-mode physical comparability no-go:
  `eventually_routeT_commonMode_reference_exceeds_two_targetWidths` proves
  uniformly for `lambda ∈ [x,2x]` that the frozen reference relative width
  exceeds twice the target width.  The separation has exact positive exponent
  `theta - 1 + 49/80 = 29/80 - d/2`.  Therefore neither existing outer nor
  arbitrary-order physical-slice receiver can be applied directly to the
  common-mode pair: both require `R ≤ 2H`.  A dyadic width telescope is not a
  shortcut, because it must additionally control its polynomially wide
  transition rungs; a valid successor needs a paired noncomparable receiver
  or a new transition-band mechanism.

- Correction to the immediately preceding route-T inference: the corpus
  already has the fixed-source proportional width ladder through
  `exists_eventually_routeT_proportional_primeFree_large_range_packet_natOrder`.
  It reaches the literal `N^(31/80)` target width, so proposing that ladder
  again is redundant.  Its known failure is quantitative, not structural:
  the generic cell/L2/L4 assembly leaves the exact `1/50` gap above the
  required `3/2` moment exponent.  The common-mode comparability theorem
  therefore isolates the real new target: a cancellation-preserving,
  arithmetic transition-band estimate whose gain survives before any
  positive Gram or generic fourth-moment reduction.

- Route T phase-extraction exponent correction (Lean-closed): the pointwise
  target approximation threshold is `80/49`, but a dyadic-shell integral
  pays the shell length as well as the pointwise Mellin defect.  Its true
  exponent is `2 - 49*mu/80`, so the analytic transfer can have a decaying
  target error only for `160/49 < mu < mu_ref`, where
  `mu_ref = 1/(1-theta)`.  `MaynardCommonModePhaseExtraction` now formalizes
  both boundaries and their strict overlap.  The earlier `80/49` interval was
  an integrand-level condition, not a valid phase-integral window.  This
  correction changes the route: the known selected-cell receiver through
  `11/5` cannot consume the phase bridge at all.

- Route T receiver consequence of that correction: the corpus extends literal
  physical-cutoff selected-cell counting through `mu <= 11/5`, and its scalar
  adjacent/overweight comparisons have no upper-height restriction.  But
  `160/49 > 11/5`; there is **no** overlap between the actual phase-integral
  window and the known selected-cell extraction.  The hard obstacle is not
  merely phase-integral-to-cell conversion: a new all-amplitude receiver or a
  phase-aware signed correlation must work above `160/49` before the bridge
  can touch Route T's existing count machinery.

- Route T phase-window localization (Lean-closed): every exponent with both
  integrated target reserve and arbitrary-order reference reserve satisfies
  `11/5 < mu < 17/4`
  (`routeT_phaseExtraction_integratedWindow_in_selectedCellGap`).  This
  places the whole phase-transfer window strictly between—not merely outside
  one endpoint of—the two existing selected-cell regimes.  The missing object
  is therefore now concrete: a cancellation-preserving, all-amplitude,
  phase-aware selected-cell/count receiver on that intermediate band.

- Route T phase-extraction bridge (new, Lean-closed):
  `exists_fixedSource_pointMassPhase_lower_of_pairedShell` proves that every
  positive paired shell with lower mass `B` yields a phase integral of the
  *same frozen literal Heath--Brown aggregate* at least
  `B - E_reference - E_target`.  Here
  `E_reference = P*Cj*(N/R)^(j+1)*U^(-j)` is the arbitrary-order wide
  reference tail, while
  `E_target = 4*P*V*(H/N)*|V-U|` is the sharp narrow target-to-point-mass
  error.  This is the first Route-T theorem that retains paired cancellation
  all the way to a norm-one Mellin phase on the selected shell.  It removes
  the analytic-interface obstruction, but the integrated target error places
  any decaying application above `160/49`, already beyond the `11/5`
  selected-cell ceiling.  The successor must be a new high-height,
  phase-aware all-amplitude receiver rather than a direct handoff to the
  existing count.

- Route T inverse-Mellin test (negative, with survivor): the frozen aggregate
  is indeed an exactly finite `LSeries` packet
  (`LSeries_heathBrownWindowRelevantEligiblePacket`) with explicit finite
  support, and the corpus already supplies the exact finite-window phase and
  sinc kernels (`SymmetricPhaseIntegral`, `DirichletPolynomialSincEnergy`).
  However the packet is an *eligible, window-relevant signed subpacket*, not
  the full von Mangoldt coefficient sequence.  Prime-freeness therefore gives
  no coefficientwise sign, vanishing, or local-mass law for it.  A phase
  integral lower bound alone can only be converted generically to an `L2` or
  pointwise bound after a shell-length loss, below the existing `alpha >= 3/4`
  selected-cell threshold.  Thus unweighted inverse-Mellin localization is
  not a Route-T closure.  The positive survivor is precise: construct a
  *signed local coefficient correlation* for the eligible packet—retaining
  the paired kernel's cancellation—whose Fourier kernel has a source-proved
  one-sided lower bound.  This is a different hard target from another
  generic cell/L2/L4 extraction.

- Route T phase derivative reserve (Lean-closed): in the full integrated
  phase window `mu < 1/(1-theta)`, every Route-T amplitude `alpha >= 3/4`
  has canonical derivative-complement exponent at most
  `mu*(1-alpha) - (1-mu_ref/4)`.  The reserve is strictly positive, and
  arbitrary fixed polylogarithmic receiver costs absorb into half of it.
  Thus scalar derivative counting is not the high-phase obstruction; the
  missing theorem is phase-aware selection/correlation before count formation.

- Route T bare-phase spatial boundary (Lean-closed): the extracted point-mass
  shell is exactly a zero-real-part unit-cell Mellin packet.  Its unconditional
  spatial `L2` energy is bounded by `8*x` times the squared cell envelope sum
  (up to the established logarithmic factor), so generic phase `L2/L4` retains
  one full physical-base factor and cannot supply Route T's second-count
  measure scale.  The exact positive survivor is an anchored phase difference
  or signed phase correlation that contributes one reciprocal-base gain before
  the spatial energy step; with that gain, the existing second-count
  cancellation closes without additional exponent loss.

- Route T local-anchor no-go (Lean-closed): in the actual phase window
  `mu > 160/49`, the phase oscillation of a shell of height `M^(1/mu)` across
  one target-width prime-free interval has base exponent
  `1/mu - 49/80 < -49/160`.  It is therefore asymptotically phase-flat across
  every available local gap.  Endpoint differencing inside a single prime-free
  interval cannot create the reciprocal-base gain missing from bare-phase
  spatial energy.  The surviving target is necessarily nonlocal: correlate
  separated physical bases, or prove a source-specific signed correlation law
  that does not reduce to local phase variation.

- Route T phase-orientation no-go (Lean-closed): the point-mass phase packet
  is exactly covariant under global source multiplication, and in particular
  `a ↦ -a` reverses its real part while preserving every norm-level datum used
  by the current common-mode transfer.  Hence no positive signed phase lower
  can be deduced from the paired-shell norm lower and norm-only analytic bounds
  alone.  A separated-base continuation must introduce a source-specific,
  non-gauge-invariant signed correlation; more norm estimates cannot supply
  the missing orientation.

- CCM-FU factorial endpoint (Lean-closed): the deterministic boundary in the
  critical Chebyshev--factorial prefix satisfies
  `|E_N| ≤ log(N+3) + 1 + log 2`, using only finite Stirling comparison.
  Thus it cannot create a power-scale obstruction in the completed profile;
  any such obstruction must remain in the signed Chebyshev-remainder
  transform.  This does not bound that transform.

# Exhaustive clock continuation

Owner: critical-clock product task. RH and paid exhaustive continuation remain open.

## Frozen target

Construct nested prime cores exhausting every prime, with cumulative source
payments controlling all intervening original cutoffs and their complete
processing under one critical-action bound. Sparse bounded checkpoints alone
do not satisfy this target.

## Source facts and obstruction checks

- The preceding growing-depth payment uses a fixed seed, excludes prime 2,
  and only pays prescribed primes above a moving logarithmic threshold.
  Its quantified conclusion does not admit direct exhaustive iteration.
- `exists_mobiusDivisorSmallTerminalCore` processes all primes outside two
  macroscopic signed windows and has a square-root head. Taking its clock
  beyond an inherited finite core can include every old prime.
- `mobiusDivisorSuccessorEnvelope_le_terminal_density` controls the terminal
  square sum by `M * primeCounting M`, uniformly over the inherited core.
  PNT absorbs the additional logarithmic clock weight into a uniform
  quadratic endpoint bound, now proved in the source construction below.
- `MobiusDivisorWeightedTerminalHeadBarrier` already excludes completing all
  these small-head endpoints by fixed-positive-weight monotone insertions.
  That obstruction does not exclude nonmonotone bounded completion.

## Closed source construction [BRIDGE]

Module: `MobiusDivisorExhaustiveClockCheckpoints`.

- `eventually_exists_mobiusDivisorTerminalClockBudget`: there is b>=8 such
  that, eventually for every N, at `M=28*(b+1)*N` an actual prime core P
  contains every prime at most `4*b*N`, is contained in the active primes
  below M, and has `W(P,M)<=200*M^2`. Every original integer cutoff
  `M<=L<=M+M^(1/4)` has `W(P,L)<=201*L^2`. No source availability, initial
  energy, or sign premise is assumed.
- `exists_mobiusDivisorExhaustiveClockCheckpoints`: closed existence of
  strictly increasing clocks and nested actual prime cores with
  `M_(n+1)=8*M_n`, `P_n subset SelectionPrimes(M_n)`, and
  `SelectionPrimes(M_n) subset P_(n+1)`. Every prime is eventually permanently
  processed. The constants 200 and 201 hold uniformly for all stages at
  their checkpoints and collars, independently of growing core cardinality.

## Dependency-closed paper proof

1. Exact squarefree energy shows `W(P,M)<=(1+log M)*E(P,M)`.
2. For a terminal core with head at most `5*sqrt M` and residual quotients
   at most 7, the existing literal density law gives
   `E(P,M)<=((46/5)^2+(441/25)*pi(M))*M`.
3. PNT gives `(1+log M)*pi(M)<=4*M` eventually. Also `1+log M<=M` for M>=1.
   Hence `W(P,M)<=(3880/25)*M^2<=200*M^2`. This avoids exponential
   cardinality constants entirely for the constructed terminal cores.
   The core producer is used only at fixed epsilon=1; no invalid substitution
   of a moving epsilon into its eventual threshold is made.
4. The actual terminal-core producer leaves omissions only in its two signed
   windows, both above `4*b*N`. It therefore includes every prime below that
   boundary. Core-uniform cutoff transport spends one additional `M^2` on
   the fourth-root collar, yielding `201*L^2`.
5. Beyond the common threshold T, choose `N_n=(T+1)*8^n`. Since b>=8,
   the lower processed boundary at stage n+1 exceeds M_n. Any witnesses
   selected at these clocks are therefore nested and capture the entire
   previous active prime set. Strict clock growth gives prime exhaustion.

## Whole-route consequence

Prime exhaustion, nesting, and a core-uniform full weighted bound at
geometric checkpoints are now simultaneously produced. Small primes,
including 2, are eventually included. This is stronger than the former
independently chosen fixed-seed extensions. Inclusion is not a proved payment
at the old clock. Cumulative paid continuation and RH remain open.

## Unproved implications that must not be asserted

The checkpoint estimate concerns `W(P_n,M_n)`. Original-wall completion
requires control of `W(P_(n+1),M_n)` once the next core includes all primes
active at M_n. The attempted induction supplies no comparison between these
two quantities. Advancing the clock in an exhaustion argument therefore
leaves a missing estimate at the old wall. Fourth-root collars do not cover
the factor-eight gaps of the proposed checkpoint sequence. The attempted
diagonal selection has not supplied that estimate or a cumulative payment law.

The next mathematical obligation is source control of old-wall completion
and inter-checkpoint motion. Producing more independently bounded endpoints
will not establish that missing estimate.

## Weighted completion attack

- Corpus audit: `exists_mobiusDivisorTerminalPrimeOrder` already constructs
  an endpoint-optimal terminal order for unweighted energy. Repeating this
  theorem would not advance continuation. Its weighted analogue is absent
  from the inspected source and search hits.
- Closed [BRIDGE]: every actual terminal core admits
  a complete remaining-prime order whose full logarithmic clock energy never
  exceeds the larger actual endpoint energy. This produces an order; it
  does not assert a bound on the final signed source or solve the frozen
  paid-exhaustion target.
- Dependency-closed paper mechanism: retain the literal terminal leaf cost
  `(1+log p)*a_p^2`. If some next insertion decreases energy, take it. If
  none does, every remaining signed leaf agrees with the head and the final
  square dominates every remaining intermediate state. Induct on omitted
  primes. Unlike monotone completion, this allows final energy increases.
- Module `MobiusDivisorTerminalClockOrder` proves the exact weighted
  terminal decomposition and `exists_mobiusDivisorTerminalClockOrder`.
  `exists_mobiusDivisorSquareRootTerminalClockOrder M` is a closed producer
  for each literal square-root core, with no energy or sign premise.
- `exists_mobiusDivisorExhaustiveClockOrders` is a closed construction of
  nested, prime-exhaustive cores at factor-eight clocks, together with an
  actual complete list of each checkpoint's remaining primes. Every list
  prefix has `W<=max (200*M^2) (F(M)^2)`. Its final processed set equals all
  primes active at that checkpoint and is contained in the next core.
  Discarding two initial checkpoints makes each old active-prime core
  contain all square-root primes of the next clock, admitting the terminal
  construction uniformly over stages.
- Whole-route consequence: terminal ordering creates no additional peak
  above its two weighted endpoints. Uniform payment of the completed
  endpoint and transport between checkpoints remain independent open
  obligations. This result must not be called paid exhaustive continuation.
- The old-wall estimate itself remains the completed arithmetic source;
  prime exhaustion cannot change it. Neither large later-clock terminal
  capacity nor an order minimizing intermediate peaks supplies its bound.
- Direct endpoint-payment attempt: the proved PNT cancellation is
  `F(M)*log M/(M*sqrt M) -> 0`, where `F` is the full signed Abel source.
  The required endpoint is `F(M)^2=O(M^2)`. The former rate does not imply
  the latter. The available `O(M^2)` diagonal and terminal singleton costs
  leave the mixed full-head square uncontrolled; absorbing the logarithmic
  leaf weights does not remove that square.
- Broad 2026 searches on sweeping and hysteresis found
  [Goatin--Moreti](https://arxiv.org/abs/2601.17403), on scalar conservation
  laws with a Play memory operator. Its supplied constitutive law has no
  established identification with the arithmetic clock; no result is used.

## Coupled-energy attempt: no closure

- `mobiusDivisorCriticalClockPairing_joint_energy_law` retains the exact
  insertion increment `E_old(T)/p - 2*K_old(log p,T)/sqrt p` at the enlarged
  clock. Nonincrease at that clock would require
  `K_old(log p,T) >= E_old(T)/(2*sqrt p)`. Paying clock growth requires
  additional cumulative control. Cauchy--Schwarz bounds the absolute size
  of K and does not supply this lower bound. No such source bound was
  proved in this attempt; individual nonincrease is not asserted necessary
  for the more general cumulative target.
- The literal prime-dilation identity gives each new oriented coordinate
  as `B_R - sqrt p*A_R`. Expanding a weighted modified energy still leaves
  `sum_R w_R*B_R*A_R` with its sign. Bounding its absolute value loses the
  required payment. Exact-zero rigidity for this residual only concerns
  zero energy; it does not exclude bounded nonzero residual energy or
  approximate aggregate cancellation.
- The cross-term energy method in
  [Bouin--Dolbeault--Ziviani](https://arxiv.org/abs/2608.28120) requires
  coercivity and a specified dissipative evolution. Neither has been
  established for the arithmetic prime-delay product. Importing that method
  without proving these source properties would assume the missing step.
- Whole-route status: no new bound on completed F(M), no payment for the
  factor-eight clock gaps, and no new Lean theorem from this attempt.
  Further work must establish cumulative signed arithmetic correlation;
  another endpoint order or an assumed coercivity premise does not close
  paid exhaustive continuation. This is an unsuccessful proof attempt,
  not a disproof or retirement of the route.

## Prescribed-prime self-correlation and direct debt reduction [BRIDGE]

- The exact renewal formula at the prescribed prime r gives
  `rho(P+r)*D_(P+r)(r)-rho(P)*D_P(r)` equal to
  `-rho(P)*r*sqrt(r)/(r+1)*(D_P(1)+D_P(r^2)/r^2)`.
  Here rho retains the full squarefree density product; D is the actual
  inverse-cube continuous-head pairing. This is a derived candidate, not
  a replacement for the frozen paid-continuation conjecture.
- Dependency-closed paper lower bound: put
  `g(x)=H_P(x)+A*H_P(x/A)`, A>=1. Its squared inverse-cube integral is
  `2*(D_P(1)+D_P(A)/A)`, while its signed moment is
  `(1+1/A)*m_P`. The existing core-uniform positive moment m0<=m_P and
  `integral_(1,infinity) x^(-3)=1/2`, applied to
  `(g(x)-2*m0)^2/x^3`, give `D_P(1)+D_P(A)/A >= m0^2`.
  Thus the negative self-correlation margin has a single constant before
  both the prime and growing core, retaining rho exactly.
- Novelty audit: the corpus already has prescribed-prime phase preparation
  and local relative-debt reduction. Those results have core-dependent
  budgets. This result instead bounds one actual correlation at the
  prescribed ratio uniformly in the core.
- Closed: `exists_mobiusDivisorDilationMean_uniform_plus_gap` and
  `exists_mobiusDivisor_uniform_prescribed_prime_correlation_drop` prove
  the two bounds above with the constant chosen before the core and
  prescribed prime. Density is retained; the numerical margin is not
  claimed independent of the density product.
- Closed source producer: `exists_mobiusDivisorDirectPrescribedDebtReduction`.
  For any nonempty finite prime core P, prescribed missing prime r, and
  helper lower bound B, two actual fresh primes p<q above B and d>0 satisfy,
  on one common eventual cutoff tail,
  `d*M^2*(1+log M) <= (W(P+r,M)-W(P,M))
    -(W(P+r+p+q,M)-W(P+p+q,M))`.
  The debt is measured before all helpers; there is no preliminary core
  change and no assumed debt or source sign. The full original logarithmic
  clock weight remains in the conclusion.
- Paper mechanism for the producer: continuity preserves the strict
  negative relative correlation near ratio r. The exact two-prime profile
  gives positive relative coefficient release there. PNT supplies fresh
  primes in that ratio window. Fixed-core logarithmic counting comparison
  transfers this strict gain to the complete finite clock energies on one
  eventual tail. These are source proofs, not assumed comparison inputs.
- Whole-route obligation unchanged: this inverse-cube correlation law is
  not yet a bound on finite logarithmically weighted counting energy;
  cumulative finite-cutoff payment and completion remain to be proved.
- The ratio-window width, helper onset and finite-clock onset still depend
  on P and r. A strict relative-debt decrease need not pay the entire debt
  or bound either absolute energy. Iterating it without quantitative
  threshold and total-payment control would repeat the original gap.
- Further dependency-closed consequence, now formalized in
  `MobiusDivisorQuantitativePrescribedDebtPayment`:
  write `K=rho(P)*D_P(1)`, `debt=K(P+r)-K(P)` and
  `G=rho(P)*D_P(r)-rho(P+r)*D_(P+r)(r)`. The three-shift Gram inequality
  gives `2*K*G >= sqrt(r)*(r+1)*debt^2`. Cauchy--Schwarz pairs
  `H(x)+r^2*H(x/r^2)` with `r*H(x/r)` in the inverse-cube measure.
  This keeps density exactly and relates the available feedback to the
  actual debt, rather than only the fixed positive source moment.
- Closed derived producer [BRIDGE], not a replacement for paid exhaustion:
  `exists_mobiusDivisorDirectPrescribedDebtDescent` in
  `MobiusDivisorDirectPrescribedDebtDescent`. Positive prescribed-prime
  coefficient debt forces `D_P(r)<0`
  by the exact release identity. The proved self-correlation drop makes
  `rho(P+r)*D_(P+r)(r)-rho(P)*D_P(r)<0` simultaneously. Continuity gives
  a common ratio interval; the same actual helper pair therefore
  decrease both absolute energies and their relative debt before any
  preparation. The two-prime profile and full logarithmic counting limit
  give a dependency-closed paper proof of this local simultaneous descent.
  Its whole-route limitation is the uncontrolled total payment and moving
  onset, not the sign of either absolute asymptotic energy change.
- Exact closed conclusion: either the prescribed-prime limiting coefficient
  debt is nonpositive, or for every helper-distance bound there are fresh
  actual primes p<q and d>0 such that, on one common eventual integer-cutoff
  tail, the old-core full logarithmic energy drops by at least
  `d*M^2*(1+log M)`, the prescribed-prime core energy drops by at least
  `2*d*M^2*(1+log M)`, and their relative debt drops by at least
  `d*M^2*(1+log M)`. Both baselines precede all helpers. No energy/sign/
  payment premise is supplied. The first alternative is a coefficient
  statement, not an assertion of finite-clock payment.
- Iteration audit: this particular witness selection imposes
  `p>sup(P)` and `q>r*p`. Repeating it for the same r makes the successive
  helper scales grow at least geometrically. The certified relative gain
  uses `d<=a/(2*p)`, with
  `a=c*rho(P)*r*sqrt(r)/(4*(r+1)*U^2)` and `U>=r`; rho decreases under
  prime insertion. Thus these certified coefficient-normalized amounts can
  have arbitrarily small total when the first helper is moved far out. This invalidates inferring
  full repayment from repeated strict descent. It does not upper-bound the
  actual payments or disprove another construction. Quantifying the same
  isolated-pair step alone does not resolve the whole-route obstacle;
  cumulative mixed correlations between batches at usable clock scales
  remain the required source problem.

## Cumulative-batch attempt: no closure

- The direct local descent theorem does not contain a comparison between
  the payment of a union of helper pairs and the sum of their isolated
  payments. The exact renewal formula changes the source pairing after
  every helper; the full product contains all inter-pair terms. Treating
  each pair against the original core leaves these terms unpaid.
- The inherited-prime cluster producer already controls the entire Euler
  product, but only proves favorable marginal insertion after preparation.
  Its own `barrier_reciprocal_cost` proof requires positive reciprocal-prime
  mass for fixed positive net repayment. Its `barrier_reciprocal_halfweight`
  proves that helpers beyond B with bounded inverse-square-root mass W
  have reciprocal mass at most `W/sqrt(B)`. Thus that bounded-mass distant
  cluster construction cannot be upgraded to full net payment by choosing
  the helpers farther out. This is an existing source obstruction, not a
  new obstruction or a retirement of the cumulative route.
- The finite retained-field source cone is already closed for every fixed
  field, including common-parent prime supply and full preparation bounds.
  Those witnesses do not control their aperture, margins, source capacity,
  or preparation cost uniformly over growing fields. Reusing this existence
  theorem does not close the changing-core quantifiers.
- The whole-route failure in this attempt is explicit: no signed bound on
  the inter-pair terms, no sufficient cumulative payment, and no control of
  old-wall completion or the intervening original cutoffs was obtained.
  No new Lean theorem is claimed. Subsequent work must attack the finite-
  cutoff mixed source charge itself; neither another isolated-pair bound
  nor an arbitrarily distant bounded-mass preparation removes this gap.
- Broad 2026 searches on avalanche and renormalization led to
  [Hénard](https://arxiv.org/abs/2608.10992). The probability-tail triangular
  system in that paper has no established identification with the signed
  arithmetic clock. No result from the paper is used.
- Both deep corpus searches completed without reported search errors; the
  lexical follow-up also completed. Relevant theorem statements and source
  proofs were inspected directly. All owned search processes exited. No
  Lean process, numerical computation, or full build was started for this
  unsuccessful cumulative-batch attempt.

## Finite-cutoff diagonal-payment attempt: no closure

- The exact arity-head history balance retains nonempty copied-child
  squares, not sums of individual channel squares. At the level of paper
  bookkeeping, a channel with initial remaining-prime rank k>0 appears in
  precisely k-1 nonempty copied diagonals over a complete history: each
  removal counts while another remaining prime is present. Its initial
  arity-head diagonal weight is k, so one unweighted copy remains. Rank
  zero contributes its head square directly. The analogous logarithmic
  diagonal removes the sum of log(p) over the channel's processed primes.
- This does not give a lower bound on actual payment. Every actual copied
  square also contains signed off-diagonal source pairs; their negative
  part can reduce the diagonal contribution. Dropping those terms would
  be an invalid lower bound. Keeping them recovers an uncontrolled signed
  covariance in the complete history balance. No new Lean carrier was
  added for this bookkeeping, and no net-payment theorem was obtained.
- Whole-route implication: neither separately upper-bounding the rank
  entrance diagonal nor formally cancelling only its individual squares
  establishes the requested bounded critical action. The missing estimate
  must retain the off-diagonal copied terms together with the accumulated
  arity-head charge and the changing cutoff.
- The finite-charge deep search completed normally. The exponent-method
  search and rank-payment search returned partial results with reported
  retrieval/runtime failures; their available hits were checked against
  source. No retrieved theorem supplied the missing covariance bound.
  All three owned searches exited. No Lean process or numerical experiment
  was started, and no new Lean proof is claimed for this attempt.

## Debt feedback and quantitative helper construction [BRIDGE]

- `mobiusDivisorDilationMean_three_shift_gram` proves the literal
  three-shift Gram inequality:
  `2*(D_P(A)/A)^2 <= D_P(1)*(D_P(1)+D_P(A^2)/A^2)` for every
  positive dilation and finite prime core. It follows by integrating the
  square of the three actual delayed heads, with coefficients
  `(D_P(1), -2*D_P(A)/A, D_P(1))`. No new source estimate is assumed.
- Closed feedback and actual-prime producer: writing `rho` for the full
  squarefree Euler product, `K=rho*D_P(1)`, `delta=K(P+r)-K(P)`, and
  `G=rho(P)*D_P(r)-rho(P+r)*D_(P+r)(r)`, the exact renewal identity gives
  `2*K*G >= sqrt(r)*(r+1)*delta^2`. In the positive-debt branch both weighted
  pairings have negative margin `r*min(delta,delta^2/K)/8`. Continuity on a
  ratio window contained in `[r,2*r]`, the existing actual-prime pair
  profile and the full logarithmic counting limit then give payment
  `min(delta,delta^2/K)/(128*r*p)` on a common eventual cutoff tail.
  Public names: `mobiusDivisor_prescribed_debt_quadratic_feedback`,
  `mobiusDivisorPrescribedDebtPairPayment`, and
  `exists_mobiusDivisorQuantitativePrescribedDebtPayment`.
  The latter constructs two fresh actual primes beyond any prescribed
  distance, with old-core absolute drop >= d, prescribed-prime-core drop
  >= 2*d and relative-debt drop >= d, all multiplied by the complete
  `M^2*(1+log M)` weight on one common tail. Its first alternative is
  nonpositive limiting debt, not finite-clock payment.
- Whole-route implication: this removes an unspecified gain from the direct
  helper construction; it does not supply a cumulative payment budget.
  The allowed ratio aperture, first-helper threshold and finite-counting
  onset still depend on the core. Exhaustive continuation requires control
  through these changing thresholds and all intervening original cutoffs.
- Deep Gram/debt search returned partial indexed source/method hits, including
  exact dilation transport and physical pairing formulas. No retrieved hit
  was treated as a checked instance of the new three-shift feedback law.

- The quantitative-threshold deep/method search returned partial hits:
  fixed-core continuity, comparable-prime second-insertion cost and existing
  clock collars. None gave core-uniform onset or a batch mixed-correlation
  bound. In particular the pair profile obtains its error constant from
  `exists_bound_mobiusDivisorDilationMean P`, a fixed-core contour bound.
- Broad 2026 interlacing/recurrence searches led to
  [Jordaan--Kumar, revised August 2026](https://arxiv.org/html/2604.25692v2).
  Its mixed recurrence starts from polynomial real-root/interlacing data.
  No correspondence with the signed arithmetic heads was established;
  no result from that paper enters the proof.

- Paper audit of this exact certificate under repeated positive-debt steps:
  actual coefficient debt decreases, so `delta_n <= delta_0`, while this
  witness selection has `p_(n+1) > q_n > r*p_n`. Therefore its advertised
  coefficients obey `d_n <= delta_0/(128*r*p_n)` and every finite sum is
  bounded above by `delta_0/(128*p_0*(r-1))`. This is strictly below the
  initial debt. It bounds the guaranteed coefficients, not the actual
  energy releases; a step might release more or end the positive-debt
  branch. Thus iterating these certificates alone cannot certify full
  repayment. This paper consequence was not added as another Lean receiver.

## Collective-window attempt: clock-span survivor

- The existing actual debt-prime producer requires reciprocal helper mass
  above a positive eta to halve its inherited coefficient debt. Increasing
  cardinality inside a bounded ratio window does not evade this condition:
  Mertens' interval bound controls the entire prime window, not just a
  sparse selection or a bounded inverse-square-root budget.
- Closed source survivor,
  `exists_mobiusDivisorLogClockSpanDebt` in
  `MobiusDivisorDelayedClockSpanDebt`: for every even
  nonempty finite prime core and every prescribed lower prime bound, the
  source produces an omitted prime r, debt delta>0, kappa>0 and threshold T.
  If tau>=T, every actual helper set with
  `tau < log p <= (1+kappa)*tau` leaves net coefficient energy greater than
  `K(P)+delta`, while the initial omitted-prime energy is `K(P)+2*delta`.
  No helper cardinality, inverse-square-root mass or source-sign premise
  is needed. The original full logarithmic finite clock debt has the same
  positive lower bound on one common eventual tail over every subset of
  that finite prime window.
- Paper mechanism: with m=min(S), a=m-1 and b=max(S), interval Mertens gives
  `tau*sum(1/(p+1)) <= kappa*tau+log(2)+mertensIntervalConst`.
  Choose kappa=eta/4 and tau>=4*(log(2)+mertensIntervalConst+1)/eta.
  This contradicts the necessary reciprocal mass for half repayment.
  Finite intersection of the full clock limits gives the common tail.
- Quantifier scope: the common finite-clock tail is obtained AFTER fixing
  tau. Its onset can depend on tau. This excludes eventual repayment in
  each fixed window; it does not by itself exclude a coupled schedule
  tau=tau(M) using transient finite-clock cancellation. The prior claim
  that every successful schedule must use older helpers or wider spans
  was stronger than this theorem. Paid exhaustive continuation remains open.

- Four deep/source-method searches completed with partial retrieval coverage.
  Fixed-core cluster products, reciprocal-cost and cardinality results were
  checked in source; broad whole-corpus hits included Nyman--Beurling
  carriers and signed tensor expansions, without a discharged source
  payment bound. No candidate was substituted for the missing cumulative
  correlation law.
- Broad 2026 paving/fragmentation searches located
  [Han--Hart--Khudorozhkov--Nandkishore](https://arxiv.org/abs/2604.06461).
  Its constructed Hamiltonian sectors have no established identification
  with these arithmetic helper products; no paper result enters this proof.

## Finite-clock feedback attack: no continuation proof

- Put `A_P(b,T)=T*mobiusDivisorCriticalClockTriangularPairing P b T`,
  `a=log r`, and retain the literal density `rho(P)`. Specializing the
  joint source law at lag a gives the finite-clock feedback identity

  `rho(P)*A_P(a,T+a) - rho(P)*r/(r+1)*A_(P+r)(a,T+a)`

  `= rho(P)/(r+1) * (A_P(a,T+a)-A_P(a,T)`
  `  + sqrt(r)*(A_P(2*a,T)+A_P(0,T+a)))`.

- The known infinite-clock self-correlation drop does not remove the
  displayed finite lag-boundary difference. Nor may its equal full-clock
  Gram diagonals be substituted for the different finite endpoints here.
  No cumulative sign bound on these actual source terms was established.
  This equation is a diagnostic specialization, not a payment producer;
  no additional carrier module is being promoted.
- The local quantitative helper theorem has a core-dependent ratio
  aperture, helper threshold and counting onset. Its quantifiers allow
  choosing a tail after fixing a core; they do not supply one paid tail
  while that core grows. Waiting alone does not address the old-wall
  completed source square. These are failures of the attempted iteration,
  not a disproof of paid exhaustive continuation.
- Two renewed deep searches reported complete retrieval (`partial=false`);
  the multiple-debt query reported partial retrieval and mostly unrelated
  quadratic-residue hits. Indexed source/compiler coverage remains mixed.
  Actual finite-clock, common-reserve, prescribed-prime and quantitative
  payment declarations were checked. No new cumulative payment theorem
  was found or proved. Search status is not mathematical evidence against
  the target.
- Broad 2026 hysteresis/balayage searches located
  [Yadav--Green--Das](https://arxiv.org/abs/2607.24163).
  Its externally driven reaction law has no established correspondence to
  arithmetic prime insertion. No result from that paper enters the proof.
- Whole-route change required: work directly with the cumulative finite
  counting mixed terms and old-wall completion, rather than repeat a
  fixed-core coefficient-limit iteration. The frozen target remains
  paid exhaustive continuation -> bounded critical action -> RH.

## Audit facts

- Finite-clock feedback diagnostic: `lake env lean
  /tmp/hgt-finite-clock-feedback.lean` passed; axiom audit contained only
  `propext`, `Classical.choice`, `Quot.sound`. One earlier owned check
  was terminated and collected before replacement; failed elaborations
  were corrected before the successful check. This diagnostic introduces
  no production module and asserts no payment sign. The scratch was
  removed; `/tmp/hgt-finite-clock-feedback.log` retains the final audit.
  All three renewed searches and all owned Lean processes exited.

- Delayed clock span: `lake env lean /tmp/hgt-clock-span.lean` passed
  without warnings. The public theorem's axiom audit contains only
  `propext`, `Classical.choice`, and `Quot.sound`. Named final audit
  `lake build GaloisForLFunctions.RHTower.MobiusDivisorDelayedClockSpanDebt`
  passed without new-leaf warnings; cached dependency messages replayed.
  The leaf is wired into `RHTower.lean`; no full or umbrella build ran.
  Index refresh passed. Lint returned only the four previously recorded
  unrelated reachability errors, none concerning this leaf. All four
  owned searches, all scratch Lean checks, the named build, lint and index
  exited. Scratch proof/card removed; audit logs remain under
  `/tmp/hgt-clock-span*`. The local failed candidate and its positive
  survivor are recorded in
  `../5-failed/rh-delayed-short-clock-span-payment.md`.

- Quantitative payment: `lake env lean /tmp/hgt-quant-debt.lean` passed
  without warnings. All three public theorem axiom audits contain only
  `propext`, `Classical.choice`, and `Quot.sound`. Named final audit
  `lake build GaloisForLFunctions.RHTower.MobiusDivisorQuantitativePrescribedDebtPayment`
  passed without new-leaf warnings; cached dependency warnings were replayed.
  The module is wired into `RHTower.lean`. No full or umbrella build ran.
  Corpus index refresh passed. Lint returned six unrelated reachability
  errors: the four previously listed modules, plus
  `ThetaCuspHawkingBMFullAngularCTPSchwarz` and
  `HTGeometry.HilbertSchmidtBlockDouble`. No lint error concerned the new leaf.
  Both owned deep searches, all scratch Lean checks, the named build,
  index and lint processes exited. Owned scratch proof/fragments removed;
  audit logs remain under `/tmp/hgt-quant-debt*`.

- `lake env lean /tmp/hgt-direct-debt-descent.lean` passed without warnings.
  The new simultaneous-descent producer's axiom audit contains only
  `propext`, `Classical.choice`, and `Quot.sound`.
  Its named final build passed without new-leaf warnings; existing
  dependency warnings were replayed. The leaf is wired into `RHTower.lean`.
  No full or umbrella build was run.
  Final index refresh passed. Final lint returned only the four previously
  listed unrelated umbrella reachability errors; the transient Maass error
  was absent. All owned Lean/build/search/index/lint processes exited.
  Owned scratch proofs and fragments were removed; logs remain under
  `/tmp/hgt-self-debt*` and `/tmp/hgt-direct-debt-descent*`.
- `lake env lean /tmp/hgt-self-debt.lean` passed without warnings. All
  three public source theorems' axiom audits contain only `propext`,
  `Classical.choice`, and `Quot.sound`. The new module is
  `MobiusDivisorPrescribedPrimeSelfCorrelation`, wired into `RHTower.lean`.
  Its named final build passed without new-module warnings. No full or
  umbrella build was run.
- Self-correlation index refresh passed. Lint reported five unrelated
  umbrella reachability errors: `MaassFiniteDeckCuspidalGreen` plus the
  four previously listed below. No error concerned the new module.
- `lake env lean /tmp/hgt-paid-terminal-order.lean` passed without warnings.
  The three public order producers' axiom audits contain only `propext`,
  `Classical.choice`, and `Quot.sound`. The promoted leaf is wired into
  `RHTower.lean`. Final named audit
  `lake build GaloisForLFunctions.RHTower.MobiusDivisorTerminalClockOrder`
  passed without new-leaf warnings; only existing dependency warnings were
  replayed. No full or umbrella build was run.
- Terminal-clock-order index refresh passed. Repository lint again returned
  only the same four unrelated umbrella reachability errors listed below;
  no new-leaf error. All owned processes exited, scratch proof removed,
  logs retained under `/tmp/hgt-paid-terminal-order*`.
- `lake env lean /tmp/hgt-exhaustive-checkpoints.lean` passed without warnings.
  Both public theorem axiom audits contain only `propext`, `Classical.choice`,
  and `Quot.sound`.
- The leaf is wired into `RHTower.lean`. Final named audit
  `lake build GaloisForLFunctions.RHTower.MobiusDivisorExhaustiveClockCheckpoints`
  passed without new-leaf warnings. Existing dependency warnings were replayed;
  no full or umbrella build was run.
- Corpus index refreshed successfully. Repository lint returned four unrelated
  pre-existing umbrella reachability errors: `ThetaCuspHawkingBMLiteralCyclicPeierlsLowerWeylRadialDetector`,
  `ThetaCuspHawkingBMLiteralCyclicPeierlsSelfInverseSquarePhysical`,
  `ThetaCuspHawkingBMLiteralCyclicPeierlsSelfMixedCuspFlux`, and
  `XiHeatCassiniWoldJointDepthMobiusSourceTransport`. No error concerns this leaf.
- All owned Lean, build, search, index, and lint processes exited. Scratch
  proof/name-probe files were removed after their verified proof was promoted;
  audit logs remain under `/tmp/hgt-exhaustive-checkpoints*`.
- Full-corpus deep search completed; the focused terminal/weighted search
  returned partial results. Candidate lemmas, source methods and their actual
  quantifiers were checked against source. No search result discharged an
  assumed source estimate.
- Broad 2026 searches on reservoir and dissipation led to
  [Beuria--Shukla](https://arxiv.org/abs/2608.04028). Its freely designed decay
  spectrum supplies no law for the fixed arithmetic source; no result from
  that paper is used.

## Uniform debt while helper windows and cutoffs move

- `exists_mobiusDivisorUniformMovingHelperDebt` produces an actual omitted
  prime r>N, delta>0, eta>0, B>0 and ONE cutoff M0 for each nonempty even
  finite prime core P. Its source gap is K(P+r)=K(P)+2*delta. At EVERY
  M>=M0, EVERY actual helper set S with p>=B and sum_S(1/p)<=eta leaves
  W(P+r+S,M)-W(P,M)>=delta*M^2*(1+log M). M0 precedes S; cardinality,
  overlap, child depth and helper positions may change with M.
- `exists_mobiusDivisorMovingClockSpanDebt` produces r,delta,kappa,T,M0
  with the same gap, and the finite-clock lower bound holds for all
  M>=M0, all tau>=T and all helper subsets of
  tau<log p<=(1+kappa)*tau. Unlike the earlier fixed-window theorem, this
  covers coupled tau(M) and S(M), including transient cutoff choices.
- Exact mechanism: old squarefree cofactor r survives unchanged if
  r>M/B and no helper divides it. All other old samples lie in a set of
  cardinality at most floor(M/B)+sum_S floor(M/p). Each old weighted
  sample is <=C(P)*M*(1+log M), with C(P)=((3/5)*2^(card(P)-1))^2.
  New squares are nonnegative. Consequently the full possible payment is
  <=C(P)*M^2*(1+log M)*(1/B+sum_S 1/p), uniformly before any limit.
  The actual omitted-prime coefficient gap then produces the stated
  finite-clock witnesses. Interval Mertens supplies the moving-span bound.
- Whole-route implication: a moving short window cannot escape these
  debts by outrunning a window-dependent convergence threshold. The
  retained-cofactor count closes that specific quantifier gap. This is
  a derived bridge, not paid exhaustive continuation. Broad reciprocal
  helper mass, older active helpers, cumulative mixed cancellation and
  completion of every original action cutoff remain uncontrolled.
- Scratch proof of both producers passed with only propext,
  Classical.choice and Quot.sound. No numerical computation or
  additional axiom was used. Named audit status is recorded on the card.

- The named final build of `MobiusDivisorMovingClockDebt` passed without
  new-leaf warnings; cached dependency warnings were replayed. It is wired
  into `RHTower.lean`. No full or umbrella build ran. Lint reports only
  the four unrelated reachability errors documented on the
  [formalized card](../3-formalized/rh-moving-helper-clock-debt.md).

- Corpus index refresh passed. All owned Lean/build/search/lint/index
  processes exited. Scratch proof and fragments were removed after
  promotion; audit logs remain under `/tmp/hgt-moving-clock*`.

## Whole-child balancing: unresolved source feasibility

- `eventually_exists_mobiusDivisorFiniteDepth_uniform_prime_collar` fixes
  the child field I before choosing its inward margin, cutoff collar and
  eventual onset. Applying it with the complete field at the running
  cutoff would exchange these quantifiers. A smaller fixed I leaves new
  receiving coordinates outside the controlled inner product. The full
  weighted insertion identity still contains those coordinates.
- Boolean selection and fractional merger have different squared
  energies. For parent a, copied child b, receiving weight w, copied
  weight w+ell and selection fraction t, their exact difference is
  `t*(1-t)*w*b^2`. Keeping the full copied logarithmic weight does not
  erase this variance. This scalar diagnostic alone does not account for
  overlapping helper products or construct an arithmetic target.
- A signing theorem controls deviation from a supplied fractional mean;
  interpreting its signs as prime inclusion/exclusion does not bound that
  mean. No complete weighted fractional source payment has been produced.
  [Guo--Fang--Lu, September 2026](https://arxiv.org/html/2609.11189v1)
  explicitly gives endpoint signing without a prefix bound. No theorem
  from the paper is imported or assumed in Lean.
- Whole-route consequence: sharper generic rounding cannot supply the
  missing arithmetic mean or exchange the fixed-field quantifiers. The
  open construction must establish full fractional payment, including
  copied squares and all active children, before its Boolean rounding and
  original-wall completion. This attempt supplies no new payment theorem.
- Current retrieval had incomplete/stale inventory (5,044 pending files
  in the reported snapshot). Four deep searches were inspected with their
  candidate lemmas and source arguments; relevant signatures were checked
  directly in current source. Missing search hits are not mathematical
  evidence of impossibility.

- The two weighted variance identities passed `lake env lean` in scratch
  without warnings. No source module was added; the identities are not
  claimed as new payment knowledge. All owned search and Lean processes
  exited, and the scratch file was removed. The unresolved attempt is
  recorded in [whole-child fractional payment](rh-whole-child-fractional-payment.md).

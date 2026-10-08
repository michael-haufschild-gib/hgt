# WP03 — Singular arithmetic detection research loop

- **ID:** WP03-SAD
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/weil-work/03-singular-arithmetic-detection.md
- **Statement:** Every full-cone Weil-positive sequence has its literal reciprocal G with ζG bounded on every half-plane Re s > x > 1/2.

## Goal and exact scope

Prove the assigned detector from full positivity alone. No extra arithmetic regularity,
summability, zero-free, growth, or spectral-integrality premise may be assumed.
The detector does not itself produce a full-positive sequence or prove unconditional RH.
Existing Lean modules remain read-only. New modules use WeilWorkSingularArithmetic*.
User explicitly requires wiring finished modules into the umbrella; this overrides the
package's default read-only umbrella restriction for the necessary import only.

## Plan

1. Audit exact corpus frontier and current primary literature.
2. State competing falsifiable conjectures addressing actual untwisted functions.
3. Attack novelty, truth, circularity and significance before formalization.
4. Complete dependency-closed paper proofs; formalize only surviving exact statements.
5. Audit leaf modules, axioms and lint; record limitations; start next conjecture.

## Gates

- [x] 0 → 1: assigned target and scope read; corpus search initiated.
- [ ] 1 → 2: dependency-closed paper proof of detector.
- [ ] 2 → 3: exact detector formalized and audited.
- [ ] 3 → 4: publication and novelty audit complete.

## Working log

- 2026-10-07: Read hgtl7, repository instructions, WP03 and shared contract.
  docs/architecture.md and docs/testing.md absent. update_plan tool unavailable;
  this file records the plan. Existing unfinished goal already matches user request.
- Corpus bounded-quotient search complete; coverage source-heavy (compiler freshness
  not inferred). Exact receiver verified in WeilProducerZetaQuotientBohrRecurrence.
- Existing reciprocal subpolynomial growth and producer logarithmic growth already
  close a naive growth-estimate proposal. Do not repackage these as new knowledge.
- Bohr-route card distinguishes mean/typical-twist control from the untwisted
  exceptional orbit. Its paper-only claims are not adopted as established theorems.
- [OPEN CORE] Strengthen unconditional actual-function control to height-uniform
  boundedness of ζG, or discover a genuinely new restriction that addresses this gap.

## No-go closure

No new route retired. Initial candidate selection remains in progress.

## Cycle 1 — Sharp reciprocal cancellation and the quotient gap

- Bold target: for every full-positive λ, the Dirichlet polynomials of
  qλ = 1 * μλ have uniformly bounded sup norm on each Re s ≥ σ > 1/2.
  Failure could occur through exceptional aligned heights despite small ordinary sums.
  [OPEN CORE]: prove this bound from positivity, without a supplied regularity premise.
- Competing target: ordinary sums of qλ have square-root cancellation. This is weaker
  than the required uniform vertical bound and must not be substituted for it.
- Preliminary candidate kills: reciprocal subpolynomial growth is REDISCOVERED
  (WeilProducerReciprocalZeta); horizontal logarithmic potential control is REDISCOVERED
  (WeilFullConeHorizontalPotential); generic Pick/Stieltjes constraints are consequences
  of the parent Herglotz theory and do not alone advance the arithmetic detector.
- Positive working bridge: sharp sums of μλ are O(N^(1/2+ε)) for every ε>0,
  with no coefficient-bound premise. Corpus search found the smoothed theorem and
  a general sharp theorem requiring |b(n)|≤1. Neither supplies this exact statement.
  Verdict BRIDGE: classical Perron/short-smoothing mechanism, no claim of scientific
  novelty. It is useful because it removes an unpaid premise before attacking qλ.
- Complete paper argument: choose δ>0 and 0<a<q≤1 with δ+q≤ε and δ<1/2.
  Existing literal reciprocal G has |G(c+it)|≤K(2+|t|)^a on c=1/2+δ and
  the whole strip to 2. Shift the existing smooth Perron formula to c for cutoff
  smoothWeight(N,1/2). On integer arguments this is exactly 1 for 1≤n≤N,
  exactly 0 for n≥N+1; μλ(0)=0. The fractional Mellin bound costs
  ((N+1/2)/(1/2))^q (N+1/2)^c, hence O((N+1)^(c+q)), uniformly in N≥1.
  N=0 is zero. All imports and analytic admission are supplied by existing theorems.
  Thus no near-cutoff error and no bound on individual μλ(n) is needed.
- Next: formalize this exact bridge, then attack the qλ convolution estimate and
  distinguish ordinary cancellation from the necessary uniform twisted control.
- Sharp reciprocal estimate passed direct Lean audit. Added ordinary-series
  convergence and literal-reciprocal identification, including G(1)=0. Initial
  capstone compile needed one local-definition unfolding in the final indexing
  rewrite; targeted `lake build --old +...SharpReciprocal` is running.
- Wired only the new leaf into RHTower. Initial formal lint found our then-unwired
  leaf plus eight unrelated unwired modules; our import is now added. No unrelated
  source is changed to repair another work package's lint failures.

## Cycle 2 — Quotient mean-square contour and exceptional heights

- Conjecture: ordinary quotient sums qλ=1*μλ satisfy O(N^(1/2+ε)).
  The first hyperbola argument gave only exponent 2/3; that loss is not intrinsic.
- Corpus search located `ZetaVerticalMeanSquare.exists_integral_normSq_zeta_vertical_le`
  (actual namespace RHTower, source line 654). It is unconditional and uniform in
  σ∈[1/2,3], with dyadic bound CT(1+log T)^3. Search coverage was partial;
  the exact source was read and its hypotheses checked.
- Dependency-closed analytic proof recorded in PROOF.md: reciprocal t^a bound,
  dyadic ζ second moment and Cauchy–Schwarz give integrability of
  |ζG| |t|^(-1-q) for q>a>0; fractional Mellin decay then gives sharp qλ sums.
  Pole removal is the existing c*zetaEntire*exp(P), not a removable-singularity
  hypothesis. Lean formalization remains outstanding.
- Kill/novelty audit: this is a classical analytic BRIDGE, not novel science.
  The detector shortcut fails: translating the weighted integral by arbitrary t₀
  makes its constant depend on t₀. No averaging argument pays uniform boundedness.
- Anti-theatre/laziness: corpus gap narrowed, scientific frontier not yet moved.
  No step was deferred because of effort. Avoid multiplying easy corollaries;
  next research must confront exceptional-height control or an arithmetic rigidity
  mechanism that forces it. The main uniform twisted-sum conjecture stays OPEN.

## Strengthening forced by the reciprocal contour

- New exact theorem: for every ε>0, a single Cε works for all N and all real t:
  |Σ_{n≤N}μλ(n)n^(-it)|≤Cε(N+1)^(1/2+ε)(2+|t|)^ε. No exceptional set.
- Paper proof first: replace G(s) by G(s+it), twist the coefficients, and use
  2+|y+t|≤(2+|y|)(2+|t|). The previous Mellin bound is linear in its strip
  constant, so the complete height dependence is retained explicitly.
- Refactored the sharp theorem into this stronger theorem and its t=0 corollary;
  no duplicated contour proof, extra hypotheses, computations, or heartbeat raises.
- Targeted `--old` build passed. Ordinary convergence on Re s>1/2, literal G
  identification, and ordinary harmonic sum zero are in the same compiled leaf.
  Final direct audit and refreshed axiom audit pending.
- Scientific novelty remains unestablished. This is WP03's quantitative
  intermediate progress, not its bounded-quotient solution. The displayed height
  factor cannot be dropped by taking ε→0: constants depend on ε.
- Final verification: direct `lake env lean` leaf audit exit 0, no diagnostics;
  all five declarations audited in a /tmp import file, with only `propext`,
  `Classical.choice`, `Quot.sound`. Targeted `--old` build passed; umbrella import
  verified; indexes refreshed. Formal lint's seven remaining failures are other
  work's unwired modules, listed in EVIDENCE.md. No own Lean process remains.
- Continue with the quotient's actual weighted contour and the exceptional-height
  restriction. Do not mark the main detector complete or present BRIDGE status
  as significant scientific novelty.

## Cycle 3 — Formal quotient contour assembly

- Previous turn classified PROGRESS: all-height reciprocal theorem changed the
  authoritative Lean corpus and passed its audits. Main target remains unchanged.
- Revalidated WP03 target, current files and prior paper proof. New deep weighted
  zeta search was partial and did not supply the needed integrability bridge.
- Started owned leaf `WeilWorkSingularArithmeticWeightedZeta.lean`: a dyadic
  T log³T mass bound implies integrability against t^(-1-η), then specialize to
  the actual zeta norm using its unconditional second moment. Proof can use
  u≤1+u² in place of Cauchy–Schwarz; the extra log power is still summable.
- First Lean check found local elaboration issues (implicit exponent, `id`,
  rewriting rpow, explicit composition, and pointwise power). Corrected without
  changing the paper argument; second direct leaf check in progress.
- Next: reflect to negative heights and add the compact interval; combine with
  reciprocal subpower growth; apply fractional Mellin decay and pole-removed
  quotient Perron. No zero-free, uniform-height or coefficient-bound premise may
  be introduced to make this assembly pass.
- Weighted zeta admission now passed its targeted `--old` build: both rays and
  the compact interval are handled, and the full actual-line weight is
  (2+|t|)^(-1-η), for every η>0 and σ∈[1/2,3], σ≠1.
- Wrote `WeilWorkSingularArithmeticMellinMass.lean` and
  `WeilWorkSingularArithmeticQuotient.lean` from the closed paper proof.
  Mellin leaf is in its first targeted build; quotient assembly is not yet checked.
  The final quotient line uses c=1/2+q<1, so the weighted zeta pole exclusion is
  discharged, not added as an arithmetic premise.
- Quotient targeted `--old` build passed, with no diagnostic in the new leaf.
  Both the sharp qλ sum and ordinary Dirichlet convergence are now Lean proofs.
  Weighted-zeta and Mellin final direct audits passed without diagnostics.
  Quotient direct audit is running; nine-declaration axiom audit follows.
- Added the quotient umbrella import, reaching both analytic helper leaves.
  Formal lint reports nine unrelated unreachable modules and none of these
  leaves. Global whitespace check finds only unrelated docs/prompts.md edits.

## Cycle 4 — Square mass versus signed cancellation

- Exact next conjecture: for every hW : WeilPositiveFull lam and every ε>0,
  there is Cε≥0 such that Σ_{1≤n≤N}|qλ(n)|²≤Cε(N+1)^ε for every N,
  with the same literal qλ=1*μλ. No such bound is assumed in a Lean theorem.
- Why it matters: dyadic Cauchy–Schwarz would give absolute convergence of
  Σqλ(n)n^(-s) for every Re s>1/2. On each strict inner half-plane one can
  fix a smaller abscissa, obtaining the uniform bound required by WP03.
  The new content would be a nonlinear arithmetic restriction on full positivity,
  substantially stronger than ordinary cancellation or averaged vertical control.
- First attack: ordinary cancellation cannot imply this square-mass law.
  The alternating coefficients (-1)^(n+1) have bounded signed partial sums
  but square mass N. Their eta factor has a lattice of reciprocal zeros;
  this is NOT a full-positive counterexample. Thus the proof must retain the
  exact full-positive arithmetic structure, not merely the new sum estimate.
- Current primary-source audit: Brevig–Kouroupis–Perfekt, arXiv:2405.03522v2,
  gives explicit failures of interchanging boundary and vertical-mean limits,
  even for bounded Dirichlet series. Booker, arXiv:1308.3067v2, Definition1.3
  assumes coefficient square control and a discrete spectrum with only finitely
  many noninteger masses. Refinement after source reading: full positivity's
  existing dyadic mean-square theorem already gives subpolynomial square mass
  for lam(n)/sqrt(n). It gives no such law for qλ; the spectral conditions and
  other coefficient conditions still prevent a direct converse-theorem application.
- Preliminary verdict for the exact full-positive square law:
  SURVIVES PRELIMINARY ATTACK, not a proof or established novelty claim.
  Search coverage was partial for the nonlinear-convolution query. Parent
  theorems do not pay the missing estimate; no absence claim follows from search.
- [OPEN CORE]: derive a bound for the actual qλ square mass from the full Weil
  form, preserving all divisor interactions. Candidate algebraic handle is
  (log n)qλ(n)=Σ_{d|n}(Λ(d)−lam'(d))qλ(n/d), obtained formally by differentiating
  the literal quotient Dirichlet series in its absolute-convergence region.
  A coefficient-faithful quadratic test must retain the entire off-diagonal
  sum. Positivity alone gives no currently proved coercive bound for that sum.
- Competing possibility: a nontrivial full-positive system has positive-power
  qλ square mass. Such a system would refute this stronger law without by itself
  refuting WP03's bounded-quotient target. Search/kill this stronger law before
  formalizing any conditional receiver or routine algebraic corollary.
- First arithmetic attack found a sign obstruction: with c_n=qλ(n)/sqrt(n),
  the actual Toeplitz inequality gives 2E_N≥2I_Λ−(log N+C0)S_N, a LOWER bound
  for the logarithmic reciprocal energy. It cannot supply the required upper
  bound. Details retained in PROOF.md. The naive substitution strategy fails;
  the source square-law conjecture itself remains OPEN. Next: test a genuinely
  coupled use of the full Weil form, not a reversed one-sided inequality.
- Final cycle3 audits all passed: three direct leaf commands exit0 with no
  diagnostics; nine-public-declaration axiom audit exit0 with only propext,
  Classical.choice, Quot.sound. Index refresh exit0 and scoped whitespace exit0.
  Main detector remains unsolved; no goal completion is claimed.

## Cycle 4 continued — Absolute quotient regularity is an overshoot

- Previous goal turn: PROGRESS (three new audited Lean leaves and exact sign
  obstruction). Rechecked current owned sources/card; no own Lean process live.
- Re-read Bohr-route rows2,5,7 and current polarized/source mean-square theorems.
  They already distinguish uniform recurrence from mean recurrence: a fixed
  exceptional physical orbit is not controlled by almost-everywhere twist laws.
  Coupled spectral Cauchy–Schwarz is available, but it retains the source norms;
  it supplies no new upper bound for qλ square mass.
- New audit conclusion, paper level: absolute convergence of the actual quotient
  qλ at ANY real abscissa below1 already forces lam=Λ. Thus the proposed
  subpolynomial square-mass law is an arithmetic uniqueness claim stronger than
  the specified bounded-quotient detector, not a way around the regularity wall.
  Full proof and external dependency are recorded in PROOF.md below.
- Primary parent: Hewitt–Williamson's Dirichlet Wiener theorem as stated in
  Deutsch1974, AIF24(3), pp165–169, https://aif.centre-mersenne.org/item/10.5802/aif.524.pdf.
  An absolutely convergent ordinary Dirichlet series bounded away from zero on
  its half-plane has an absolutely convergent reciprocal there. Modern weighted
  versions remain current: Dabhi2026, https://articles.math.cas.cz/10.21136/MB.2026.0072-25.
  Their bounded-away-from-zero premise is discharged on strict inner half-planes
  by analytic almost periodicity and the quotient receiver; it is not assumed.
- Corpus's weighted Wiener algebra constructs the Banach algebra but the located
  code does not supply this inverse theorem. No unproved inverse statement has
  been imported into Lean. This classification is PAPER, not a Lean result.
- Verdict on the proposed way around the closed regular classes: REDISCOVERED
  regularity mechanism after inversion. The source square-mass conjecture itself
  is not refuted or proved. Do not spend a cycle building a conditional Wiener
  receiver and claim that it advances the required source bound.
- Hard question retained: can positivity control the actual convolution operator
  of qλ on weighted coefficient ℓ² for each x>1/2, without bounding its ℓ¹ norm?
  This is the multiplier form of the original target; merely restating it is
  not new science. A candidate proof must use a full-form identity with signed
  cross terms and a source-derived uniform constant. Neither the one-sided
  Toeplitz estimate nor mean-square/independent-twist estimates provide it.

## Cycle 5 — Actual quotient square mass at exponent one

- Exact candidate: for arbitrary hW and every ε>0,
  Σ_{1≤n≤N}|qλ(n)|²≤Cε(N+1)^(1+ε). This is weaker than cycle4's
  uniqueness-strength bound, but stronger than the pointwise bound obtained
  by differencing the existing sharp signed sums. No new source premise.
- Candidate mechanism: the actual G is subpower on strict inner strips;
  zeta's second moment therefore gives actual quotient mass Oη(T^(1+η)).
  Recover finite coefficient energy from finite-height Fourier tests, retaining
  the height loss and choosing height as a power of coefficient cutoff.
- First kill audit: this is a BRIDGE through classical Carlson/dual mean-value
  machinery, not yet a novel-science claim. It does not give bounded means
  or uniform quotient bounds. The corpus already has log-growth coefficient
  extraction in CarlsonHalfPlaneProducerFloor, but its log-growth premise does
  not hold for the quotient. Generalize the quantitative estimate only after
  closing its paper proof; do not silently reuse that premise.
- Alternative distribution proof: isolate log n frequencies with a compact
  bump at scale 1/N and use Plancherel against weighted actual-line mass.
  Its Fourier identification and global L² admission must be proved, not assumed.
- [OPEN CORE]: close the finite-height extraction with actual quotient growth,
  then reassess whether its coefficient consequence reveals a stronger structural
  restriction relevant to the remaining singular arithmetic class.
- Paper core closed by a shorter argument: integrate the ALREADY PROVED finite
  all-twist reciprocal polynomial for T=208(N+1); the mean-value lower bound
  yields reciprocal square mass Oε(N^(1+ε)). Divisor Cauchy–Schwarz and the
  exact convolution summatory identity yield the same quotient square mass.
  Full proof recorded in PROOF.md. New leaf SquareMass is in verification;
  neither an infinite mean limit nor a new Carlson theorem is required.
- Both square-mass theorems passed Lean. Removed unused-variable/tactic
  warnings; targeted `lake build --old +...SquareMass` then passed with a clean
  new leaf. Added its RHTower import. Direct final audit and axiom audit follow.
  Latest lint reports ten unrelated unreachable modules and none of these leaves.

## Cycle 6 candidate — sharp reciprocal obstruction

- Candidate source law: every full-positive literal reciprocal G is unbounded
  on every half-plane Re s>x with 1/2<x<1. Equivalently its abscissa of boundedness
  is exactly1, since absolute convergence gives boundedness for x>1.
- Mechanism: G=κ(s−1)exp(P(s)) has exactly one zero in Re s>1/2. A bounded
  Dirichlet continuation would be uniformly almost periodic on an inner strip
  containing1. A distant almost period and the minimum-modulus zero argument
  force a second zero, contradiction. No zeta zero-density theorem is needed.
- Expected positive survivor: μλ cannot have absolute convergence below1;
  together with cycle5 this makes the reciprocal square-energy exponent1 sharp
  for every hW, not merely for systems distinct from Λ.
- Kill audit underway. This is a classical Bohr mechanism, hence provisionally
  BRIDGE; do not call the source consequence new scientific knowledge without
  the current corpus/literature comparison. It does NOT obstruct bounded ζG:
  the zero at1 is canceled in that product. Uniform control of G itself is an
  invalid strengthening of WP03, even though each positive height exponent
  in its growth bound can be arbitrarily small.
- Current primary audit found this exact recurrence obstruction stated in
  Brevig–Kouroupis–Perfekt Section3, including the 1/ζ boundary example.
  Parent mechanism verdict REDISCOVERED; source application BRIDGE. A complete
  paper proof with all constants/domains is now in PROOF.md. Lean formalization
  of this positive sharpness statement is outstanding; do not declare it done.
- Wrote `WeilWorkSingularArithmeticReciprocalObstruction.lean` from the closed
  paper proof. Its source capstone supplies the literal reciprocal from hW
  alone and excludes every uniform half-plane bound for 1/2<x<1. Verification
  pending. SquareMass's final direct and axiom audits have now passed cleanly.

## Cycle 7 queued — actual quotient subpower conjecture

- Exact weaker source conjecture: arbitrary hW supplies the literal G and its
  pole-removed Q=ζG, and for every 1/2<x<1 and ε>0 there is C≥0 with
  |Q(σ+it)|≤C(2+|t|)^ε for every x≤σ≤2 and every real t.
- This is not established by the square-mass bound. The current proof supplies
  a polynomial quotient bound by multiplying reciprocal subpower growth with
  an unconditional zeta bound; the missing improvement is actual peak correlation.
- First kill tests: check whether the exact source law is already in the corpus;
  test any suggested proof against the one-sided Herglotz sign obstruction;
  compare any alleged generic upgrade to the reciprocal obstruction in cycle6.
  The latter shows that subpower growth alone cannot pay uniform boundedness.
- Deep initial search was partial and returned mostly irrelevant hits. Focused
  source search in WeilProducer leaves found reciprocal Lindelöf and the bounded
  quotient receiver, not the proposed source estimate. This is no absence proof.
- [OPEN CORE]: derive a source inequality coupling zeta peaks with the exact
  reciprocal, retaining signed divisor interactions. Separate upper bounds,
  mean-square coefficients, and generic independent twists do not pay it.
- Kill refinement from actual source reading: WeilPositiveProducerLindelof
  already bounds BOTH Fλ and 1/Fλ by arbitrary positive height powers. The
  local logarithm is identified with the same global G by
  eqOn_exp_neg_of_agree. Consequently, for every δ,ε>0 at large heights,
  (|t|+3)^(-ε)|ζ(σ+it)|≤|Q(σ+it)|≤(|t|+3)^ε|ζ(σ+it)| uniformly on the
  specified inner strip. Their polynomial growth exponents coincide.
- Thus the proposed subpower-Q law, under hW, is exactly the corresponding
  zeta Lindelöf law. The earlier interpretation as cancellation of polynomial
  zeta peaks was wrong: G cannot cancel those peaks by a fixed power of height.
  Verdict: REDISCOVERED growth question, not a new source-specific mechanism.
  The positive comparison law follows on paper from the existing two-sided
  producer bound. Do not assert an unproved Lean comparison theorem.
- Wrote the exact hW-only capstone in
  WeilWorkSingularArithmeticGrowthComparison.lean; it retains the literal G and
  the actual ζG value, includes zeta zeros without dividing by ζ, and compares
  both norms uniformly in σ at sufficiently large |t|. Not yet checked.

## Cycle 8 candidate under initial corpus audit

- Given the failed attempt to obtain a new route merely by changing height
  growth, ask a structural arithmetic question instead: does arbitrary full
  positivity force lam(n)=0 whenever n≥2 is not a prime power?
- This is a source conjecture, not an Euler-product premise added to a theorem.
  It is unproved and could fail for genuinely singular compensating systems.
  It would constrain the entire nonlinear reciprocal construction by forcing
  its logarithm onto the multiplicatively primitive frequencies.
- First kill checks: search the full corpus for an existing support theorem or
  counterexample; check whether finite matrix positivity already permits these
  frequencies; audit whether the proposed conclusion merely follows from a
  stronger currently proved uniqueness result. No Lean code until the paper
  argument is closed. Do not assume a Selberg Euler product from terminology.
- Direct source inspection found a strictly weaker existing result:
  WeilConeAsymptoticPrimeSupport.tendsto_nonprimeMass_div_log requires lam≥0
  and a nonprime coefficient envelope. WeilConeMultiplesOfPrimeLaw's semiprime
  floor exclusion also requires a sign condition. Neither gives exact support
  for the arbitrary mixed-sign cone assigned here. Read these premises literally.
- Potential use for the new source norm: test whether reciprocal/quotient
  square-mass control can replace the subcritical L¹ tail estimate in the
  existing multiplicative moment amplification. This is not yet an argument;
  inversion of q may reintroduce precisely the forbidden zero-free premise.

- Kill refinement: Bohr-route row80 already considered exact prime-power
  support and killed its Euler-product detection payoff at the absolute
  abscissa1 wall. Verdict on this proposed route: REDISCOVERED. That argument
  neither proves nor refutes exact source support. Row37′'s statement that
  composite support is possible was not accompanied by a located full-positive
  counterexample; do not promote the heuristic to a theorem. The useful
  surviving question is signed multiplicative interaction, not an assumed
  prime-supported Euler product.

## Cycle 6 final audit

- Narrowed the reciprocal-obstruction imports to the reciprocal producer,
  minimum-modulus zero lemma, and bounded-strip almost periodicity. Canceled
  the earlier broad build by its owned PID and verified exit before restarting.
- Targeted `lake build --old +...WeilWorkSingularArithmeticReciprocalObstruction`
  exit0. Final direct `lake env lean` leaf audit exit0, no diagnostics.
  Import-only public-theorem axiom audit exit0: only propext, Classical.choice,
  Quot.sound. Umbrella import added. No numerical computation or heartbeat hack.
- Sharp reciprocal boundedness obstruction is now Lean-proved. The proposed
  absolute-abscissa and square-energy sharpness corollaries remain paper-only.
  No endpoint x=1 claim. Main bounded-product detector remains open.

## Cycle 9 — arithmetic operator audit

- The broad singular-arithmetic deep search completed with full inventory
  coverage but mostly irrelevant ranked hits and largely source-only compiler
  metadata. Focused source reads found the full dyadic lambda square bound
  and the exact multiplicative Toeplitz upper bound.
- Reassess the signed operator, rather than infer a uniform multiplier from
  coefficient norms. The proposed replacement of log N by a coefficientwise
  log n diagonal is dangerous: the formal producer recurrence makes that
  diagonal act like the one-sided convolution on producer coefficients.
  Its adjoint then doubles the energy. Any claimed bound must retain the
  finite-cutoff boundary and its exact factor; suppressing it would even
  contradict the von Mangoldt model. This is a kill test, not a proved source
  improvement. Focused corpus search and primary operator-theory audit follow.

- Focused search again supplies the existing one-sided Toeplitz bound; the
  strongest located primitive-set consequence is already in WeilPrimitiveSetMeanSquare.
  No new signed operator estimate was obtained. Do not mistake the hW premise
  for an order relation between the lambda and von Mangoldt operators.

## Cycle 7 completed

- GrowthComparison targeted --old build, final direct leaf audit, and axiom
  audit all exit0. Public capstone uses only the three standard axioms. Import
  wired; index refreshed. Final lint has seven unrelated unreachable modules.
- Anti-theatre: cycles6–7 are BRIDGES/REDISCOVERED parent mechanisms, not
  significant new science. They prevent invalid strengthenings of the target.
  Source boundedness of ζG is unchanged. No proof step was skipped for effort.

## Cycle 10 — actual mean recurrence, current literature check

- Exact generic proposal: an ordinary Dirichlet series with square-summable
  coefficients and ordinary convergence in Re s>0 has its coefficient mean
  square on every Re s>0. Verdict FALSE: Brevig–Kouroupis28Sep2026, Theorem6,
  supplies a theta=0 counterexample with mean abscissa1/4. Primary record and
  proof read at https://arxiv.org/html/2609.35496v1. This is not a counterexample
  to the additional full-positive source constraints.
- Their order-zero replacement is a valid positive survivor. Applied after
  shifting G by any fixed real a>1/2, cycle5 supplies H² coefficients and the
  corpus supplies order zero. Thus G has the expected actual-line mean square
  on Re s>1/2. This is PAPER, not yet a Lean theorem. A direct proof using the
  already formal all-twist sharp sums and finite mean-value bound is recorded
  below in PROOF.md; it avoids importing any new analytic theorem as an axiom.
- Even that mean identity cannot make G uniformly bounded: cycle6 excludes
  boundedness across1. For the quotient, the order-zero premise is exactly
  the unproved zeta subpower question by cycle7. No Carlson inference is free.
- Bohr-route rows4,7 already kill passage from generic mean recurrence to the
  actual exceptional orbit. Positive-density recurrence conditioned on finite
  prime alignment still needs a tail estimate relative to the alignment's
  shrinking density. The present coefficient norms give no such estimate.

## Cycle 11 — coefficient concentration candidate

- Exact new source conjecture under audit: for every hW and ε>0, some Cε
  bounds |mu_lambda(n)|≤Cε*n^ε for all n≥1. This is a conjecture about the
  literal reciprocal coefficients, with no added Euler product or Ramanujan
  premise. It would remove rare square-root-size coefficient spikes that
  cycle5's aggregate bound allows. It does not itself pay the detector.
- Competing possibility: full positivity permits such spikes while forcing
  compensation across dense multiplicative correlations. A counterexample
  must carry full positivity; arbitrary Dirichlet-series examples do not suffice.
- First [OPEN CORE]: derive an individual coefficient bound stronger than
  n^(1/2+ε) from the complete source form, or exhibit a mechanism consistent
  with that form that prevents the improvement. Check the corpus before code;
  no fresh Lean leaf is justified until the exact paper proof closes.
- Focused reciprocal-Ramanujan deep search completed (partial=false) and
  returned the reciprocal definition/identity, existing cancellation, and the
  bounded-quotient prime consequence. It did not locate the conjectured
  individual bound; candidate applicability remains source-checked rather than
  compiler-certified by the search index. Direct Weil-source search agrees.
- Primary comparison: Banks2017, https://hrj.episciences.org/4027/pdf,
  Theorem2.1 assumes bounded original coefficients and k-free inverse support,
  proving nonvanishing only on Re s>1. Neither hypothesis has been derived
  for the arbitrary producer, so it cannot settle the present conjecture.
- Next concrete work: formalize cycle10's closed source mean proof, then audit
  whether excluding coefficient spikes requires a new full-form inequality.
  Keep the source conjecture and its negation live; no coefficient hypothesis
  may be inserted into an allegedly unconditional capstone.

### Cycle 10 formalization checkpoint

- New reciprocal uniform-tail capstone compiled under `lake build --old` and
  passed a direct `lake env lean` audit. Three unnecessary-sequencing warnings
  were removed afterward; final re-audit pending. Literal G, every alpha>1/2,
  every epsilon>0, and every sigma>alpha occur in one theorem. Bound:
  K*(2+|t|)^epsilon*(N+1)^(alpha-sigma). No added coefficient premise.
- Weighted square summability for reciprocal and quotient is written from
  cycle5's source square mass and mathlib's summatory L-series theorem.
  Targeted compilation currently running. Actual reciprocal mean limit still
  PAPER; it is not implied merely by those summability theorems.
- Mean comparison simplified on paper: both actual G and finite approximants
  have subpower height bounds, so their squared-norm difference tends uniformly
  to zero for N=floor(sqrt(T))+1. No integral Cauchy–Schwarz is needed.
- Current deep tail search completed with partial=false and full inventory
  coverage. Most returned candidates have source-only compiler metadata and
  mismatched hypotheses; no candidate settled the actual mean-limit gap.
- Weighted square summability target build passed, no leaf warnings. The
  reciprocal tail also rebuilt successfully after its warning cleanup.
- MeanComparison now contains the finite mean error and its vanishing for
  N=floor(sqrt(T)). Its first checks exposed only continuity elaboration and
  rewrite/index details; those have been repaired, pending the next build.
- ReciprocalMeanSquare is written: finite negative-time Montgomery–Vaughan,
  square-root cutoff, exact ordinary-series/polynomial identity, then the
  source capstone. Targeted build currently running. Do not call the mean
  law formal until this and direct leaf/axiom audits pass.

### Cycle 12: recurrence tail audit (no new theorem claimed)

- Rechecked the proposal that finite-prime recurrence plus small mean tails
  could force recurrence of the actual reciprocal near its zero at1.
  Deep search completed partial=false; a narrower lexical search returned
  no declarations. Direct source reading found the obstruction already in
  Bohr-route rows4,7: the alignment density can decay faster than the tail
  estimate. This is REDISCOVERED, not a full-cone counterexample.
- The ordinary-series mean formula is the positive survivor being closed in
  cycle10. Do not retire that no-go with its formalization still outstanding.
- Big-picture correction: means can coexist with the unique zero at1 and
  unbounded reciprocal values. A new detector argument must constrain the
  actual exceptional orbit, or derive an arithmetic comparison with Lambda;
  replacing the target by another averaged bound does not close WP03.

### Cycle 13: reciprocal Ramanujan rigidity candidate

- Exact conjecture under audit: every full-positive lambda either equals
  Lambda for n>=2, or there exists c in (0,1/2) such that, for every C>0,
  some n>=1 satisfies |mu_lambda(n)|>C*n^c. Equivalently, subpolynomial
  pointwise growth of the literal reciprocal coefficients would force Lambda.
- This is separate from cycle11, which conjectures that positivity supplies
  that pointwise growth for all producers. Their conjunction would close
  detection. Neither statement is proved or inserted as a premise in Lean.
- [OPEN CORE]: rule out a nontrivial dense mixed deviation while only knowing
  reciprocal Ramanujan growth. The existing finite-type theorem instead
  assumes regular continuation across the critical line; it does not supply
  this step. Subcritical absolute deviation summability is not assumed here.
- First broad deep search finished partial=false but many Ramanujan hits
  concerned Ramanujan sums rather than coefficient growth. A mechanism-focused
  Weil search is running; no absence or novelty conclusion from those hits.
- Primary converse-theorem audit: Ki–Lee2011 and Kaczorowski–Perelli2015
  assume global continuation and a functional equation, with extra Euler
  structure for the Selberg class. Those hypotheses are not consequences of
  the pointwise reciprocal bound currently under consideration. They cannot
  be imported to prove this candidate.
- Diagnostic under consideration for cycle11: multiply G by exp(H), where H
  is an absolutely convergent lacunary prime series on Re s>1/2, to preserve
  its analytic estimates while altering prime coefficients. The prime formula
  follows from the source `dirichletExp_prime` proof. This is not a full-positive
  counterexample; preserving full positivity is precisely an unproved step.
  Do not claim the source conjecture false on this basis.
- Focused growth-to-Lambda search completed partial=false. Returned regular
  continuation, atomic-mass, and phase-lock receivers do not derive those
  hypotheses from reciprocal coefficient growth. The constant-sign theorem
  additionally needs ordinary convergence of the deviation error on every
  point of the critical line. Neither cycle10's fixed interior means nor the
  reciprocal Ramanujan conjecture supplies that premise. Provisional verdict
  for cycle13: SURVIVES PRELIMINARY ATTACK, with the stated open core intact;
  no scientific novelty claim yet.
- Next representation checked against `DirichletConvolutionExponential`:
  for a finite set S of distinct primes and P_B=product_(p in B)p, the finite
  convolution definition gives

      mu_lambda(P_S) = sum_(partitions pi of S)
        product_(B in pi) (-lambda(P_B)/log(P_B)).

  Reason: the k-th convolution power is a sum over ordered partitions, and
  division by k! removes their orderings. For empty S the empty partition
  gives1. This is the classical exponential formula, a representation bridge,
  not a new research theorem. Search returned the convolution definition and
  unrelated partition results; no applicable source inequality was located.
  The hard step is a full-positivity bound on these signed partition sums.
  Taking absolute values loses their arithmetic cancellations and is not a proof.

### Cycle 10 completed formal checkpoint

- ReciprocalTail, SquareSummability, MeanComparison, ReciprocalMeanSquare:
  targeted `--old` builds and all four final direct `lake env lean` audits
  passed. Six public capstones have only standard axioms. The separate
  scratch API probe needed explicit universe levels, then exited0 too.
- The exact actual reciprocal mean identity is now LEAN, for every fixed
  sigma>1/2. Both coefficient energies are finite at every such sigma.
  The ordinary uniform tail and the square-root-cutoff mean approximation
  are also public capstones. All four leaves are wired; no umbrella build.
- Latest lint fails only on seven unrelated unreachable modules (listed in
  EVIDENCE.md). No owned source failure, extra hypothesis, numerical job,
  heartbeat override, or unproved claim is hidden in this checkpoint.
- Cycle12's positive mean-law survivor is complete. Classification BRIDGE;
  mean control still does not constrain the actual exceptional quotient orbit.
  The detector and cycles11/13 remain open. Next research targets the full
  arithmetic form and signed multiplicative coefficient correlations, rather
  than another generic mean or continuation lemma.

### Next coefficient test: retain the first nonlinear cancellation

- Cycle11's prime-square consequence, stated exactly for diagnosis: for every
  full-positive lambda and epsilon>0 there is C>=0 such that, for every prime p,

      |lambda(p)^2/log(p)^2 - lambda(p^2)/log(p)| <= C*p^epsilon.

  The left side is twice |mu_lambda(p^2)|: only the one-block and two-block
  terms survive in the finite Dirichlet exponential. This is an unproved
  necessary subcase of cycle11, not a distinct claimed scientific advance.
  A proof must force cancellation between the two displayed signed terms.
  Neither termwise absolute bounds nor a theorem assuming multiplicativity
  of mu_lambda may be substituted for this source claim.
- The precise three-point Toeplitz test does not pay it. Set
  a=lambda(p)/sqrt(p), b=lambda(p^2)/p and B=2log(p)+C0>0. Testing the actual
  upper bound on coefficients (1,t,1) supported at (1,p,p^2) gives
  4at+2b<=B(2+t^2). Taking t=2a/B yields b<=B-2a^2/B.
  This is an upper bound for b, whereas the desired cancellation requires
  two-sided proximity to a^2/log(p). The missing direction is explicit.
  This repeats the earlier one-sided sign obstruction, now at the first
  nonlinear coefficient; do not count it as a new no-go theorem.
- Latest full-form/multiplicative-correlation search completed partial=false.
  Inventory coverage was complete, but its coverage snapshot was one generation
  old, semantic coverage unavailable, and candidate compiler metadata mostly
  source-only. All returned candidate and argument signatures were inspected.
  The generated suggestion `WeilPositiveFull -> RH` dropped the actual
  nonnegativity and coefficient-order premises of `...of_le`; it is inapplicable.
  No conclusion of absence or novelty follows from this search.
- Brevig–Perfekt–Seip, arXiv:1602.04729, Theorem5.1, requires a Carleson
  inequality for all Hardy-space tests to infer Volterra boundedness. The
  present one-sided Toeplitz estimate is not that inequality. Booker's
  discrete-spectrum assumptions were rechecked and remain unproved here.
- Index refresh completed after the cycle10 audits (exit0); generated API,
  gaps and overview files have no Git diff. Owned whitespace check passed.
- Honest assessment: cycle10 closes a known analytic bridge, not the scientific
  detection frontier. Cycles11/13 and the prime-square cancellation test remain
  conjectures. No step was rejected for effort. The next proof effort must
  obtain a new constraint from full arithmetic positivity, preserving signed
  divisor interactions, rather than repeat mean-value or operator membership
  arguments whose additional premise is exactly the open problem.

## Cycles 15--19: premise audit and regular-perturbation diagnostic

- Venturini's 2020 nonvanishing theorem applies to bounded completely
  multiplicative coefficients. Reciprocal coefficients do not have that
  property even for Lambda. Multiplication by zeta(2s) repairs the classical
  example, but not a general producer. If its new coefficients b were real,
  bounded and completely multiplicative, the Euler logarithm would force
  lambda(p^k)=(2*1_(2 divides k)-b(p)^k)*log p and zero elsewhere.
  Positive deviation then lies on even powers and is summable below1.
  Existing one-sided rigidity already closes this proper subclass. Verdict:
  REDISCOVERED subclass receiver, not a new detection argument.
- Cycle17's sparse-prime perturbation argument is now explicit in PROOF.md.
  A uniform positive full-form margin would permit reciprocal prime spikes
  p^a, 0<a<1/2, while bounded exp(H) and exp(-H) preserve the exact quotient
  target. Margin existence remains OPEN (HF L74). No actual full-positive
  counterexample, no source theorem with an added margin premise, and no
  retirement of cycles11/13 is claimed. Diagnostic classification: BRIDGE.
- Full-form definition and perturbation-symbol norm bound were checked in
  source. Literal-zeta insertion/deletion operator theorems were not silently
  transferred to arbitrary lambda. The HF L324 evaporator proposal is killed
  by its L325 coefficient/function-limit mismatch and is not a counterexample.
- Spectral-deficit and determinant queries supplied no applicable new bound.
  Generated suggestions again omitted coefficient-order premises; rejected.
  General Hamburger/Burnol receivers still require meromorphic continuation
  and a functional equation absent here. Do not replace the WP03 problem by
  those stronger assumptions.

## Cycle 20: exact forward-energy substitution

- Source sequence: a_lambda=dirichletExp(logZetaCoeff(truncate lambda)), the
  coefficients of exp(L), not producerMobius. Exact paper claim:
  sum_(1<=n<=N)|a_lambda(n)|^2/n <= K_lambda*(1+log N).
- Mechanism: D a=lambda*a. Test the actual multiplicative Toeplitz ceiling
  with c_n=a(n)/sqrt(n), truncated at N. Its signed convolution becomes
  2 sum log(n)|a(n)|^2/n exactly. The resulting logarithmic-moment inequality
  gives O(log N) by an explicit absolutely-continuous Gronwall argument.
  Full dependency-closed proof is in PROOF.md. The owned forward-coefficient
  leaf passed its targeted --old build, final direct Lean audit and all
  seven standard-axiom checks; import wired.
- This changes the sign failure of the reciprocal test by choosing forward
  coefficients. No extra producer property is assumed. Corpus searches and
  exhaustive relevant text search located the parent bound and exponential
  identity, but not this exact consequence. Search limitations are recorded;
  absence and scientific novelty are not inferred. Verdict: BRIDGE.
- Next stronger conjecture: with r_lambda the positive residue of exp(L) at1,
  sum_(n<=N)|a_lambda(n)-r_lambda|^2/n=o(log N). It would impose coefficient
  concentration at the pole mode; falsity would expose residual logarithmic
  energy beyond that mode. [OPEN CORE]: force the sharp leading constant,
  not merely O(log N). Neither Gronwall nor a mean-value theorem does this.
- Working plan: formalize the exact logarithmic convolution and finite energy
  inequality, then the closed O(log N) proof; audit the variance conjecture
  against the full form and existing source results. Detector remains OPEN.

## Cycle 21 candidate: fractional coefficient energy, stable under regular changes

- Exact selected conjecture: for arbitrary full-positive lambda, put
  a_half=dirichletExp((1/2)*logZetaCoeff(truncate lambda)). There exists
  K_lambda>=0 such that for every N>=1,

      sum_(n<=N)|a_half(n)|^2/n <= K_lambda*(1+log N)^(1/4).

- Why this representation: the exponent class survives multiplication by
  exp(H) when H has absolutely summable coefficients at1/2. Weighted
  convolution Young bounds, in both directions using exp(-H), prove that
  stability. Cycle17's sparse regular perturbation does not destroy it.
  The competing pole-mode variance conjecture from cycle20 stays open;
  neither candidate has been used as a premise in Lean.
- The directly available ceiling is weaker: for real 0<z<2, the same
  coefficient substitution gives (2/z) sum log(n)|a_z(n)|^2/n <=
  (log N+C)E_z(N). Its continuous Gronwall argument gives exponent
  z/(2-z), hence1/3 at z=1/2. Improving1/3 to1/4 is [OPEN CORE].
  This is a prospective proof of the weaker bound, not a completed Lean result.
- Literature calibration: Hough, *The angle of large values of L-functions*,
  JNT167(2016), Lemma6 equation36, contains the logarithmic1/4 law for the
  classical half-divisor coefficients (take both shifts equal1). Its proof
  uses their multiplicative structure. Mastrostefano's generalized-divisor
  framework also assumes multiplicativity and a divisor-function majorant.
  Neither is an all-full-positive-source theorem. The novelty, if proved,
  must be the source transfer without those assumptions, not exponent1/4.
- Deep search was partial after a Qdrant semantic deadline. All returned
  candidate/argument statements were reviewed; none supplied that transfer.
  The radial-Mellin source hit already has the forward exponential identity,
  but no critical coefficient-energy bound. Its exact statement was checked.
  Provisional verdict: SURVIVES PRELIMINARY ATTACK, no novelty claim yet.

## Cycles 22--23: fractional-energy and prime-variance audits

- A further deep fractional-energy search returned a suggested double-square-
  root argument. Its scalar power identity has no connection to the requested
  coefficient norm; rejected. Full candidate and source-argument statements
  were reviewed. A broader source query found WeilConeSoundararajanMoments:
  its sharp quadratic moment exponent assumes both a logarithmic coefficient
  bound and summable rest weight. Neither follows from our current proof.
- Primary exponentiation checks: Ponnusamy--Sugawa2019 assumes normalized
  univalence for its logarithmic coefficient bounds. Chang--Gui2021, equation
  (2.1), bounds an exponential's circle norm by the weighted square norm of
  its logarithm. No corresponding prime-polydisc norm has been proved for
  the present source. These are calibration results, not all-source receivers.
- Cycle23's first proposed test, c=delta_1+t sum_(p<=N)lambda(p)/sqrt(p) delta_p,
  is exactly WeilMeanSquare.exists_sum_sq_prime_div_le. Source inspected at
  WeilPrimitiveSetMeanSquare:284. Verdict REDISCOVERED; no duplicate Lean.
- Next exact candidate (unproved): for each full-positive lambda and every
  epsilon>0, eventually

      sum_(p<=N) lambda(p)^2/p <= (1/2+epsilon)*(log N)^2.

  Existing all-source coefficient is1; the corpus records1/2 for Lambda.
  [OPEN CORE]: remove the factor-two loss by using coupled multiplicative
  tests while retaining arbitrary signed composite weights. Dropping those
  composite terms, imposing an Euler product, or importing the conditional
  moment theorem would add an unproved premise. The half-power1/4 conjecture
  remains open; a prime bound alone would still leave composite interactions.
- Research relevance check: neither proposed energy improvement alone pays
  the uniform quotient receiver. Their intended contribution is a new
  restriction on singular arithmetic correlations, not another claim that
  an averaged norm controls the exceptional untwisted orbit.

### Cycle24 attack on the proposed two-prime improvement

- Exact finite diagnostic: restrict the divisor matrix to (1,p,q,pq), put
  a=lambda(p)/sqrt(p), b=lambda(q)/sqrt(q), u=sqrt(a^2+b^2), and choose the
  composite entry c=lambda(pq)/sqrt(pq)=-2ab/u (zero when u=0).
  For every real vector (x0,xp,xq,xpq), the budget-u defect, multiplied by u,
  is exactly

      (u*xp-a*x0-b*xpq)^2 + (u*xq-b*x0-a*xpq)^2.

  The coefficients of the unscaled defect are u on its diagonal, -2a on
  (0,p),(q,pq), -2b on (0,q),(p,pq), and -2c on (0,pq).
  Thus the full four-point ceiling holds, and (u,a,b,0) saturates it.
  Arbitrary signed composite compensation can therefore attain the star
  threshold sqrt(a^2+b^2) even after this particular extra divisor is kept.
- This is an algebraic Schur-complement calibration, not a full-positive
  arithmetic source. It invalidates a local two-prime proof of a strict
  improvement; it does not refute cycle23's all-scale conjecture or retire
  the full route. A successful improvement must couple additional indices
  or use compatibility of the same source across scales. Corpus and primary
  audits classify this as BRIDGE (classical Schur completion). Its exact
  square decomposition, iff classification and star equality now have
  complete Lean proofs in WeilWorkSingularArithmeticDivisorCompletion.
  Targeted --old build, final direct audit and three standard-axiom checks
  passed; import wired. No full-source counterexample is asserted.

### Cycle25 candidate: compatibility on the next divisor layer

- Exact next finite question: for three nonzero prime entries a,b,d, can
  one source attain the star ceiling u=sqrt(a^2+b^2+d^2) on
  (1,p,q,r,pq,pr,qr)? Conjecture: no, regardless of the three composite entries.
- Proposed mechanism: at equality the star null vector forces
  c_ij=-2a_i*a_j/u. After eliminating the three singleton coordinates,
  the residual matrix on the three pair coordinates has diagonal
  a_k^2/u and off-diagonal -a_k*a_l/u (complementary indices). Scaling by
  the nonzero a_k gives 2I-J, which has a negative all-ones direction.
  Thus the pairwise repairs cannot all attain the star threshold together.
  Corpus audit found generic Schur identities; the exact arithmetic source
  transfer and its quantitative value remain under investigation.
- More useful quantitative candidate: the singleton-to-pair block R obeys
  R^T R=S*I+a*a^T-2*diag(a_i^2), S=sum a_i^2. Restricting to these two
  layers removes arbitrary composite entries entirely. Any full ceiling B
  must dominate the norm of R. For k equal prime entries, its squared norm
  is (2k-2)*a^2 versus the star's k*a^2.
- Cutoff cost is essential: retaining pairs of primes up to X requires
  cutoff X^2, so the Weil ceiling doubles from log X to2log X. The displayed
  square-root-two gain alone therefore does NOT improve cycle23. Next work
  must retain the actual product cutoff pq<=N and optimize nonuniform
  prime layers. No source bound or detector closure is claimed.

### Complete formal checkpoint for cycles20 and24

- ForwardCoefficients and DivisorCompletion: targeted --old builds, final
  direct lake env lean checks, and all ten public axiom checks passed.
  Both leaves wired, no umbrella build, no numerical job or heartbeat hack.
- Cycle20's all-source critical energy O(log N) is LEAN. Cycle24's exact
  finite composite compensation is LEAN. Both are BRIDGE, not claimed
  significant scientific novelty or detector closure.
- Latest lint fails only on16 unrelated unreachable leaves (EVIDENCE.md).
  Cycle25 prime-layer source reindexing is next. Keep the product cutoff;
  arbitrary composite terms must disappear by support, never by dropping
  their signs. Cycles21/23 and WP03 remain open.

### Cycle27: sharpness of the entire Toeplitz relaxation

- Current turn: continued hgtl7; previous turn classified PROGRESS. Exact
  detector still open. Cycles25/26 tested the product cutoff and whether
  zero-free coefficient energy forces Gaussian prime variance. Neither
  supplied the missing implication. Do not formalize a continuum toy model
  while ignoring the stronger all-cutoff attack below.
- Conjecture under attack: the entire family of multiplicative Toeplitz
  ceilings, with budget log N, forces eventual prime-square constant<1.
  Paper verdict FALSE. Positive survivor: one explicit nonnegative,
  prime-supported weight system satisfies every ceiling with C=0 while its
  normalized prime spikes approach1. This does not assert Weil positivity.
- Construction: choose increasing primes p_j so that, writing L_j=log p_j,
  2*(j+2)*sum_(i<j)L_i <= L_j. Put b_j=(j+1)/(j+2)*L_j and
  lambda(p_j)=sqrt(p_j)*b_j, with lambda zero elsewhere. Choose successive
  primes beyond p_j^[2*(j+1)*(j+3)] to obtain the required separation.
- All-cutoff proof: let p_j be the last selected prime<=N. Earlier shift
  forms cost at most2*sum_(i<j)b_i. If N<p_j^2, the p_j shift is a matching,
  costing b_j, so total<=L_j<=log N. If N>=p_j^2, all shifts cost at most
  2*sum_(i<=j)b_i<=2*L_j<=log N. Every complex test vector is retained.
  At N=p_j the single prime contributes ((j+1)/(j+2))^2*(log N)^2.
  Thus no asymptotic constant<1 follows from all Toeplitz ceilings alone.
- Plan: (1) finish corpus/primary novelty audit, (2) formalize the exact
  all-cutoff construction and sharpness, (3) leaf build/direct/axiom/lint
  audits, (4) pivot to source information lost by the Toeplitz relaxation.
  Classical shift bounds are BRIDGE; the arithmetic relaxation barrier is
  SURVIVES PRELIMINARY ATTACK, pending Lean and wider novelty assessment.

### Cycle27 complete; next source-level conjecture

- LEAN CLOSED: WeilWorkSingularArithmeticToeplitzSharpness constructs one
  nonnegative prime-supported lambda satisfying all logarithmic Toeplitz
  ceilings with C=0. Square mass<=log^2 N at every cutoff, yet every
  smaller constant is exceeded by prime mass arbitrarily far out.
  Exact infinite positive survivor, not just a finite negative example.
- Targeted --old build, final direct leaf audit, six public standard-axiom
  checks passed. Umbrella import wired. Lint:18 unrelated unwired leaves,
  no WP03 failure. No full build, numerical job, raised heartbeat or
  overlapping Lean process. Failed subroute card records closure.
- Verdict: the Toeplitz-only inference in cycle23 is FALSE. Its sharpness
  construction is a new corpus barrier using classical methods; scientific
  novelty is not established. The conjecture from full Weil positivity
  remains OPEN, as do cycle21 and the exact WP03 receiver.
- Anti-theatre: an all-cutoff relaxation witness is not a full-positive
  counterexample. Anti-laziness: the same infinite sequence handles every
  cutoff and complex test, and the sharp positive survivor is formalized.
  Stop spending cycles optimizing divisor layers inside this relaxation.
- Next competing candidates: (i) full-source normalized prime spikes tend
  to zero; (ii) signed full-source local harmonic variation is bounded;
  (iii) the previously open half-power exponent1/4. Candidate(ii) retains
  source information that the Toeplitz estimate discards and has an exact
  existing nonnegative-source theorem to attack. Candidate(i) alone would
  not give a summed prime bound; candidate(iii) still lacks a composite
  cancellation mechanism. None is asserted proved.
- Cycle28 exact conjecture: for every hW:WeilPositiveFull lambda, there is
  M>=0 such that, for every Z>=1 and finite cutoff N1,

      sum_(n<N1, |log n-Z|<=1/2) |coneDeviation lambda n|/n <= M.

  In existing notation: exists M>=0,
  WeilAbscissa.LocalMassBounded (WeilOneSided.coneDeviation lambda) M.
  Read source: WeilDeviationLocalMass:584 proves this with lambda(n)>=0;
  exhaustive source search found only that producer and conditional uses.
  [OPEN CORE]: bound the negative part without adding a sign/size premise;
  signed profile-window cancellation alone does not bound total variation.
  This would strengthen the all-source local estimate from O(Z) to O(1)
  and unlock the existing bounded harmonic-sum receiver
  `WeilConeMultiplesOfPrimeLaw.exists_abs_sum_coneDeviation_div_le`.
  Correction: the convergence receiver in
  `WeilLittleODeviationHarmonicConvergence:369` needs local mass tending
  to zero, not merely bounded local mass. It is
  not yet the uniform quotient detector. Novelty/kill audit is unfinished.

### Cycle29: sharp summatory law without a sign premise

- C28 remains open. Corrected its receiver: bounded local mass gives bounded
  harmonic sums; convergence requires vanishing local mass in the cited theorem.
- Competing C29 targets: (a) signed local total variation O(1), still missing
  negative-part control; (b) sharp summatory law
  |sum_(2<=n<=N) lambda(n)-N| <= C_epsilon (N+1)^(1/2+epsilon);
  (c) ordinary convergence of sum (lambda-Lambda)/n. Choose (b), then (c).
- Corpus: deep summatory and Perron searches both partial (semantic/reranking
  deadlines); inventoried files complete, compiler coverage mostly source-only,
  background refresh active. Candidate and source-argument signatures checked.
  Existing sharp reciprocal module already supplies the integer-gap technique;
  `WeilPositiveProducerLindelof.norm_regularPart_le_of_re_ge` supplies the
  stronger logarithmic bound for the actual source's regular part.
- Paper mechanism: R=A-Phi is holomorphic on Re s>1/2 and
  D_lambda=1/(s-1)+R on Re s>1. On every strict inner half-plane R=O(log(3+|t|)).
  Use smoothWeight N (1/2), exactly equal to the sharp cutoff on integers.
  Absolute Dirichlet convergence gives Perron on Re s=2. Fubini plus Mellin
  inversion identifies the pole contribution with integral_1^infinity w(x) dx,
  lying between N-1 and N-1/2 for N>=1. Shift the R contribution to
  c=1/2+q, q=min(epsilon/4,1/4), and dominate log height by height^(q/2).
  Existing fractional Mellin bound costs N^q, hence error O(N^(1/2+epsilon)).
  Absolute interchange follows from x^-2 times the integrable Mellin transform.
  Horizontal edges vanish by rapid Mellin decay. No positivity of lambda used.
- Abel summation then gives a limit of sum lambda(n)/n-log N, since an error
  O(N^(1/2+epsilon)), epsilon<1/2, is integrable against N^-2. Classical PNT
  gives the corresponding Lambda limit, hence ordinary deviation convergence.
- Verdict: BRIDGE, apparently missing source consequence in searched corpus;
  no publication novelty claim. Primary comparison: de Roton--Revesz,
  arXiv:1210.2284, explains why signed Tauberian arguments need additional
  control. Here the control is derived from the source, not assumed.
- Anti-theatre: neither summatory cancellation nor harmonic convergence bounds
  the quotient uniformly in height. Exact WP03 still open.
- Anti-laziness: pursue the sharp half-power law; no sign, size, local-mass,
  Tauberian slow-decrease, or numerical premise will replace an unproved step.
- Plan: prove pole Mellin identity; assemble source sharp law; derive harmonic
  convergence; direct leaf/axiom audits, umbrella import, lint; resume detector.

### Cycle29 implementation checkpoint

- Two owned leaves written: PolePerron (121 lines) and Summatory (263 lines).
  Pole Fubini and continuous main term are proved; the summatory leaf proves
  the source half-power error, centered ordinary Dirichlet convergence on
  Re s>1/2, and plain deviation harmonic convergence. Every source premise
  comes from hW alone. No sign or local-mass premise remains.
- Full scratch-file check passed with the exact source and mathlib API probes.
  Targeted --old builds passed; only the new leaves were compiled (dependency
  diagnostics replayed). New leaves imported by RHTower. No umbrella build.
  Both final direct `lake env lean` checks passed without diagnostics. All five
  public declarations use only propext, Classical.choice, and Quot.sound.
  Lint found eight unrelated unreachable leaves, no owned or forbidden
  declaration error. Index refresh passed; generated documentation unchanged.

### Cycle30 candidate selection

- C29 addresses signed cancellation, not absolute variation. C28 (bounded
  absolute local mass) remains open. The existing harmonic sign receiver
  WeilConeHarmonicPinning:224 still requires NotchSmall. Its four fields in
  PrimeSmallDeviationArithmetic:177 include three absolute-mass estimates.
  C29 does not prove those fields.
- Competing targets: (a) remove NotchSmall from the untwisted harmonic sign
  law; (b) prove all gcd-twisted harmonic sums converge; (c) signed control
  of the full arithmetic notch error. Choose (a) as the next falsifiable
  source statement, with (c) the intended mechanism. (b) needs new fibre
  information not supplied by ordinary unweighted partial sums.
- Exact conjecture: for every hW:WeilPositiveFull lambda and every real T,
  if sum_(n<N) coneDeviation(lambda,n)/n tends to T, then T<=0.
  C29 now supplies convergence; the conjectural content is only the sign.
  It is not asserted proved and would not alone solve WP03.
- The actual kernel is ZetaNotch.weightedMoment L 1 (log n), an integral of
  notchWindow L t * |zeta(1/2+it)|^2 * exp(-it log n). Current refined
  envelopes bound each coefficient error absolutely by refWeight, whose
  leading term is L/sqrt(n). Multiplication by |d(n)|/sqrt(n) therefore
  leaves L*sum |d(n)|/n, at the same scale as the desired main signal.
  A signed aggregate estimate must be proved before taking absolute values;
  merely inserting the new partial-sum theorem into the existing envelope
  cannot work. This is an OPEN CORE, not a new hypothesis.
- Deep harmonic query complete, no errors, inventory complete; mostly
  source-only compiler coverage and unmeasured semantic coverage. Candidate
  lemmas mostly irrelevant Gibbs hits; useful source arguments point to
  the actual conditional pinning law. Lexical fallback confirms the same
  receiver. Source definitions and exact error envelope read directly.
- Do not formalize a wrapper around NotchSmall or a new conditional detector
  and call it progress.

### Cycle30 primary audit and whole-contour candidate

- Deep Gonek/contour query completed, no errors; full file inventory but
  mostly source-only compiler coverage, unmeasured semantic coverage,
  snapshot three generations old and background refresh active. Inspected
  every candidate and source-argument signature. Useful hits are single-mode
  chi stationary-phase bounds, not the required infinite source estimate.
- Primary source: Laaksonen's 2016 thesis, Lemma3.5, requires a(n)=O(n^epsilon).
  That coefficient premise is not available here. Direct application is
  REJECTED; no published theorem is being treated as a source producer.
- Candidate mechanism: retain D_lambda inside the whole critical-line moment
  D_lambda(s)*zeta(s)*zeta(1-s), then shift the contour to Re s>1. Functional
  equation converts it to chi(1-s)*D_lambda(s)*zeta(s)^2, whose coefficients
  are lambda0*d_2. If R1 is the finite part of D_lambda at1, the candidate
  arithmetic main term is X*[log(X)^2/2+(2*gamma+R1-1)*log(X)+O(1)].
  The archimedean comparison suggests X*[log(X)^2/2+(gamma-1)*log(X)+O(1)].
  Their next coefficient is R1+gamma, the ordinary deviation harmonic limit.
  These calculations motivate the sign conjecture; they are NOT a closed proof.
- Three explicit obligations: (i) a signed convolution asymptotic with
  o(X log X) error; (ii) a smoothed chi coefficient extraction with an
  aggregate error derived from the actual source mean square, not an assumed
  pointwise Ramanujan bound; (iii) a justified positive boundary pairing,
  since zeta(s)*zeta(1-s) is nonnegative only on Re s=1/2.
- Available input for (ii): WeilMeanSquare.exists_sum_sq_Ioc_le_of_weilPositiveFull
  gives sum_(N<n<=2N)lambda(n)^2 <=2N*(log(2N)+C)^2. This allows large
  individual coefficients; it is not the premise of the published lemma.
  Smooth windows may remove endpoint losses, but this must be proved.
- Anti-theatre: harmonic convergence does not imply NotchSmall, and a formal
  convolution identity alone would not prove the sign or WP03. Anti-laziness:
  test the aggregate contour route with all three obligations exposed.
  Verdict OPEN CORE; no novelty claim or new Lean leaf for C30 yet.

### Cycle30 refinement: Gaussian extraction and symmetric-strip positivity

- The corpus already has the exact needed Gaussian transform:
  ZetaChiGaussianKernel:1273 and the generic series interchange
  ZetaLeftLineGaussianIntegrals:192. Approximation :434 and quadratic tail
  :794 are enough. No new stationary-phase or Ramanujan theorem is needed.
- With sigma=9/8 and cutoff Y=T^(4/3), absolute Dirichlet summability gives
  aggregate Gaussian-kernel error O(T^(5/6)). This is stronger than the
  earlier contemplated mean-square route and uses existing source premises.
- Subtract canonical Lambda before shifting. For p=(s-1)zeta, R=A-Phi,
  V=D_lambda*zeta^2+zeta'*zeta equals p*(R*p+p')/(s-1)^2.
  F=(D_lambda*zeta+zeta')*zeta(1-s) equals
  (R*p+p')*zeta(1-s)/(s-1). Their leading coefficients are ell=R(1)+gamma
  and -ell/2 respectively. There are no off-line-zero poles to control.
- Symmetric strip 1/4..3/4 applied to b_T(s)/(s-1/2-ir), with
  b_T=zeta(s)zeta(1-s)*exp((s-1/2)^2/T^2), gives Re(right integral)=pi*b_T
  on the critical line. Integrate against the already constructed positive
  boundary measure, retaining its regularized Herglotz kernel for Fubini.
  This resolves the paper boundary-passage obligation without boundary values.
- Gaussian Mellin inversion of V, shifted to3/4, gives the main term
  ell*sqrt(pi)/2*X*log X+O(X). Together these yield ell<=0 on paper.
  Full derivation and kill audit saved in PROOF.md, Cycle30. Status PAPER
  CANDIDATE: exact Lean assembly and second proof audit still required;
  no C30 formal theorem or WP03 solution is claimed.
- Next implementation objective, after that audit: all-source nonpositive
  harmonic limit, using only hW. Avoid a conditional boundary or Gonek
  interface as the capstone. Keep the exact uniform quotient goal visible.

### Cycle30 second audit and implementation plan

- Previous turn: PROGRESS (C29 verified and C30 paper argument recorded).
  Current worktree still contains both C29 leaves and exact WP03 stays open.
- Competing statements remain signed local-mass control, all-fibre harmonic
  convergence, and the untwisted harmonic sign. Select the last: it exposes
  an arithmetic restriction beyond convergence without claiming the detector.
- Second paper audit: right-minus-left contour sign is positive; F's residue
  is -ell/2; zeta-zero poles disappear in the product; summability at9/8
  pays both Gaussian errors. The symmetric-strip argument keeps the whole
  regularized Herglotz kernel before Fubini. No new source premise found.
- Primary comparison: Booker, arXiv:1308.3067v2, Definition1.3(A3), requires
  discrete support and all but finitely many integer spectral multiplicities.
  These are not supplied by full positivity. Its classification is not a
  black-box replacement. Laaksonen's pointwise-coefficient premise is also
  absent; the already-formalized Gaussian kernel bypasses it.
- Verdict BRIDGE. No publication-level novelty claim; the exact all-source
  sign theorem remains absent from audited corpus hits. Paper proof now
  accepted for formalization, subject to Lean exposing any omitted step.
- Plan: (1) symmetric-strip Cauchy and actual source positive pairing;
  (2) signed convolution/pole cancellation and Gaussian extraction;
  (3) Gaussian Mellin asymptotic and all-source harmonic sign;
  (4) targeted --old builds, final direct audits, axioms, imports and lint;
  then reassess what the sign says about the uniform quotient frontier.
  update_plan is not exposed in this session; this card tracks the plan.

### Cycle30 implementation: exact positive source pairing

- Reflected Cauchy helper passes targeted --old build. Herglotz pairing passes
  targeted --old build: the full regularized kernel is jointly integrable
  under fourth-order decay, and the normalization constant cancels. Explicit
  majorant is 40*C/((1+t^2)(1+r^2)). No finite-total-mass premise added.
- Concrete zeta-Gaussian test is now being checked. Its critical-line value
  is |zeta(1/2+ir)|^2 exp(-r^2/T^2); quarter-strip polynomial zeta growth plus
  Gaussian decay supplies every generic test hypothesis. Final direct checks,
  axioms and umbrella wiring remain outstanding for the new C30 leaves.
- Located existing canonical critical identity:
  WeilZetaSquareBoundaryInequality.re_datum_normSq_add_deriv_mul_conj.
  It already handles zeta zeros by multiplication. Reuse it for the later
  canonical contour term; do not reprove zero-free boundary identities.
- Anti-theatre answer in chat: verified contour helper does not prove C30
  or WP03. Anti-laziness answer in chat: continue through actual Gaussian
  hypotheses, then arithmetic extraction; no conditional helper capstone.

### Cycle30 remaining arithmetic and canonical steps

- Canonical term J=[(A+1/(s-1))*zeta+zeta']*zeta(1-s)*g_T.
  Use WeilZetaSquareBoundaryInequality:274 for zero real part on Re=1/2,
  including zeta zeros; shift J to3/4 using polynomial strip bounds and
  Gaussian decay. Combine with the verified-source pairing to bound F.
- Constant identification has explicit corpus ingredients:
  MertensSecondTheorem.mertensAbelTail_eq=-2*gamma;
  ZetaResidueFactorDerivative.deriv_zetaResidueFactor_one=gamma;
  DirichletUniformAbel.differentiableOn_dirichletSum and C29 convergence
  at3/4 give ordinary-sum holomorphy near1. Match it on Re>1, then identify
  the harmonic limit with R(1)+gamma by continuation/Abel uniqueness.
- Still required in Lean: exact signed convolution Dirichlet identity,
  pole cancellations, Gaussian kernel aggregate O(T^(5/6)), Mellin main
  term, final sign. None is discharged by the positive pairing alone.
  Full WP03 uniform quotient bound remains the later unsolved target.
- Further exact reuse for the Mellin stage: HTGeometry/AnalyticDoublePoleSplit
  provides `exists_doublePole_principalPart`; HTGeometry/RectangleDoublePole
  provides `rectIntegral_eq_double_pole_residue_on`. These handle the V*M*X^s
  double pole without pretending the simple-pole vertical-shift theorem
  applies directly. The second-order principal term has zero closed-contour
  integral; the derivative of the analytic numerator supplies the X log X
  coefficient. Read their exact hypotheses before assembling the shift.

### Cycle30a final formal audit

- Three new leaves verified: CauchyReflection, HerglotzPairing
  (source regularization and Fubini), GaussianPairing (actual test and
  source capstone). All targeted --old builds and all three final direct
  source checks exit0, no warnings. Five axiom audits standard-only.
- Actual Gaussian identity, nonnegativity and absolute integrability use
  only hW as the source assumption, with T>=1 as the test parameter range.
  All new leaves wired into RHTower; no full/umbrella build run.
- Lint exits1 for eight unrelated unreachable leaves, listed in EVIDENCE;
  no owned error or prohibited declaration. Turn classification PROGRESS.
- Next objective remains C30's all-source harmonic sign, not a new wrapper:
  canonical subtraction, signed convolution and pole cancellation,
  aggregate Gaussian extraction, Mellin asymptotic, constant identification.
  Exact WP03 is OPEN. Do not mark the goal complete for this bridge.
- Index refresh exits0; generated catalog files have no Git diff. All owned
  jobs exited and 12 C30 scratch/log files removed. Cross-session memory:
  research/weil-work-03-c30a-positive-gaussian-pairing-2026-10-07.

### Cycle30b continuation: canonical subtraction

- Previous turn PROGRESS: actual Gaussian positive pairing verified.
  Goal unchanged: exact arbitrary-source uniform quotient detector remains open.
- Revalidated C30 competing routes: signed absolute local-mass control and
  all-fibre harmonic convergence still lack proofs. Continue the accepted
  untwisted harmonic-sign paper proof; C30a has now paid its positive pairing.
- Exact next source conclusion: Re integral F(3/4+it)g_T dt <=0 for every
  hW and T>=1, F=[(A+1/(s-1)-Phi)zeta+zeta']zeta(1-s).
  Canonical J has zero real critical value by the existing weighted identity,
  is holomorphic on the quarter strip, and has polynomial growth. Gaussian
  decay permits shifting J from1/2 to3/4. Subtract the verified C30a identity.
  This is a dependency-closed subproof of C30, not a new novelty claim.
- Kill audit: no division by zeta, no RH, no boundary limit for Phi, no
  coefficient sign premise. Only canonical J reaches the boundary. Verdict
  BRIDGE; the harmonic sign and WP03 remain separate uncompleted conclusions.
- Plan: prove canonical Gaussian contour cancellation and actual-source
  subtraction; then pole/convolution and aggregate Gaussian extraction.
  Final targeted builds, direct checks, axioms, imports and lint follow.

### Cycle30b verification continuation

- Previous turn PROGRESS: canonical subtraction, pole cancellation and
  exact Gaussian pole transport were written; paper/evidence audits updated.
- Prior build handle77343 is missing, no matching Lean/Lake process exists,
  and no CanonicalGaussian olean exists. Its log has no terminal success;
  the build is interrupted/unverified, not counted as passed.
- Continue the same dependency-closed C30 argument. Next actions: verify
  CanonicalGaussian, PoleCancellation and GaussianShift, then finish the
  signed convolution/extraction and Mellin asymptotic. WP03 remains OPEN.
- Written leaves now cover canonical subtraction, common pole numerator,
  actual Gaussian contour transport, literal signed convolution and generic
  chi extraction, and the source error series O(T^(5/6)). All remain under
  audit until targeted builds and direct final checks pass. No imports are
  wired prematurely. The Mellin main term and harmonic-limit identification
  remain outstanding; full C30 and WP03 are not claimed.

### Cycle30c paper refinement: one-sided Mellin sign

- A full Gaussian Mellin asymptotic is unnecessary for ell<=0. The signed
  Gaussian upper bound O(x^(-5/6)) near0, absolute O(x^(-2)) at infinity,
  and exact Mellin transform give a uniform upper bound for
  Gamma(sigma/2)*Re V(sigma)/2 on1<sigma<3/2. Multiplying by(sigma-1)^2
  forces Re P(1)<=0. Exact proof and kill audit in PROOF.md.
- Corpus audit: the absolute-growth no-go MellinPoleRadialGrowth is not
  applicable to this one-sided claim. Mathlib hasSum_mellin_pi_mul_sq
  supplies the generic signed-coefficient transform with weighted absolute
  summability. Using the profile exp(-pi*n^2*t) changes the Mellin parameter
  to sigma/2 and the source bound to t^(-5/12); this avoids an extra
  Mellin square-root substitution. No full contour asymptotic required.
- Verdict BRIDGE, no publication novelty claim. Implementation of this
  refinement waits for the five current C30b leaves to pass their audits.
- CanonicalGaussian targeted --old build exits0, no owned warnings. The
  remaining linear dependency chain is being checked through the leaf
  GaussianError target; no umbrella or full build is run. Final direct
  source audit and axiom/import/lint checks remain outstanding.
- PoleCancellation targeted dependency build now passes. Both punctured
  limits use the exact analytic numerator; no removable-singularity or
  source sign assertion is assumed. GaussianShift, SignedConvolution and
  GaussianError remain under audit in the same foreground build.
- GaussianShift now passes its targeted dependency build, including the
  source growth estimate, absolute right-line integrability, exact residue
  transport and signed upper bound. Initial namespace/layout failures were
  repaired; the final direct audit remains outstanding. The same build
  continues to SignedConvolution and GaussianError.
- Next Mellin integrability proof can use the exact termwise Gamma norm
  integrals from mathlib MellinEqDirichlet, Measurable.tsum, the bound
  enorm_tsum_le_tsum_enorm and lintegral_tsum. Summable integral norms make
  the resulting lintegral finite. DominatedConvergence's transform identity
  alone does not return integrability; do not use it as that missing proof.
  API names added to the pending scratch audit; no new Lean claim yet.
- SignedConvolution and GaussianError targeted builds pass. The latter's
  only warning was an unreachable tactic after gcongr; that tactic is now
  removed and the final source audit will check the cleanup. All five
  C30b leaves are wired into RHTower. No full/umbrella build run. Pending:
  scratch API check, final direct checks, refreshed leaf artifact, axioms,
  authoritative lint and source index, then C30c implementation.
- All C30b API probes pass after specifying universes in generic probes.
  The cleaned GaussianError target passes. CanonicalGaussian and
  PoleCancellation direct audits pass; the remaining direct checks and
  axiom audit continue sequentially in handle55570. Lint has six unrelated
  unreachable modules (current list in EVIDENCE); source index exits0.
- Scheduling refinement: with all five targets and their APIs checked,
  prepare GaussianBound in a separate file while the final direct audits
  run. Its four source theorems pay both series' convergence, exact error
  subtraction, and the signed O(T^(5/6)) Gaussian upper bound. This file is
  WRITTEN/UNVERIFIED, not wired. New API scratch is /tmp/wp03-c30c-api.lean;
  run it only after handle55570 has exited, then targeted GaussianBound.
- All five final lake-env-lean source audits pass without warnings. The
  cleaned error target also passes without warnings. The same sequential
  handle55570 is now running the 37-declaration axiom audit; do not start
  another Lean process until it exits.
- Handle55570 exits0: all37 public C30b declarations have standard-only
  axiom lists. C30b final audit is complete, recorded in RESULT/EVIDENCE.
  All other old search/lint/index jobs also exited. Current foreground
  handle28447 checks /tmp/wp03-c30c-api.lean then the targeted --old
  GaussianBound leaf. Do not overlap another Lean job with it.
- C30b final evidence saved in the result files and memory
  research/weil-work-03-c30b-source-gaussian-extraction-2026-10-07. All18
  completed C30b/frontier-search scratch and log files removed after their
  jobs exited. Only current C30c scratch/build files remain in use.
- Mellin implementation refinement: use fixed upper envelope C*t^(-11/12)
  on(0,1] and S*t^(-5/4) on(1,infinity), rather than evaluating integrals
  depending on sigma. Mathlib intervalIntegral.integrableOn_Ioo_rpow_iff
  and integrableOn_Ioi_rpow_of_lt give its integrability; near interval
  can be restricted from(0,2) to avoid endpoint conversion. This does not
  replace the independent absolute-integrability proof for Hpi's Mellin
  integrand. Exact argument added to PROOF.
- C30c API correction: actual complex numeral projection names are
  Complex.re_ofNat/im_ofNat. First GaussianBound check then found only
  an rpow-two conversion and positive-factor cancellation lemma mismatch.
  Repaired with Real.rpow_two and mul_le_mul_iff_right₀; updated minimal
  mathlib-only API scratch passes. Current handle11990 is the targeted
  GaussianBound build. Earlier handles28447/14656 exited with failures.
- Prepared /tmp/wp03-c30c-mellin-api.lean (NOT RUN): minimal API probes
  plus an actual proof that integrable summands with summable norm integrals
  have an integrable complex sum. It uses AEMeasurable.tsum,
  ofReal_integral_norm_eq_lintegral_enorm and Summable.tsum_ofReal_lt_top
  with the lintegral triangle bound. Test after the current Lean job exits;
  this keeps the later Mellin comparison independent of default integrals.
- Handle11990 exited1: its sole remaining failure was the unsimplified
  imaginary part of(2*pi) in the real contour inequality. Replaced that
  simplification by norm_num[Complex.mul_re,Complex.mul_im]. Current
  handle43190 runs the minimal API check, targeted GaussianBound build,
  its final direct source check, four axiom reports, then the Mellin API
  and integrability scratch. One sequential foreground Lean process only.
- Handle43190 exited1: broad norm_num normalized only one exponential's
  argument, so the real arithmetic tactic could not identify the two
  equal values. Replaced it with precise complex-projection simp rules,
  retaining the exponential argument. Current handle88286 performs the
  targeted build, direct audit, four axiom reports and Mellin scratch in
  sequence. C30b remains fully audited; GaussianBound is still pending.
- GaussianBound targeted --old build passes without warnings. Its umbrella
  import is wired. Handle88286 continues with the direct source check,
  four axiom reports and the Mellin integrability scratch. Exact source
  signed Gaussian upper bound is now kernel-checked; final audit pending.
- GaussianBound final direct check passes without warnings. Handle88286
  is running its four axiom reports, then the Mellin scratch. C30c lint
  exits1 with six unrelated unreachable modules (now
  WeilWorkDeficitXiApproximationCost plus the same five HTGeometry leaves);
  no WP03 error. Index refresh exits0. Final axiom evidence and cleanup
  still pending; no second Lean process started.
- GaussianBound's four axiom audits pass, all standard-only. Six new
  leaves and41 public declarations are fully audited across C30b/C30c.
  Handle88286 is now only running the minimal Mellin API/integrability
  scratch; corpus source audits are complete. WP03 and harmonic sign
  remain OPEN. Preserve the scratch proof in PROOF if it passes, then
  remove completed C30c scratch/log files and update memory.
- Handle88286 exited1 only on the Mellin scratch's unscoped infinity
  symbol. Replaced it by typed top; scratch-only handle48594 exits0 with
  no diagnostics. All source and scratch jobs have now exited. The checked
  integrability proof is preserved in PROOF.md. No source audit needed
  rerunning for the scratch-only fix.
- NEXT: actual Hpi(t)=sum a(n)exp(-pi*n²*t) profile, envelopes via
  T=sqrt(4*pi/t), actual Mellin convergence/transform, fixed integrable
  upper envelope and pole limit ReP(1)<=0, then identification with C29's
  ordinary harmonic deviation limit. Gamma_R(1)=1; continuity at1 follows
  by inverting its globally differentiable reciprocal (verify the exact
  continuous-inverse API before use). Exact WP03 still needs its uniform
  quotient detector after this sign theorem; do not mark the goal complete.
- Iteration classification PROGRESS. Six leaves audited,41 standard-only
  public axiom lists; all imports wired. All10 completed C30c scratch/log
  files removed after their jobs exited, in addition to the earlier18.
  No owned job or unverified Lean source remains. Checked Mellin helper
  retained in PROOF.md. Cross-session continuation memory:
  research/weil-work-03-c30c-signed-gaussian-bound-2026-10-07.

### C30d: actual Mellin convergence and source pole sign

- Previous iteration PROGRESS; goal OPEN. Plan: normalize the actual
  Gaussian profile, discharge norm Fubini from source Dirichlet
  summability, prove its exact Mellin identity, then compare with a fixed
  integrable upper envelope and extract the pole sign. Identify the
  ordinary harmonic limit afterward; uniform quotient detection remains
  a separate unpaid gate.
- Fresh deep corpus search inventories68538 files, generation1281256;
  partial only because reranking exceeded its deadline. All returned
  candidate/source statements and proposed ingredient sets inspected.
  Generic contour suggestions do not discharge the actual-source Mellin
  obligation. No useful replacement theorem found.
- External audit: DLMF2.5 and Miller--Schmid's Distributions and Analytic
  Continuation of Dirichlet Series (math/0403030) concern classical
  Mellin mechanisms; no novelty claim for the transform itself. The
  proposed new corpus consequence is the actual full-positive source
  pole sign. Paper proof and integrability obligation remain explicit
  in PROOF.md. Verdict BRIDGE; no absolute-bound or zero-free premise.
- GaussianProfile targeted --old build passes without warnings; umbrella
  import wired. Mellin, MellinBound, PoleSign and HarmonicSign are drafted
  but UNVERIFIED. Current sequential foreground handle72992 runs the
  remaining minimal APIs then the targeted Mellin build. No other owned
  Lean process. Final direct checks, axiom audit, lint and cleanup unpaid.
- Harmonic lookup found the existing real approach-to-pole theorem and
  Laurent limit in ZetaResidueFactorDerivative; reused, avoiding a new
  duplicate filter bridge. Exact harmonic identification paper proof
  added to PROOF.md. Existing sign receiver needs NotchSmall; this cycle
  aims to remove it, not infer scalar equality or full rigidity.
- C31 PRELIMINARY candidate (do not promote to a theorem): multiply the
  actual test by q(s)=P(s)P(1-s), P a real finite Dirichlet polynomial.
  On the critical line q=|P|², while q(1)=P(1)P(0) can have either sign.
  If the C30 signed extraction survives finite positive dilations, the
  same Mellin argument gives RePsource(1)*q(1)<=0 and hence scalar
  equality. All convergence, canonical reflection, contour transport,
  real-frequency kernel errors and exact Mellin factors must be paid.
  No equality or rigidity has been established from this candidate.
- C31 deep search is complete,68550 files,generation1281376,partial=false;
  all20 candidate and20 source statements plus ingredient sets audited.
  Source suggestions still retain pointwise/nonnegativity/regularity
  premises where relevant. Checked exact scaled kernel transform in
  ZetaLeftLineGaussianIntegrals: integral=2*pi*r*sum a(n)J_T(n*r).
  Its scale factor must be retained. Exposed-point equality refers to the
  riemannKernelAutocorr functional, not this harmonic constant. Do not
  conflate them. C30d verification remains the active implementation.
- Mellin targeted --old build passes without warnings. Both actual-source
  convergence and exact transform are verified; import wired. Current
  handle8844 continues sequentially through MellinBound, PoleSign and
  HarmonicSign. GaussianProfile+Mellin final direct audits still unpaid;
  remaining three leaves remain unverified until their checks finish.
- MellinBound targeted --old build passes without warnings, import wired.
  Its actual-source uniform bound is verified. PoleSign first check had
  only function-composition and neighbourhood elaboration errors, now
  fixed. Current foreground handle63389 builds PoleSign then HarmonicSign.
  Prior handles have exited. Five-leaf direct check script and12-declaration
  axiom scratch are prepared in /tmp/wp03-c30d-* but not yet run. All
  minimal mathlib API probes now pass. No sign theorem claimed yet.
- PoleSign targeted --old build passes without warnings: the actual
  source coefficient ReP(1)<=0 is now verified. Import wired. Handle63389
  now runs only HarmonicSign. Direct/axiom checks remain unpaid for all
  five new leaves; no WP03 completion claim.
- C30d COMPLETE/PROGRESS: all five targeted --old builds and all five
  final direct lake-env-lean checks pass without warnings. All12 public
  declarations have standard-only axiom lists. All imports wired. The
  actual ordinary harmonic limit is ReP(1)<=0 from hW alone. Working
  result, evidence, paper proof and WP03 frontier row updated.
- Final lint exits1 only on seven unrelated unreachable modules (listed
  in EVIDENCE); index exits0. No owned Lean job remains. Scratch/log
  cleanup and continuation memory are the remaining housekeeping items.
- NEXT C31: audit/prove the concrete Q(s)=1-(3/2)*2^(-s) weighted source
  Gaussian contour and its three-dilate upper bound. Exact profile and
  scale factors are in PROOF. Do not infer its bound from C30's scalar
  bounds, since two coefficients are negative. If paid, its pole factor
  -1/8 should force the reverse inequality and harmonic equality. This
  would still not be the exposed-point functional or WP03 closure.
- Housekeeping complete: all25 owned C30d/C31 scratch, log and research
  files removed after their jobs exited. No owned process or unverified
  source remains. Generated catalog files have no Git diff. Continuation
  memory: research/weil-work-03-c30d-harmonic-sign-2026-10-07. Goal ACTIVE;
  C30d is a completed research cycle, not WP03 completion.

### 2026-10-08 C31 kill audit and positive salvage

- C31 phase-free polynomial profile: FALSE AS STATED. The exact near
  kernel estimate contains cos(2*pi*y). C30's integer specialization
  removes it legitimately; the n/2 specialization gives (-1)^n.
  Therefore the previously logged -1/8 scalar Mellin argument cannot
  force harmonic equality. C30d remains valid.
- Corrected profile: (1+c^2/2)H(t)-(c/2)H_alt(t/4)-cH(4t).
  The additive twist has its own Dirichlet series, not V(s).
- C31a survivor paper proof closed in PROOF.md: all-real positive
  frequency weighted kernel error, summation over the actual source,
  exact scaled source contour extraction and O_r(T^(5/6)) remainder.
  Formal status pending. Weighted positivity/twisted pole control are
  next conjectures, not assumed conclusions.
- Corpus searches c31a/c31b complete without partial results; latest
  coverage68559 files,generation1281694. All candidate/source statements
  checked; returned parity/dilation abstractions do not supply the
  actual arithmetic extraction. Proposed ingredients rejected.
- External audit: Booker's L-data framework assumes discrete spectral
  support and near-integral multiplicities, absent for arbitrary hW.
  Its classification cannot close this task. No novelty claim for the
  classical additive-twist mechanism.
- C31a implementation: TwistedGaussianError and TwistedExtraction are
  new owned leaves. First check found cosine product-order and scale
  product-normalization script errors, repaired. Targeted check pending;
  no theorem claimed yet. An API probe/build briefly overlapped due to
  misreading a live handle; the owned build was terminated by PID and
  its exit verified. Subsequent Lean calls are strictly sequential.
- C32 corpus audit: deep search partial (semantic deadline),68565 files,
  generation1283089. All20 candidate and20 source statements inspected;
  proposed generic quadratic-form ingredients are inapplicable. Direct
  rg found relevant existing WeilZetaSquareDilationRigidity,
  WeilFibreBochnerLaw, WeilConeNotchBochnerLaw and GcdWeightedSeriesInversion.
  Their exact statements retain absolute boundary decay, NotchSmall,
  convergent gcd-weighted sums, or absolute harmonic tail control.
  The gcd representation itself is REDISCOVERED, not a new theorem.
- Revised C32 target: derive the literal polynomial-weighted Gaussian
  inequality for arbitrary hW, retaining the additive twist, then test
  whether it removes NotchSmall from the full fibre law. Do not assume
  twisted pole limits, coprime-subseries convergence, or absolute tails.
  Those are the open arithmetic obligations. The main WP03 receiver
  (uniform quotient boundedness) is still open.
- C31a uniform refinement exposed by the proof: one source constant
  controls ALL r>0, with contour error C*r^(-1/8)*T^(5/6), rather than
  a separate unspecified constant for each r. Paper derivation and
  novelty verdict BRIDGE recorded; exact-name/kernel lexical re-search
  produced no matching theorem. The fixed-scale version passed its
  targeted check; stronger quantifier order is now being checked.
- C31b dependency-closed paper proof of the literal two-term polynomial
  Gaussian inequality is now in PROOF.md. It uses the actual Herglotz
  pairing, canonical zero real part, residue shift, and C31a extraction.
  It retains H_alt. Lean formalization pending.
- C32 explicit competing conjectures: full positivity alone forces all
  ordinary gcd-weighted harmonic limits and the finite twist sign law;
  or it forces only regularized/subsequential arithmetic limits. First
  open core: existence of the arithmetic limits. Neither the C30 scalar
  convergence nor classical gcd inversion supplies this. Do not replace
  it by an absolute-tail hypothesis.
- C31a COMPLETE/PROGRESS: strengthened uniform-scale statements pass
  both targeted --old builds and both final direct lake-env-lean checks,
  with empty final diagnostics. All9 public axiom audits standard-only.
  Both imports wired; index exit0; generated catalogs have no Git diff.
  Lint has9 unrelated unreachable modules, no owned/prohibited errors.
  Source result, proof and evidence updated. WP03 remains OPEN.
- Next implementation is C31b's actual polynomial-weighted Gaussian
  inequality, whose full paper proof is now recorded. Preserve the
  parity/additive twist and exact residue; do not reuse the failed scalar
  Mellin factor. Then audit arithmetic-limit existence for C32.
- Cleanup verified: all18 owned scratch/log/research files removed
  after every owned process exited. No unverified owned source remains.
  Continuation memory: research/weil-work-03-c31a-uniform-twist-2026-10-08.
  Goal ACTIVE; C31a is a completed bridge cycle, not WP03 completion.

### C31b continuation: actual polynomial-weighted positivity

- Previous goal turn: PROGRESS, nine audited source-extraction theorems.
  Re-read exact WP03 target and C31b paper proof against current tree.
  Main receiver remains unpaid; hgtl7 workflow continues.
- Exact Gaussian bound and dependency-closed proof are already in
  PROOF.md. New implementation will pay polynomial analytic properties,
  the actual Herglotz/canonical weighted pairing, residue shift, and the
  literal parity-weighted Gaussian inequality. No twisted pole limit,
  NotchSmall, sign, or absolute tail premise will be introduced.
- Fresh corpus search running for the precise weighted mechanism.
  External re-search checks polynomial/twist and Gaussian/Herglotz
  formulations. Verdict remains BRIDGE unless stronger arithmetic
  content survives the subsequent limit audit.
- Fresh search complete:68568files,generation1283236,partial=false.
  All20 candidate and20 source statements checked; returned boundary
  rigidity statements retain extra summability. Proposed parity-graph
  ingredients are unrelated and rejected. Primary external exact searches
  returned no hits; previously audited additive-twist/gcd parents remain
  the comparison, with no novelty claim for polynomial algebra.
- PolynomialWeight and PolynomialPairing targeted --old checks pass.
  The actual weighted spectral identity and source sign on Re=3/4 are
  paid. PolynomialShift initially exposed a product-association mismatch
  in the residue limit; repaired with an explicit typed limit. Current
  targeted build proceeds through Shift, Gaussian and Profile. Their
  results are not claimed until verification and axiom audits finish.
- C32 renewed searches: parity/pole deep search68573files,
  generation1283395,partial=false; sourceSquareCoeff follow-up same
  coverage,generation1283416,partial=false. All20 candidate and20 source
  statements inspected in each. Proposed dirichletLimit ingredient is
  an entire transform of a Dirichlet-character test, not a limit of our
  additive-twisted coefficient series; source definition checked and
  ingredient rejected. Gcd/sieve hits do not pay actual source limits.
- C32 sharper target and paper proof now recorded: actual normalized
  parity Mellin expression is asymptotically confined to an explicit
  interval determined by ell<=0. Uses fixed c=+/-sqrt(2), no pole-limit
  premise. Nontrivial interval survives when ell<0; no harmonic equality
  or uniform quotient bound is claimed. First Lean debt: actual parity
  Mellin convergence and weighted transform identity.
- C31b targeted build COMPLETE: PolynomialWeight, PolynomialPairing,
  PolynomialShift, PolynomialGaussian, PolynomialProfile all pass,
  without owned warnings. Gaussian's finite integral subtraction needed
  explicit Pi.sub_apply normalization; no mathematical change. All five
  imports wired. Sequential final direct audits/30 public axiom reports
  are currently running; no umbrella build.
- Index refresh exit0; generated catalogs unchanged in Git. Formal lint
  exit1 reports seven unrelated unreachable leaves only: WeilPaperNullSamplingSpace,
  WeilWorkQuantizationPositiveFactor, ApertureConeCalculus,
  ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal,
  BoundaryCoronaCStarAlgebra. No owned-source/prohibited-declaration error.
- New primary-source check opened Guillot--Wu arXiv1901.01947v1 and
  Choudhury--Panigrahy arXiv2506.24053v1. Finite gcd positivity/totient
  decomposition is established algebra, not the missing actual-source
  analytic limit. The latter page has an August2026 internal date;
  no July2026 novelty claim relies on it. C31b remains a BRIDGE.
- Name the new interval step C32a. Parent C32 (actual full arithmetic
  fibre law) and exact WP03 receiver remain unchanged. Kill audit shows
  the two-term limiting quadratic constraints allow nonconvergent scalar
  functions inside the interval for ell<0. This is not an arithmetic
  counterexample; additional actual-source structure is needed for
  ordinary convergence. Do not sell the interval as the full fibre law.
- C32a implementation started after the dependency-closed paper audit.
  Exposed the already-proved generic exponential Mellin convergence and
  actual source norm-series lemmas in owned Mellin leaf; proofs unchanged.
  New ParityMellin leaf defines the actual alternating coefficients,
  proves absolute Dirichlet convergence, and proves actual Mellin
  convergence/identity. UNVERIFIED until current C31b foreground audit
  exits and its own targeted/direct checks run. No concurrent Lean job.
- C31b COMPLETE/PROGRESS: all five final direct source checks exit0 with
  empty diagnostics. All30 public declarations report only propext,
  Classical.choice, Quot.sound. Result/proof/evidence/frontier updated.
  Anti-theatre and anti-laziness answers posted in chat. C32a continues;
  exact WP03 goal ACTIVE/OPEN. No claim of harmonic equality.

### C32a continuation after interrupted turn

- Previous turn PROGRESS: C31b fully source/axiom audited; actual C32a
  parity and polynomial Mellin leaves written. Goal unchanged/ACTIVE.
- Interrupted process handle81187 is missing; /tmp log is absent and
  process inventory shows no owned PolynomialMellin job. Started a fresh
  targeted --old build only after this authoritative check.
- Current hgtl7 skill re-read; October2026 SOTA standard retained, with
  no novelty claim from empty search results. Exact WP03 receiver and
  current frontier row re-read. Memory C31a is superseded by C31b card.
- Explicit research question: Given the exact internal and external
  frontier, what would a Fields Medal-winning mathematician conjecture?
  Parent answer remains C32: actual full arithmetic fibre law from hW
  alone. Competing alternative: only subsequential/regularized arithmetic
  limits. OPEN CORE remains ordinary arithmetic limit existence.
  C32a interval constraint is a dependency-closed BRIDGE to investigate
  that core, not a claimed new parent theory or replacement objective.
- Fresh deep source audit:68583files,generation1286264; partial at semantic
  runtime deadline. All20 candidate and20 source statements inspected.
  Proposed finite-support twistBound/poleSystem ingredients retain finite
  support/BoundaryRegular hypotheses, so do not apply. Source multiples
  law also requires nonnegative coefficients; not imported here.
- External broader check: Bettin1607.05595 concerns twisted Dirichlet
  L-function moments/Estermann; Farmer--Wilson math/0408221 assumes
  specified Euler factors plus additional converse hypotheses. Neither
  abstract supplies continuation for our unrestricted alternating series.
  Their primary pages were opened; no new novelty claim is made.
- ParityMellin targeted check PASSED: actual absolute Dirichlet/Mellin
  convergence and exact alternating transform. PolynomialMellin now
  PASSES, including actual weighted convergence/identity and real-axis
  quadratic identity. Function subtraction needed Pi.sub_def, not merely
  Pi.sub_apply. Minimal pole-limit API probe passes, including explicit
  square-root/rpow evaluations; no numeric experiments.
- Exposed common upper-envelope argument in owned MellinBound so scalar
  and polynomial sources share the same proof. Scalar endpoint preserved.
  PolynomialTail, PolynomialMellinBound, ParityPoleBound and
  ParityPoleInterval now implement the paper chain; UNVERIFIED pending
  their checks. Tail build is the only active Lean/Lake job.
- Tail's half-scale normalization left only a polynomial identity after
  denominator clearing; ring closes it. Sequential targeted checks now
  run Tail, shared MellinBound, PolynomialMellinBound, ParityPoleBound,
  ParityPoleInterval, stopping at first failure. One foreground Lake
  process at a time. Final direct/axiom audits still unpaid for C32a.

### C33: growing tests versus arithmetic mass escaping fixed denominators

- C32a interval targeted check PASSED. Six new imports wired. Eight
  final direct source checks plus21 public axiom reports run sequentially;
  no final audit claim until their process exits. Latest lint has11
  unrelated unreachable modules and no owned/prohibited-declaration error;
  index exits0, generated catalogs unchanged.
- C32a's five anti-theatre and four anti-laziness answers posted in chat.
  Verdict BRIDGE: actual no-limit-premise bound, no novelty claim.
- Given the exact internal and external frontier, what would a Fields
  Medal-winning mathematician conjecture? Parent C32 remains that the
  actual arithmetic fibre law is rigid. C33 sharpens the competing worlds:
  growing finite polynomial tests detect every nonzero actual deviation,
  versus an arithmetic defect that escapes every fixed denominator test.
  The latter is a possible obstruction, not a constructed full-positive
  source or a theorem. [OPEN CORE]: uniformity sufficient for arithmetic
  inversion as polynomial length grows. Fixed discriminants do not pay it.
- First paid bridge selected: quantify the complete finite-polynomial
  contour extraction with one source constant and explicit coefficient
  weights. Existing T^(5/6) kernel error already permits short growing
  reciprocal prefixes; all-order kernel formalization is unnecessary for
  this first test. Do not replace C32/WP03 by the routine bridge.
- Rejected shortcut: formally replacing both factors by the reciprocal
  turns the deviation pairing into H'(s)H(1-s), H=zeta*G. Even when justified,
  the associated averaged sign matches ordinary Dirichlet energy decay;
  it supplies no rigidity. No substitution on the unavailable left domain
  is made in Lean.
- Corpus arithmetic search68601files,generation1286472/73 was partial at
  reranking deadline. All20 candidate and20 source statements inspected;
  proposed additive-convolution/Estermann ingredients do not identify our
  arbitrary source's twisted residues. Fourier search same coverage was
  partial; all20+20 statements inspected. Existing iterated-derivative
  Fourier decay handles generic analytic machinery, not arithmetic
  denominator uniformity. All-order kernel idea retained only as optional
  later optimization, not the selected mathematical breakthrough.
- Primary external pages opened: Miles1803.05878 (lognormal Mellin/Fourier
  transform), Bettin--Chandee--Radziwill1411.7764 and Pratt--Robles1706.04593
  (mollified zeta mean squares). Classical finite polynomial expansion is
  not novel. These sources do not prove the arbitrary full-positive
  source's growing arithmetic inversion. No numerical computation run.

- C32a COMPLETE/PROGRESS: all eight final direct source checks exit0,
  empty diagnostics. All21 public declarations standard-only axioms.
  Six imports wired; RESULT/PROOF/EVIDENCE/frontier updated. Exact goal
  ACTIVE/OPEN. The interval proof does not assert a parity limit.
- C33 four new leaves now written (FiniteWeight,FiniteGaussian,
  FinitePairing,FiniteShift), unverified/unwired. Paper bridge complete;
  exact C33 detection conjecture still has arithmetic-completeness core.
  API probe session30743 is the sole owned foreground Lean process.

- C33 FiniteWeight targeted check PASSED. FiniteGaussian targeted check
  PASSED after normalizing finite-sum domains and swapping the double-sum
  order. An unused ring tactic was removed; final recheck still due.
  Both minimal API probes passed. FiniteEnergy and FiniteBound now written
  from the closed paper chain. Energy targeted check is the sole active
  build. Pairing/Shift/Bound checks follow sequentially. No final C33 claim.
- C32's22 owned scratch/log files removed after source/axiom terminal exit;
  authoritative results remain in docs and Serena memory. No live C32 job.

- FiniteEnergy targeted check PASSED, no warnings. It bounds BOTH the
  complete ratio-extraction budget and the literal pole weight by one
  universal constant times E(c)*(N+1)^(9/8). Cauchy proof needed explicit
  rational-exponent normalization only. FiniteBound adds the complete
  hW-only endpoint and moving-length exponent5/6+9*theta/8; UNVERIFIED.
- Sequential foreground loop now checks FiniteGaussian (unused-tactic
  cleanup), FinitePairing, FiniteShift, FiniteBound and stops on failure.
  Six C33 leaves require final direct/axiom audits and umbrella wiring.


## C33 final audit and C34 kill audit — 2026-10-08

- Six targeted --old checks PASS; final sequential direct audit10416
  exits0. Six source logs empty. All29 public declarations (25 theorems,
  4 definitions) report only propext, Classical.choice, Quot.sound.
  No new source premise, heartbeat override, axiom, numerical experiment,
  full build or umbrella build. Six imports wired.
- Formal lint37605 exits1 on six unrelated unreachable modules:
  RHTower.WeilWorkHigherDenominatorInversionFourier;
  HTGeometry.ApertureConeCalculus, ApertureConeWinding,
  ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra.
  No owned or prohibited-declaration finding. Global lint is not green.
  Index16197 exits0; generated catalogs unchanged.
- C33 analytic survivor BRIDGE. Positive order-T detection conjecture
  rejected as target-equivalent/CIRCULAR; arithmetic completeness unpaid.
  Five anti-theatre and four anti-laziness answers posted in chat.
- C34 exact critical absolute-harmonic candidate REDISCOVERED. Deep
  search68622files,generation1286724 is complete, partial=false/errors[].
  All20 candidate and20 source statements inspected; actual theorem
  WeilAbsoluteConvergenceRigidity:536 read. Stronger one-sided endpoint
  and signed-window results verified in WeilOneSidedConvergenceRigidity
  at306,411,425. STATUS MUST-584/586 already records them.
- Boundary search68621files,generation1286686 partial at reranking;
  variance search68622files,generation1286718 complete/errors[]. All
  candidate/source statements inspected. Odd-series radial pole and
  deletion ratio provide no analytic continuation; dyadic coefficient
  variance does not imply a global log-square bound. No such shortcut used.

Next plan: inspect the mixed cancellation frontier; propose an independent
arithmetic statement outside the full-positive-only target equivalence;
run corpus/primary-source kill audit before any further Lean implementation.
Exact WP03/goal remains ACTIVE and OPEN.

### C35: forward variance, exact conjecture and first obstruction

- Given the exact internal and external frontier, what would a Fields
  Medal-winning mathematician conjecture? For every actual full-positive
  source, with a=forwardCoeff and B=the actual forward pole residue,
  conjecture (sum_(n<=N)|a(n)-B|^2/n)/log N -> 0. Rival: a positive
  limiting variance survives while the first moment remains B. This
  asks for an independent coefficient-energy law, not an order-T detecting
  witness already contradicted by C33. No premise is added to Lean.
- Internal exact source check: WeilWorkSettledPhaseForwardSummatory:22,153
  already proves sum a=B*N+O_epsilon(N^(1/2+epsilon)) and ordinary
  centered convergence Re s>1/2. Source forward energy is only O(log N)
  in WeilWorkSingularArithmeticForwardCoefficients:325. Definitions of
  sourceCoeff and forwardCoeff must be identified explicitly before use.
- [OPEN CORE]: an upper leading constant exactly |B|^2 for the forward
  square energy. Cauchy supplies only the lower direction. No proof of
  the conjecture or of a detector implication has been claimed.
- Kill test of weaker inference: a(n)=1+c*1_(2 divides n), n>=1, has
  mean B=1+c/2 with O(1) summatory error, energy coefficient
  1+c+c^2/2, and variance c^2/4>0 for c!=0. Its Dirichlet function is
  zeta(s)*(1+c*2^(-s)). Thus centered summatory precision plus O(log N)
  energy cannot force zero variance. It is NOT a full-positive source;
  one cannot import its variance as a counterexample to C35.
- New paper lead: the existing exact log-moment inequality is stronger
  than the O(log N) corollary. Writing E_N=sum w_n, S_N=sum log(n)w_n,
  H_N=log(N)E_N-S_N, it gives (log N-C)E_N<=2H_N. Since
  H_(N+1)-H_N=log((N+1)/N)*E_N, the ratio
  H_N/(log N-C)^2 is eventually nonincreasing. A monotone-density
  argument should therefore produce an ACTUAL limiting energy constant,
  not just a limsup bound. This would define the residual variance
  precisely; it does not yet force that constant to equal |B|^2.
- Searches: mixed68625/generation1286774; energy68629/1286800;
  spectral68630/1286825; variance68630/1287372; prime68631/1287390.
  All complete/partial=false/errors[]. All candidate/source statements
  inspected, including the prime output tail. Source
  support/phase/converse hypotheses were not imported unproved.
- Primary sources opened: Hedenmalm--Lindqvist--Seip math/9512211,
  Saias--Weingartner0807.0783, Sepulcre--Vidal1711.04122,
  Broucke--Hilberdink2409.06301, Bettin--Chandee--Radziwill1411.7764,
  Burnol math/9810169, Connes--Consani2006.13771. These provide Hardy,
  periodic, mean-value and explicit-formula parents, not the source's
  zero variance. September2026 2608.24827v2 was opened; compact-window
  computations neither used nor run. No external novelty claim.

C35a implementation checkpoint (2026-10-08): generic monotone primitive
and finite-secant mass-limit leaves now compile. Their imports were
reduced to mathlib, cutting the generic check from 127s to 7--12s.
The actual hW-only forward energy-limit leaf also passed its targeted
`lake build --old +...` check (114s). ForwardMean and ForwardVariance
are written and pending checks; no completed variance audit yet.
Saturation search: files68651/generation1288489, partial=false/errors=[],
all20 candidate and20 source statements inspected. No returned result
pays the sharp residue-square energy constant. Compiler coverage mixed;
source statements and final direct Lean audits remain authoritative.

C35a COMPLETE: all five targeted --old leaf builds and direct audit84733
pass; five source logs empty; all17 public declarations standard axioms
only. Five imports wired. Lint13394 has six unrelated unreachable modules
listed in EVIDENCE; no owned issue. Index63108 passes. Closed survivor
is BRIDGE; C35 V=0 and original WP03 quotient remain OPEN. Nine audit
answers posted in chat. Next attack must use full arithmetic positivity,
not just scalar log-moment and first-mean bounds.

### C36: periodic completeness of the actual coefficient energy (OPEN)

Phase1/2 searches complete: sharp-energy68656/gen1288579 (deep),
periodic68657/1288589, BAP68659/1288682; partial=false/errors=[].
All returned20 candidate/20 source statements inspected, plus deep
proof_ideas(empty) and ingredient_sets (irrelevant generic BAG bounds).
Own then-unverified C35 declarations returned by search were not treated
as independent evidence. C35a is now verified separately.

Exact conjecture: for every full-positive source and every epsilon>0,
there exist q>=1 and v:Fin q->Complex such that eventually in N,

    (1/log N) sum_(1<=n<=N) |a(n)-v(n mod q)|^2/n < epsilon,
    a = actual forwardCoeff lam.

Rival: a full-positive source has a positive log-square distance from
all periodic sequences, even though its first mean and energy limit
exist. [OPEN CORE]: prove periodic completeness from FULL arithmetic
positivity; bounded scalar energy does not give it. C35(V=0) would imply
this conjecture with a constant approximant, but no such implication is
used as proof. This is a proposed mechanism, not a replacement for the
original uniform bounded-quotient target or a paid detector implication.

Primary external ancestry opened/read:
- Bergelson--Kulaga-Przymus--Lemanczyk--Richter, IMRN2020 rny040,
  https://academic.oup.com/imrn/article/2020/5/1300/4959780 , especially
  Theorem2.10/Corollary2.11. Multiplicativity/pretentiousness and their
  ordinary mean-square hypotheses are not known for the actual a.
- Laporta2204.01581, https://arxiv.org/html/2204.01581v1 , Delange's
  condition sum 2^omega(n)|mu*a(n)|/n<infinity is UNPAID here.
- Aggarwal--Banerjee--Gupta2608.13172v1 (Aug2026),
  https://arxiv.org/html/2608.13172v1 , Theorem3.4 concerns normalized
  summatory error terms under specific functional equations. It does
  not supply periodic coefficient approximation for this source.
- A1995 Acta Arithmetica PDF request failed; no result from it used.

Attack of weaker scalar inference: take irrational alpha and0<c<1,
f(n)=1+c*cos(2*pi*alpha*n), changing f(1) to1 if normalization is wanted.
Finite geometric sums show bounded centered ordinary partial sums,
convergence of centered harmonic sums, and log-square energy limit
1+c^2/2. For every periodic v the mixed logarithmic mean with cos is0;
cos^2 has mean1/2. Thus distance from every periodic v is at leastc^2/2.
The exact scalar moment ceiling also holds for someC: E=K log N+A+O(1/N),
S=K(log N)^2/2+O(1), and E is bounded below by a positive harmonic sum.
This disproves the weaker inference from the scalar facts alone. It is
NOT a full-positive source counterexample. No redundant Lean for this
classical comparison will be written. Full C36 verdict remains
SURVIVES PRELIMINARY ATTACK; no closed paper proof, no new Lean started.

Next: audit source-specific multiplicative correlations/prime deletions
as a way to pay periodic completeness, and keep the strongest rival
(nonperiodic residual energy) alive. Do not assume multiplicativity,
coefficient signs, character means, local mass, or Fourier completeness.

C36 mechanism audit: source ThetaTrace:206 and312 retain the actual
`defectKernel (sourceDefect hW)`. Its reflected theta identity is NOT
an unqualified functional equation; Hamburger/Voronoi cannot remove
that term. The fresh finite coprime-mask Fourier expansion supplies a
finite identity only, not coefficient periodic approximation. Correlation
search68663/gen1288771 is complete,partial=false/errors=[]; all20+20
statements inspected. Prime-deletion negative-test results warn against
assuming projected/deleted sources preserve positivity.

Algebraic lead, not a proved source law: for c=mu*a, divisor smoothing
T_sigma a(n)=sum_(d|n)c(d)d^(-sigma) has Dirichlet function
zeta(s)*F(s+sigma)/zeta(s+sigma) and logarithmic source
Lambda(n)+n^(-sigma)*(lambda(n)-Lambda(n)). Do NOT assume full positivity
is preserved: such a semigroup toward Lambda would itself require a
new source-specific positivity proof. Also distinguish periodic
approximants from divisor-indicator approximants; they are different
closures. No mean-norm convergence of this smoothing is proved.

C36 needs a detector connection before further infrastructure. Zero
limiting variance alone is not pointwise coefficient rigidity: sparse
perturbations at n_k=2^(2^k) with a(n_k)-1=sqrt(n_k) have centered
log-square mass O(log log N)=o(log N) and centered summatory O(sqrt N).
This is a scalar comparison, not a full-positive source. Retain original
uniform quotient target and the full positivity hypothesis throughout.

C36 receiver audit: exhaustive text intersection of Weil*.lean files
containing WeilPositiveFull with periodic/Besicovitch/finite-type returned
53 lines, all inspected. Actual statements read:
- WeilConeInfiniteDilationRigidity:513 requires absolute convergence
  strictly past1/2 and a regular residual source.
- WeilZetaSquareRegularPartRigidity:735 requires all three finite-type
  pieces absolutely convergent past1/2.
- WeilConeAlmostPeriodicSettledLock:465 covers every producer ONLY after
  boundary continuity, an exact nonresonant lock, exponentially summable
  phase frequencies, and a power-small L1 settling remainder are paid.
C36 coefficient approximation has no proved implication to those phase
or boundary hypotheses. Do not confuse coefficient-index periodicity,
vertical Dirichlet almost periodicity, and spectral-phase periodicity.

C36 latest corpus audits complete (2026-10-08):
- BAP-rigidity deep68667/gen1288837: partial=false/errors=[]; all20+20
  statements plus ingredient sets inspected. Returned receivers still
  require boundary lock/settlement, finite residual mass, or exposed
  pairing zero. No coefficient BAP-to-detector implication supplied.
- Fractional-energy68667/gen1288840: partial=false/errors=[]; all20+20
  statements inspected. The speculative power-energy bound is
  REDISCOVERED, already in stronger COMPLEX form at
  WeilWorkSettledPhasePowerEnergy:19,135; actual source read. For
  Re(1/z)>1/2, energy grows at most log^(1/(2Re(1/z)-1)). Generic parent
  WeilWorkSettledPhasePowerLogMoment:133 also read. No duplicate Lean.
  The power disk does not include nonzero imaginary powers; these bounds
  do not settle the boundary phase or force C35 variance to vanish.
- All owned processes terminal. C34/C35 scratch and completed C36 search
  files cleaned after coverage/results were recorded. Five C35a imports
  verified at RHTower:7091-7095; new source whitespace check clean.

Current plan: retain C35 V=0 and C36 periodic completeness as OPEN;
seek a source-specific relation between forward coefficient energy and
boundary defect that pays an existing receiver. Do not create more
mean/phase infrastructure without that relation. Original WP03 uniform
quotient objective remains ACTIVE and OPEN.


### C37: actual parity residue spends residual variance

Current turn applies hgtl7. C35 V=0 and C36 periodic completeness stay OPEN.
The generic Toeplitz-saturation idea was rejected before implementation:
C27 already formalized the all-cutoff relaxation barrier. Exact positivity,
not another scalar or matrix relaxation, is still required for detection.

Exact new bridge selected: for every hW, let B be its actual residue, V its
C35a residual variance, and r>0 the actual odd/full radial ratio. Then

    |B|^2*(2*r-1)^2 <= V.

Rival: the odd radial pole carries nonzero parity bias invisible to the
logarithmic coefficient energy. Full paper attack below excludes this rival
by Abelian energy comparison and weighted Cauchy--Schwarz. This statement
links the two actual source invariants; no parity mean or analytic continuation
of the odd series is assumed. It does not imply V=0, r=1/2 or WP03 boundedness.
Verdict BRIDGE: the general Hilbert-space residue inequality is classical;
no significant scientific novelty claimed. Stronger next conjecture remains
that full arithmetic positivity makes every such variance component zero.

Plan: complete exact paper proof, formalize source bound, targeted --old/direct
Lean/axiom/lint audits, then return to the unpaid positivity mechanism.
Primary parents opened: Vaughan Dirichlet Series II, summability section
https://personal.science.psu.edu/rcv4/568s20/568chapter5.pdf ; existing C35
regular-variation sources. General converse audits opened Dixit1905.04193
and Kaczorowski--Molteni--Perelli Dirichlet converse paper: their global
continuation/functional-equation/coefficient premises remain unpaid.
Favorov--Deger2605.10766 and Favorov2311.02728 also opened; actual source
Fourier distribution has an archimedean singularity, not the pure-point
Fourier-measure hypothesis in those results. No quasicrystal shortcut.

C37 LEAN CLOSED: actual |B|^2*(2r-1)^2<=V now proved from hW alone.
Three leaves342 lines/five public theorems, targeted --old checks and
final direct source+axiom sequence48999 exit0. Only standard axioms.
Imports wired7101-7103,index95034 pass. Lint23696 has five unrelated
unwired HTGeometry modules, no owned/prohibited failure. Source theorem
ParityVariance:83. C35 V=0,C36 completeness and WP03 remain OPEN.

C38 preliminary audit (not a completed conjecture cycle):
- defect deep68683/gen1289095 returned irrelevant generic energy rows;
  proposed ingredient chain is unverified and does not concern actual
  sourceDefect. All20+20 statements inspected; partial=false/errors=[].
- covariance68684/1289114,kernel68685/1289141,tempered68685/1289165
  complete; all20+20 statements inspected. Actual NearNullPositiveDefinite
  supplies negative-definite deviationPotential from hW, already used by
  closed regular-class rigidity. No new sign on its diagonal.
- Abandon the informal tempered-deviation shortcut: source lambda has
  sqrt-scale summatory bounds, but subtracting canonical Lambda does NOT
  preserve these without a new canonical estimate. Treating delta as
  subexponential after critical normalization silently imports the
  missing RH-strength information. No theorem or Lean added for this.
- Revisit exact quotient recurrence, retaining actual exceptional orbit.
  C10 already killed square-summable ordinary-convergence=>mean-square
  via Brevig--Kouroupis2609.35496 Theorem6; actual reciprocal G has the
  stronger source estimate, but quotient order-zero remains unpaid.

C37 five anti-theatre and four anti-laziness answers posted in chat.
Exact source bridge closed, no significant scientific novelty claimed.
Next cycle must justify actual exceptional-height control, not another
unconnected scalar estimate. All C37 owned Lean/build processes terminal.

### C38: fourth moments do not remove the exceptional orbit

The proposed route was to prove actual reciprocal fourth moments, combine
them with strict-line zeta fourth moments by Holder, and obtain an actual
quotient mean-square identity without assuming quotient order zero.
This is a potentially valid classical bridge, not a detector proof.
The precise stronger inference tested was that such mean control makes
the actual quotient recurrent on compact subsets. The existing Bohr card
rows4 and7 already identify the missing exceptional-orbit step. The actual
reciprocal itself has a proved mean-square identity and a unique zero at1;
that zero cannot recur. No actual-quotient mean identity is proved here.
Verdict REDISCOVERED for the proposed detection mechanism. No duplicate
fourth-moment formalization. Positive survivor remains the already formal
actual reciprocal mean identity; retaining its fixed-line quantifiers is
essential. C38 does not retire the exact bounded-quotient objective.

External checks: Ivic--Motohashi math/0408022 (strict-line fourth moments),
Seip1206.2815 (Hardy Dirichlet zeros), and2510.05793 (actual means versus
almost-everywhere vertical limits). Seip's half-plane of absolute
convergence must not be confused with a shifted coefficient-Hardy space.
Recurrence deep68698/gen1289378 and local deep68699/gen1289385 finished
partial=false/errors=[]; all20 candidate and20 source statements read.
Their proposed ingredient sets are unverified. Source reads, especially
the actual Bohr card, were more useful than broad semantic matches.

### C39: actual sieve residue, with the cutoff limit retained

Exact conjecture: for every full-positive source there is C<infinity with
r_Q <= C*phi(Q)/Q for every Q>=1, where r_Q is its ACTUAL coprime/full
radial ratio. This would give uniform relative control of every finite
prime-deletion residue. It does not by itself imply WP03 boundedness.
Rival: r_Q/(phi(Q)/Q) is unbounded along primorials, despite finite
forward energy. [OPEN CORE]: upgrade the energy exponent1/2 to1 from
full arithmetic positivity. No multiplicativity or coefficient sign is
assumed. The conjecture is stronger than the following paper bridge.

Positive bridge selected for audit: if K is the actual forward log-energy
constant and B the actual nonzero residue, then, simultaneously for Q>=1,

    |B|^2*r_Q^2 <= K*phi(Q)/Q.

Consequently r_(primorial y) tends to0. This is a quantitative constraint
on actual increasing prime deletion, not just a finite mask identity or
a replacement of the actual function by random twists. The parent
inequality is weighted Cauchy--Schwarz, so scientific verdict BRIDGE;
novelty of a stronger linear bound remains under attack. Complete the
paper dependency audit and corpus comparison before any new Lean.

C39a paper proof now dependency-closed in PROOF.md. Toolchain probes
verified the principal-character residue, totient product, finite Euler
harmonic majorant, primorial prime factors, and harmonic divergence.
Three owned leaves CLOSED: MaskedEnergy, CoprimeEnergy, SieveResidue;
328 lines, nine public theorems. Targeted --old checks pass; final direct
source-and-axiom sequence80754 exits0. All source logs empty; all nine
axiom reports contain only propext,Classical.choice,Quot.sound. Main
masked inequalities use direct ordered-ring comparisons. Imports verified
at RHTower:7107-7109; index19714 passes. Lint66939 has11 unrelated
unreachable modules, no owned finding; global lint remains red.
C38's five anti-theatre/four anti-laziness answers were posted. Exact
WP03 uniform boundedness, C35 variance vanishing, C36 completeness, and
the stronger C39 linear bound remain OPEN.

C39 stronger-bound search: partial=true, text_retrieval and source_retrieval
interrupted; coverage68723/gen1289697, index_generation1289686. All20+20
returned candidate/source statements inspected. Hits recover fixed-Q
cosine/deviation bounds with Q-dependent constants, not a uniform linear
bound. Source logarithm is exactly the excluded lambda/(n^sigma log n)
series, with a finite fixed-Q endpoint. No interchange of radial and
prime-cutoff limits is licensed.

Next-cycle screening: generic logarithmic Tauberian transfer of masked
radial residues is a classical bridge and still leaves detection unpaid.
Do not implement it without a source-specific detector connection.
Generic Toeplitz saturation remains blocked by C27's all-cutoff witness;
full arithmetic positivity must supply the missing additional restriction.

C39 five anti-theatre/four anti-laziness answers posted. No significant
scientific novelty claimed. Source/direct/axiom processes all terminal.

### C40: prime-cutoff endpoint coherence (OPEN, paper investigation)

Given the exact corpus frontier, conjecture: for every full-positive
source, with actual residue B and actual ratios r_Q,

    B * r_(primorial N) / (phi(primorial N)/primorial N) -> 1.

B is real and positive through the actual far-right exponential and
its nonzero pole; retain the complex formula until that identification
is explicitly verified. Equivalently, if ell_Q is the real endpoint of
sourceDeletedLogarithm, the prime-cutoff endpoint
ell_(primorial N)+log(phi(primorial N)/primorial N) should converge to
log B. The sign is fixed by r_Q=exp(-ell_Q).

This asserts agreement between two distinct summation procedures for the
signed logarithmic deviation: ordinary integer cutoffs, and radial
limits after finite prime deletion. C39a proves only r_Q->0 along this
path; it does not fix this relative asymptotic. Rival: a nontrivial
prime-cutoff endpoint defect survives despite the actual finite energy,
nonzero residue and full arithmetic positivity. [OPEN CORE]: control the
complete signed remainder across increasing prime sets, without absolute
deviation summability or exchanging unproved limits.

Scientific gate: a general Tauberian theorem or another projection bound
will not close this conjecture. A proof would identify an actual
arithmetic boundary value not paid by existing fixed-Q limits. No
implication to the original uniform-height quotient is yet proved;
retain that distinction and attack the conjecture before writing Lean.

Plan: compare exact internal rough-fibre/deletion/pinning statements;
audit external summation and Euler-product parent hypotheses; try to
kill inference from existing source invariants; then investigate a
full-positivity mechanism with every mixed-prime contribution retained.

C40 attack verdict: BRIDGE, with its exact full-positive assertion still
OPEN. `WeilWorkSettledPhaseLocalPolynomialInvisibility:95` supplies a
literal nonconstant local-polynomial model with every canonical coprime
endpoint and positive period variance. It is not a full-positive source,
so does not refute C40; it kills the proposed endpoint-only detector.
Positive survivor is already formalized there: exact endpoint
invisibility with nonzero variance. No duplicate Lean is warranted.
`WeilWorkSettledPhaseUniformDivisibility:115` does provide one radial
neighborhood for every divisibility mask, with squared bound
(K+epsilon)/q; replacing divisibility by a coprime mask requires retaining
all mixed-prime inclusion-exclusion terms and does not give C40.

Exact unresolved identity: for sigma>1 let D be the logarithm of F/zeta.
Its rough part satisfies D_rough,Q = D - (deletedLog_Q + log delta_Q),
where delta_Q(sigma)=product_(p|Q)(1-p^(-sigma)). At the radial endpoint,
exp(D_rough,Q(1))=B*r_Q/delta_Q. C40 asks this to tend to1 along
primorials. Absolute convergence pays the prime-cutoff limit for each
fixed sigma>1, not interchange with sigma down to1. C39a allows this
normalized quantity to grow like delta_Q^(-1/2), hence does not close it.

Next screening: unweighted square summability of actual quotient
coefficients gives absolute convergence on Re>1/2 by Cauchy--Schwarz.
C4 already classifies any subcritical absolute quotient convergence;
this does not bypass that regularity wall. Investigate whether weakened
logarithmic harmonic deviation control is genuinely new or already
automatic/covered before selecting the next conjecture.

### C41: logarithmic harmonic rigidity (OPEN, paper investigation)

Given the exact internal and external frontier, conjecture: for every
full-positive lam, either lam(n)=Lambda(n) for all n>=2, or

    sum_(n>=2) |lam(n)-Lambda(n)|/[n*(1+log n)] = infinity.

Equivalently, summability at this exact weight forces canonicality. The
desired eventual Lean statement is the unconditional dichotomy from hW,
not a new premise attached to WP03. Existing absolute-harmonic rigidity
uses1/n; existing log-summable rigidity uses1/sqrt(n) times inverse logs.
Neither directly includes this class. Rival: full positivity permits a
nonzero deviation with finite logarithmic harmonic mass but divergent
ordinary harmonic mass. This is a proper-subclass rigidity proposal,
not yet the arbitrary-source detector.

First attack: allowing an unspecified log power would disguise the full
problem. PrimitiveSetMeanSquare:139,166 gives dyadic absolute mass
O(N log N); hence raw1/[n*(1+log n)^J] is automatically summable for J>2.
Select J=1 exactly. The existing shifted-pole notch proof has finite-part
error sum_(n<=N)|d(n)|(1+log n)/n against a main term of size log L,
with N comparable to L^2. The proposed premise only makes this error
o((log L)^2), so the old absolute envelope is insufficient.
[OPEN CORE]: retain signed arithmetic cancellation in that error or find
a different coercive use of full positivity. Do not erase this missing
logarithm by changing cutoffs without paying tail and defect terms.

Scientific challenge: find a strict boundary between harmonic rigidity
and the automatically finite high-log moments. Absolute convergence of
the logarithm at Re=1 gives boundary quotient control but does not pay a
strict half-plane bound left of1. Current converse theorems require a
functional equation/global continuation not available here. Attack this
exact statement internally and externally before attempting Lean.

C41 verdict: SURVIVES PRELIMINARY ATTACK; proof remains OPEN. The refined
notch is already stronger than the old absolute-convergence envelope.
Its Gaussian scale mixture is localized near L, not an integral over all
logarithmic scales; do not interchange it with a fictitious long average.
The exact obstruction is the localized term
(log L)/sqrt(L) * sum_(n<=cL)|d(n)|/sqrt(n), plus rough-fibre isolation.
Finite log-harmonic mass suggests good scales by averaging this term in
log L, but no complete simultaneous-scale proof or fibre-tail argument
has been obtained. Even eliminating the error does not let the cutoff
in the prime set pass through conditionally convergent harmonic sums.

For this premise the logarithm D(s)=sum d(n)/(log(n)*n^s) converges
absolutely on Re>=1. Thus the actual F/zeta and its inverse lie in the
shifted Wiener-Dirichlet algebra there; finite rough logarithmic tails
vanish uniformly on that CLOSED half-plane. This pays C40 only within
this proposed subclass. It supplies no bound on a half-plane left of1
and does not close C41 or WP03. This is a classical positive survivor,
not a claimed new theorem. No new Lean is justified yet.

Independent next-cycle screening underway: can the actual finite forward
coefficient energy constrain the integer-floor residual spectral mass?
Existing quantization already says a noncanonical source exceeds every
sublinear residual power eventually; proving a quiet power scale would
therefore close the detector. Need an actual arithmetic energy-to-mass
law, not an assumed phase lock or a generic Hardy-space inference.

### C42: logarithmic harmonic rough-sign law (paper investigation)

Energy-to-residual-mass screening has no paid source-specific link.
Saksman--Seip, arXiv:0712.0492, theorem1(ii), gives bounded ordinary
Dirichlet series with singular inner boundary behavior and arbitrarily
small coefficient square norm. This does not give a full-positive
counterexample or identify its singular measure with our integer-floor
residual measure. It blocks treating a generic Hardy-space boundary
identity as an established energy-to-mass theorem. Do not expand into
WP04 spectral quantization without an actual arithmetic connection.

Selected exact conjecture: for arbitrary full-positive lam, put
d(n)=lam(n)-Lambda(n) for n>=2 and d(0)=d(1)=0. Either
sum |d(n)|/[n*(1+log n)] diverges, or for every finite prime set P,
every Y>0 and every integer T, some k>=T satisfies

    sum_(2<=n<=k, p does not divide n for all p in P) d(n)/n < Y.

This is an unconditional alternative from full positivity; no new
premise is added to the WP03 receiver. It extends the existing rough
sign receiver from NotchSmall to a logarithmic harmonic class which
need not satisfy uniform square-root mass decay. Rival: sparse large
blocks force every useful notch scale to have a large localized error.
[OPEN CORE]: pay simultaneous scale selection for the actual Gaussian
mixture, finite cutoff, shifted-pairing tail, and defect. C41's eventual
coefficient isolation is still separate and open even if C42 closes.

Proposed mechanism: write b_n=|d(n)|/[n*(1+log n)]. Summability gives
A(X)=sum_(n<=X)|d(n)|/n=o(log X) and
T(X)=sum_(n<=X)|d(n)|/sqrt(n)=o(sqrt(X)*log X).
For every fixed c>0, F(L)=T(cL)/sqrt(L) is integrable against
dL/[L*(1+log L)] on a sufficiently large half-line, by Tonelli and
the exponential decay after setting L=exp(t). Therefore arbitrarily
late scales have F(L) arbitrarily small. With N about L^2 the pairing
tail divided by log L tends to zero by the b_n tail. A new localized
bound for the Gaussian refined error is required: the existing bound
uses a global A+B*sqrt(x) envelope and cannot simply be invoked at one
good scale. Complete this bound on paper before writing Lean.

Plan: finish exact internal/external attack; prove the Gaussian estimate
and simultaneous error vanishing; assemble the rough-sign contradiction;
only then formalize the dependency-closed statement in owned leaves.

C42 strengthened during the paper attack: logarithmic harmonic
summability is more than the proof needs. Replace it by the exact first
field of NotchSmall, A(X)=sum_(2<=n<=X)|d(n)|/n=o(log X).
The rough-sign conclusion is unchanged. The intended unconditional
alternative is now: A(X)/log X fails to tend to zero, or every finite
rough harmonic sum has liminf<=0. Finite log-harmonic mass is a corollary.

Key correction: no separate averaging theorem is needed to select a
scale. If T(X)=sum_(n<=X)|d(n)|/sqrt(n) were >=epsilon*sqrt(X)
eventually, finite Tonelli gives

  integral_1^X T(t)*t^(-3/2) dt = 2*A(X)-2*T(X)/sqrt(X).

Its lower bound epsilon*log X-O(1) contradicts A(X)=o(log X).
Thus T(cL)/sqrt(L) has liminf0 for every fixed c>0. All other errors
vanish along every scale: T(L^2)/[L*log L]<=A(L^2)/log L->0,
and partial summation bounds the shifted tail by o(log L)/L.
The localized Gaussian split at u=L/2 and u=2L now closes the one
remaining analytic estimate on paper. Detailed proof is being recorded
before Lean; no formal theorem or scientific novelty claimed yet.

C42 paper proof recorded in PROOF.md. The dependency-closed target is
primesUpTo(y), y>=2, anchored at n0=2; arbitrary-P including empty-P
is not claimed from that proof. The IsSmoothOver definition requires
2<=n0, checked directly. All Gaussian errors and the shifted tail are
accounted for. Internal attack finds the old NotchSmall receiver and
the stronger local-window-smallness sufficient condition, not this
one-field receiver. Verdict BRIDGE: useful weakening of a source
receiver by classical analysis, not significant novelty by itself.
Proceeding to owned Lean leaves, beginning with Gaussian localization.

C42 implementation checkpoint: NotchLocalization targeted --old
build26597 and NotchGoodScales targeted --old build78539 pass. Final
direct audits and wiring remain pending. The latter proves the
good-scale selection by finite summation by parts, not a subsequence
intersection. Finite tail proof recorded in PROOF.md section5 before
implementation: retain the nonnegative envelope deficit at the
terminal cutoff, then telescope the logarithmic increments. Next:
formalize that estimate, convert to the actual source envelope, and
assemble the rough-sign contradiction. WP03 and C41 remain open.

C42 checkpoint after the first three direct audits: Localization236,
GoodScales238, Tail127 lines; nine public helper theorems. Targeted
--old builds and final direct audit42126 pass; axiom/API audit10404
passes with only standard Lean axioms. These three leaves are wired.
Index4291 passes. New NotchBudget152-line leaf is under its first
targeted check. It combines every error mass at one selected scale;
does not yet bind the actual Weil source. Next assemble the generic
ramp-pairing bound from existing moment receivers, then specialize to
the hW rough sum and publish only the unconditional source alternative.
No significant novelty or completed C42/WP03 result is claimed yet.

Assembly implementation now has NotchBudget (156 lines, repair build
48617 pending at this checkpoint) and NotchSourceBound (new draft,
never checked, unwired). The latter converts the actual lower moment
and shifted-pole pairing to the four-mass bound. Its budget cutoff is
2*c, matching Gaussian localization. Remaining sequence: verify both;
derive nonpositivity of ramp partial sums under harmonic smallness;
instantiate the zero notch and actual hW. The existing absolute-series
source input is WeilSpectral.summable_abs_deviationCoeff in
WeilConeSingularDeficitEnvelope:117, sigma>1, with deviationCoeff
defined at97 as (Lambda-lam)*n^(-sigma) for n>=2. Do not use the
unrelated ConditionalDeviationRH.summable_u, which has extra datum.

Latest checkpoint: Budget48617 and SourceBound39176 targeted --old
checks PASS and both imports are wired; their direct/axiom audits are
pending. New NotchRampSign (~70 lines) proves the abstract nonpositive
ramp receiver from harmonic smallness via those two leaves. First
targeted check is running. No other owned Lean process runs in parallel.
After it passes, specialize via exists_sum_re_weightedMoment_ge_ramp
and exists_notchWeight_bound at epsilon=0; then adapt the existing
roughSum_nonpos_of_weilPositiveFull wrapper, paying summability with
WeilSpectral.summable_abs_deviationCoeff. Finish the unconditional
alternative, audit all new leaves directly and axioms, wire finished
leaves, refresh index, rerun lint. Then return to C41 isolation.

RampSign54426 targeted --old check PASS (first attempt), wired. Actual
hW adaptation and unconditional alternative are drafted in the new
NotchRoughSign leaf and its first targeted check is live. This is the
last source specialization for the paper-proved C42 target. Four final
direct/axiom audits remain (Budget, SourceBound, RampSign, RoughSign).
The first three analytic leaves were already directly audited; do not
repeat those unchanged checks. Refresh index/lint after final wiring.

C42 CLOSED as a BRIDGE, not as WP03: RoughSign33455 passes. Final
direct/axiom audit14356 passes for the remaining four leaves; together
with42126/10404 all15 public theorems are directly audited with standard
Lean axioms only. Seven leaves,1079 lines,one public definition; all
imports wired. Index97281 passes. Lint19083 has12 unrelated unreachable
leaves, no owned/prohibited finding. Main source alternative at
NotchRoughSign:109 has only hW as its source premise.

Anti-theatre: no significant scientific knowledge beyond the parent
analysis is claimed. The new formal source receiver pays a real error
gap but still does not isolate coefficients. Some effort was classical
analysis; stop extending that infrastructure now. The hardest remaining
step is arithmetic isolation or uniform prime-cutoff control, not scale
selection. No task was declined for effort; internal searches and exact
source checks were performed before implementation.

Next cycle screening: does every noncanonical full-positive source
necessarily fail harmonic smallness? This would strengthen C41's
log-harmonic mass obstruction. Rival: a sparse mixed deviation remains
harmonically small while every fixed rough-sign law holds. Neither is
selected as a surviving conjecture yet. Deep search6779 is recorded in
EVIDENCE; inspect its ingredient set and strongest exact parent inputs,
then complete external and falsification audits before new proof work.
Soundararajan2002 requires Selberg-class data not yet paid here.

C43 exact target selected for preliminary attack: every full-positive
source is canonical or fails the C42 harmonic envelope. This is stronger
than C41. Rival: harmonically small, mixed prime/composite deviations
survive all fixed arithmetic tests. Verdict SURVIVES PRELIMINARY ATTACK,
not proved. [OPEN CORE]: isolate an individual coefficient while the
prime cutoff tends to infinity; C42 fixes the cutoff before choosing
the notch scale. No uniform interchange follows from its quantifiers.

The strongest checked endpoint parent is MUST-586,
WeilOneSidedConvergenceRigidity:411/425: either sign summable against1/n
forces equality. CauchyBounded in WeilDeviationTranslationBound:290
controls d/sqrt(n) on log-line translates, much stronger than the
harmonic envelope; its vanishing packet mean cannot be assumed here.
Booker2015, arxiv1308.3067 definition1.3 and theorems1.6/1.7 require
discrete spectral data, almost-everywhere integer multiplicities and
extra coefficient decay. Those inputs remain unpaid for our source.
The WP02 sublog-fibre work concerns different separator coefficients
and does not prove C43's source hypothesis or conclusion.

C43a positive intermediate target: a noncanonical full-positive source
must either fail harmonic smallness or have infinite absolute harmonic
deviation on composite integers. Equivalently, harmonic smallness plus
summable nonprime |d(n)|/n forces every coefficient to equal Lambda.
This replaces the pointwise o(Lambda) condition in the old isolation
proof by average smallness and a composite tail. Prime deviations may
have arbitrary signs and unbounded relative spikes. The strongest
checked thin-prime-deficit parent additionally requires a summable
negative-prime set; that is not supplied here. Verdict BRIDGE pending
the exact search and completed paper proof, not significant science.
First derive the exact coefficient-isolation bound from the new ramp
receiver and the actual unconditional harmonic convergence. Continue
attacking C43's unrestricted composite core after this closure.

C43a paper proof is dependency-closed in PROOF.md. NotchIsolation144
lines has passed targeted --old build84810 after one summability-bound
binder repair; wired. CompositeRigidity89-line actual-source adapter
and alternative are drafted and under their first targeted check.
Final direct/axiom audits remain pending. No broader C43 claim.
Next competing direction C44: could composite harmonic summability
alone already force equality? The prime-power rigidity source only
rules out constant rescaling of the canonical proper prime powers;
it does not constrain arbitrary prime coefficients as needed here.
Exact deep source search98755 is running before selecting that claim.

C43a CLOSED as a BRIDGE: both targeted builds and both final direct
leaf checks pass; repaired API and all three axiom audits96782 pass.
Only propext, Classical.choice, Quot.sound. Two leaves,233 lines,three
public theorems. Index passes; lint has eight unrelated unreachable
leaves (exact names in EVIDENCE), no owned finding. RESULT and frontier
updated. The full C43 conjecture and WP03 remain OPEN.

Anti-theatre: no significant scientific novelty claimed. The contribution
closes one formal coefficient-isolation gap using classical machinery;
it does not close unrestricted arithmetic detection. Anti-laziness: no
step was deferred for effort; exact corpus parents were checked. Next
cycle targets arithmetic lower bounds rather than more error estimates.

C44 screening98755 and propagation73445 have completed; their proposed
ingredient sets leave the key source obligations unpaid. Higher-moment
screening finds an untwisted fourth-moment upper bound in the corpus and
primary twisted-moment formulas of Bettin et al. (2016/2020), Bui--Hall
(2023), and Bui--Hall--Subira Jorge (2025). Their short, structured or
subpower-bounded polynomials do not immediately cover the actual long
deviation sum. No higher-moment no-go or proof is claimed. Next examine
whether finite arithmetic-fibre positivity can yield a common bounded
functional and recover coefficients without absolute composite tails;
deep search22211 was launched for that exact mechanism.

C46 screening: the exact old NotchBochnerLaw theorem proves a real
quadratic inequality for convergent gcd-harmonic sums. Its prose claims
every negative-mass torus measure is allowed, but the module contains
no converse realization theorem; do not promote that prose into an
arithmetic counterexample. Since its kernel can be asymmetric, only its
symmetric part is observed by the displayed real quadratic form.

C47 candidate under attack: let f(n)=mu(n)*2^(-omega(n)), with f(1)=1,
and d=f-delta_1. Hypothesis to establish: d is nonzero, bounded, has
finite sum |d|/[n(1+log n)], ordinary harmonic sum -1, and all fixed
gcd-harmonic sums -1; hence all limiting notch quadratic laws hold.
This would falsify inference from those limiting laws plus C41's mass
condition to coefficient equality, not falsify full-positive rigidity.
The candidate must also be tested against actual source continuation:
its Euler series has a square-root zero at1, whereas the actual source
deviation is holomorphic there. Primary Selberg--Delange estimates
(Granville--Koukoulopoulos2019 theorem1) are being checked; no numerical
experiment. [OPEN CORE] pending exact convergence and fibre identities,
not yet a completed paper proof or a formal counterexample.

C48 screening: local analyticity at1 plus null divisibility fibres and
sublogarithmic absolute harmonic mass is a competing abstract uniqueness
conjecture, not a theorem. Deep search79615 has no verified receiver;
its proposed finite Mobius inversion does not pay the infinite tail.
Do not infer a source theorem from this abstract conjecture.

C49 SELECTED FOR HOSTILE AUDIT, 2026-10-08. Exact proper-class conjecture:
let f be a real multiplicative arithmetic function, f(1)=1, and suppose
there is 0<=theta<1 with |f(p^k)|<=theta for every prime p and k>=1.
Set lambda(n)=Lambda(n)+f(n) for n>=2. If lambda is full-positive, then
f is the Dirichlet-convolution unit. No source satisfying this profile
is assumed to exist; this is not the full WP03 detector.

Proposed mechanism: source continuation makes F=L(f) analytic at1.
Positive real Euler factors give F(1+t)>=c*t^theta, so analyticity
excludes F(1)=0. Write H=F(1)>0. Fixed-prime convolution inversion at
the harmonic endpoint supplies all gcd-fibre limits. The actual notch
quadratic law should then yield, for every finite prime set P,
  H*Re product_p F_p(p^(-1/2) z_p) <= product_p F_p(p^(-1)), |z_p|=1.
Local maximum-modulus estimates and conjugate phase choices should
force sum_p |f(p)|/sqrt(p)<infinity. Higher prime powers then give
absolute convergence at every sigma>1/2, entering an existing rigidity
class. [OPEN CORE] audit this full chain, especially NotchSmall,
finite-prime endpoint convolution, and the real-quadratic-to-pointwise
step. No C49 Lean code before a dependency-closed proof.

This strengthens the C47 lesson: ordinary limiting tests alone admit
classical null expansions; the proposed exclusion uses source
analyticity and multiplicativity together. It must be compared with
Brevig--Heap's abscissa theorem and existing carrier/sign-alignment
rigidity, not advertised as new merely because it is new in Lean.

C49 PAPER PROOF CLOSED in PROOF.md, six steps. The final version uses
one-variable Borel--Caratheodory on a diagonal disc, avoiding phase
selection. A bound on the real part of each finite Euler product gives
a product-norm bound on its half polydisc, with a constant independent
of the number of primes. First-coefficient estimates then force
sum_p |f(p)|/sqrt(p)<infinity. Multiplicativity upgrades this to
absolute convergence at every sigma>1/2; existing endpoint rigidity
closes the class. This proof still needs its exact Lean audit.

First C49 leaf EulerDisk drafted and wired. Targeted build4170 failed
only on an unnecessary product congruence after convert; API check and
repair build71008 pass. Final direct audit95464 pending. Its two
analytic lemmas are standard bridges, not the C49 source theorem.
Remaining formal steps: local coefficient/log-product bound; actual
endpoint Euler-factor removal; source nonzero harmonic value;
NotchSmall from the strict local bound; exact Fourier/notch density
identification and capstone. No full/umbrella build or computation.

C49 update: EulerDisk final direct audit95464 and standard-axiom audit96096
PASS. An accidental overlap of those two audit processes is recorded
in EVIDENCE; both exited. Torus-sign formalization uses density of the
character span, continuity of the quadratic integral and full support
of Haar measure. Scratch work only so far. Actual-source Fourier
identification and all arithmetic C49 obligations remain unpaid in Lean.

C50 SCREENING ONLY while C49 formalization continues: the strict theta<1
boundary exposes f=mu as an integer-order-zero profile. Here F=1/zeta
has H=0, so the endpoint notch laws lose its information. At a regular
critical-line point, Re(xi'/xi)=0. If the actual continuation for
lambda=Lambda+c*mu is xi'/xi-c/zeta, Herglotz positivity would require
-c*Re(1/zeta)>=0 there. A proved sign change of Re(zeta) on the critical
line could exclude every nonzero c without RH or numerical zero data.
Corpus search launched for this exact mechanism before selecting any
conjecture. This is not a theorem, not a new premise, and does not
replace the unpaid C49 formal work. Check normalization and boundary
regularity against the actual source definitions first.

C50 normalization correction during hostile audit: the deviation is
c*(mu-delta_1), since lamC discards n=1. The actual continuation would be
xi'/xi + c - c/zeta, not xi'/xi-c/zeta. Thus the boundary inequality is
c*(1-Re(1/zeta))>=0; mere sign change of Re(zeta) is insufficient.
The existing boundary-Mobius receiver has the explicit premise f(1)=0,
so substituting f=c*delta_1 is invalid. Do not call this rediscovered or
proved. A nonzero-residue phase argument is a possible next attack,
subject to corpus search. This correction is why the exact source
normalization must precede any new formalization.

C49 TorusSign formal checkpoint: 221 lines, five public theorems. Direct
leaf audit56279 and axiom audit70884 PASS (standard Lean axioms only).
Imports wired. The exact source adapter retains the Fourier identity
and gcd-limit obligations explicitly; it does not assert their existence.
Next formal chunk is the ordinary-times-absolute harmonic convolution
lemma. Scratch written; no arithmetic lemma has yet passed Lean.
C50 also fails C49's mean-smallness input at theta=1; |mu| has positive
mean. Its boundary case is screening only, with normalization corrected.

C49 HarmonicConvolution formal checkpoint: six public theorems, including
ordinary-times-absolute endpoint evaluation, a same-endpoint absolute
inverse under strict harmonic norm contraction, and scalar inverse
product evaluation. Targeted --old36086, final direct31719 and all six
axiom checks17088 PASS; standard axioms only. Module wired. The next
step instantiates this with prime-local restrictions and proves their
exact smooth/rough convolution decomposition. Paper proof already
supplies the required finite-prime argument; no C49 capstone yet.

C49 PrimeDeletion formal checkpoint: 15 public theorems. Exact smooth/
rough Dirichlet factorization and finite-prime deletion at the ordinary
harmonic endpoint, with explicit product of local Euler factors in the
denominator. Each inverse follows from the sharp theta/(p-1)<1 bound.
Scratch2674, final direct59652 and axiom91476 PASS, standard axioms only.
Leaf wired; no dependency or umbrella rebuild. Next: compute gcd-weighted
limits via finite Euler summation, then construct their Poisson density.
The strict-profile NotchSmall and nonzero-source-value obligations also
remain open in Lean. This checkpoint is a BRIDGE, not a C49/WP03 solution.

C49 GcdEuler formal checkpoint: 237 lines, ten public theorems. It pays
the exact gcdHarmonicSum limits for Re(f)-delta_1, including the -1 at
the harmonic endpoint. Finite Euler absolute summation, multiplicativity
of the bounded gcd weight, and its unchanged rough restriction are
proved. Final direct14744 and axiom64525 PASS (standard axioms only);
module wired. Index/lint92027 refreshed the corpus; six unrelated
unreachable modules, no owned/prohibited finding. Next actual identity:
continuous Poisson/Euler density on the finite additive torus. Existing
PrimePoissonProductState/CirclePoissonFiniteProduct supply kernel moment
and product-density parents; their source Fourier identification is
still to be composed with this new arithmetic theorem.

C49 PoissonEuler formal checkpoint: 265 lines, nine public theorems.
Positive continuous additive-circle Poisson kernels, exact Fourier
coefficients of bounded analytic local series, and the finite-product
Euler density including its subtracted Poisson product are now proved.
Final direct37080 and all nine axiom3087 checks PASS (standard axioms
only); leaf wired. Next scratch identifies r=p^(-1/2), local gcd Euler
values and the literal twistGramWeight, then joins the source notch law.
Strict-profile NotchSmall, H>0 and the final prime-tail rigidity upgrade
are still unpaid. C49 remains a paper theorem awaiting full formalization.

C49 SourceEuler formal checkpoint: exact twistGramWeight normalization,
real gcd-harmonic endpoint, literal source deviation normalization and
finite Euler inequality. Ordinary H exists by the source theorem; no
Fourier or convergence hypothesis is laundered. Final direct91948 and
all13 axiom93332 checks PASS, standard axioms only; leaf wired. Index
and lint complete (six unrelated unreachable modules). NotchSmall,
H>0 and the summability/rigidity capstone remain unpaid. Next scratch
uses the finite-prime majorant product (theta on multiples, one off)
and exact counting of multiples to prove absolute mean decay. All
local-mass search hits audited; no existing producer supplies this step.

C49 MeanSmall formal checkpoint: absolute finite-prime attenuation,
exact mean by counting multiples, prime-reciprocal-driven mean zero,
generic local logarithmic mass decay and literal NotchSmall. Final
source corollary removes every smallness/convergence premise from the
finite Euler bound and supplies H<=1. Direct6389 and all10 axiom6832
checks PASS; leaf wired, no unchanged/umbrella rebuild. Index/lint
complete; eleven unrelated unreachable modules. Next: prove H>0 via
uniform local log lower bound, Euler-product limit, actual analytic
source germ and ordinary Abel endpoint. Positivity scratch82390 running.

C49 PositiveEuler formal checkpoint: local series lower bound and
uniform log Taylor remainder, exact weighted multiplicative Euler
product, and global F(sigma)>=c_theta*norm(zeta(sigma))^(-theta).
Final direct19265 and all9 axiom77020 checks PASS; leaf wired, index
complete, lint running. Ordinary Abel scratch77368 runs next. Remaining
endpoint work identifies H with G(1) for actual G=1+xi'/xi-Phi and
excludes an analytic zero using the fractional lower bound. Prime-tail
summability and the rigidity capstone remain after that.

C49 HarmonicPositive formal checkpoint: ordinary Abel limit, actual
source germ G=1+xi'/xi-Phi, exact G(1)=H and fractional lower bound
versus analytic zero prove H>0. Final direct13882/all14 axiom96206 PASS;
standard axioms only. Leaf wired, index2431 PASS. Lint27233 reports
five unrelated HTGeometry unreachable leaves. Next: finite polydisc
maximum principle and exact Caratheodory first-coefficient bound using
existing HTGeometry/CaratheodoryCoefficient.lean. Scratch44944 running.
No prime-tail/class completion claim; no scientific novelty established.

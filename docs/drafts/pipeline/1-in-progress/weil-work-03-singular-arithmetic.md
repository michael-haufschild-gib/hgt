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

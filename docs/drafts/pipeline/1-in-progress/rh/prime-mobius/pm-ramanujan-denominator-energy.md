# PM natural-denominator Ramanujan energy

- **ID:** pm-ramanujan-denominator-energy
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [PM31](pm-power-damped-mobius-haar.md);
  [actual cumulative energy](pm-centered-divisor-dyadic-energy-budget.md)
- **Statement:** For each positive damping, the centered Ramanujan
  expansion cut off by its natural denominator has a common finite
  anchored cumulative-energy budget.

## Exact carrier and proposed budget

Use the actual divisor coefficient c_epsilon and its real density alpha
from the audited PM leaves. Define the real Ramanujan coefficient

    r_q(n) = sum_(d | gcd(q,n)) d*mu(q/d),  q>=1,
    a_epsilon(q) = sum_(m>=1) mu(q*m)/(q*m)^(1+epsilon).

The first task is to prove, for each n>=1 and epsilon>0, the absolutely
convergent identity

    c_epsilon(n) = sum_(q>=1) a_epsilon(q)*r_q(n).

Here r_1(n)=1 and a_epsilon(1)=alpha_epsilon. Consequently define

    b_(epsilon,Q)(n) = sum_(2<=q<=Q) a_epsilon(q)*r_q(n),
    D_(epsilon,Q)(N) = sum_(1<=n<=N) b_(epsilon,Q)(n).

The new, unproved producer is

    for each epsilon>0, exists B_epsilon, for every Q and T,
    sum_(1<=N<=T) D_(epsilon,Q)(N)^2/(N*(N+1)) <= B_epsilon.

No uniformity in epsilon is requested. Finite T and coefficientwise
convergence would pass this inequality to the actual D_epsilon(N).
The existing discrete-energy criterion would then give PM admission,
and cofinally small positive dampings would give RH. This is only a
sufficiency argument; necessity of this particular approximation budget
has not been established.

## Paper bridge to audit

The corpus's exact gcd--Mobius Ramanujan divisor formula suggests

    sum_(q|d) r_q(n) = d * 1_(d|n).

Insert this into the actual finite divisor sum for c_epsilon(n), written
as a sum over all d with coefficient mu(d)/d^(1+epsilon). Rearranging
q|d, d=q*m, gives the proposed expansion. For fixed n, the divisor formula
bounds |r_q(n)| by sum_(k|n) k, independently of q. Thus the absolute
double sum is bounded by that fixed constant times

    sum_(d>=1) tau(d)/d^(1+epsilon),

which is covered by the divisor-square majorant already used in the
second-moment leaf. All series rearrangements must be justified with
this bound in Lean. No global physical L2 interchange follows from the
pointwise identity.

## Why this remains an arithmetic producer

The cutoff is q<=Q. It is not a finite-prime aperture, whose small-damping
physical budgets have already been disproved. Translation-averaged
Ramanujan orthogonality, Bohr mean-square approximation, coefficient
variance, and the summability of the diagonal do not supply this anchored
bound. The actual signed mixed-denominator terms must be retained.
No assumption of independent integer samples or of RH is admissible.

## Gates

- [x] Exact arithmetic carrier and sufficient budget specified
- [x] Prior corpus search1101--1103 reviewed on the parent producer card
- [x] Exact divisor expansion novelty/applicability audit complete
- [x] Pointwise bridge formalized with absolute rearrangement justified
- [ ] Proposed common energy budget proved on paper
- [ ] Exact producer formalized and all audits passed

## No-go closure

No obstruction to this natural-denominator budget is established. If it
fails, retain the exact expansion and identify which cutoff boundary or
mixed-denominator term causes failure. A failed absolute-value estimate
does not refute the signed budget. Any dependency-closed positive survivor
must be formalized before retiring the candidate.

## Log

- 2026-10-01 — Opened from the actual Ramanujan divisor-convolution hits
  in search1103, after the small-damping variance scratch passed. Search1104
  checks `Ramanujan divisor expansion` before new Lean code. The paper
  rearrangement and producer above remain unaudited; no RH progress is
  inferred from a representation change alone.

- Search1104 (`Ramanujan divisor expansion`, deep): all20 candidate/all20
  source statements and both generated steps reviewed. The actual
  gcd--Mobius coefficient formula and divisor-seed convolution are proved
  in the corpus. Their one-variable Dirichlet series evaluates a different
  weighted sum; it does not directly give the proposed expansion of
  c_epsilon. Estermann progression bounds and native Eisenstein product
  formulas have different carriers, so the generated chain does not prove
  this bridge or its energy budget. Partial=false;63965files;
  index/coverage1176729,current1176740;semantic coverage unmeasured,
  background refresh incomplete. No exact PM expansion returned.
- Inspected the literal convolution and divisor formula in
  `ThetaCuspHawkingBMEisensteinRamanujanDirichletSeries` and the independent
  sieve divisor-formula leaf. Finite Ramanujan inversion follows by
  convolving the divisor seed with mu and then zeta. Next establish the
  absolute rearrangement and identify the q=1 density exactly.

- First scratch1105 passed with empty diagnostics: exact finite divisor
  inversion, Ramanujan norm bounded by the fixed integer's divisor mass,
  definition of the actual multiple weight and its q=1 density identity.
  No module has been promoted. The absolute two-index domination can be
  made more direct: |mu(q*m)|<=1 and the product power law bound the pair
  kernel by C_n*q^(-1-epsilon)*m^(-1-epsilon). Two convergent p-series
  justify grouping by d=q*m without a new divisor-count estimate.

- Scratch1105 extended with the actual two-index summability proof,
  exact multiplication-fiber sum, and the proposed absolutely convergent
  c_epsilon expansion. Full check now running. The grouping explicitly
  kills the infinite zero fiber with the actual zero coefficient before
  replacing positive fibers by finite divisor antidiagonals.
- Next arithmetic audit (search1106): evaluate a_epsilon(q) itself using
  coprimality and the absolutely convergent Euler product. If the proposed
  formula alpha*mu(q)/product_(p|q)(p^(1+epsilon)-1) is verified, the finite
  q-cutoff can be rewritten as a particular signed divisor cutoff with
  explicit incomplete positive cofactor sums. This is a potential way to
  study its actual mixed terms, not an assumed energy estimate. The
  coefficient formula and cutoff rewrite still need paper/Lean checks.

- The extended scratch check exposed an inference timeout in the pair
  summability application and a missing explicit two-variable function
  in the divisor-antidiagonal rewrite. Split the pointwise norm estimate
  into its own theorem, typed the real summable majorant explicitly, and
  supplied the missing function arguments. No heartbeat limit raised;
  the corrected full check is running.
- Search1106 (`Ramanujan Mobius coefficients coprime Euler product`,
  deep): all20 candidate/all20 source statements and both proposed steps
  reviewed. General multiplicative Euler-product infrastructure applies
  once absolute convergence and the exact local factors are supplied.
  Coprime-support convolution identities are conditional algebra, not
  the required evaluation of this actual multiple sum. Primitive Fourier
  two-level conservation concerns a different operation. Other hits are
  unrelated algebra/character carriers. No exact coefficient evaluation
  or PM energy estimate returned. Partial=false;63970files;
  index1176924,coverage/current1176928;semantic coverage unmeasured,
  background refresh incomplete.

- Corrected scratch1105 passed with empty diagnostics, including actual
  double-series summability, exact fiber grouping, and the absolutely
  convergent c_epsilon expansion. Extended the draft to centered natural
  denominator prefixes, cumulative-prefix convergence, finite-energy
  convergence and the sufficient-budget handoff. This extension is now
  checking. Its range index Q retains denominators 2 through Q+1, so the
  zero prefix is exactly zero; it introduces no spurious density term.

## Exact multiple-weight evaluation: paper proof

For s=1+epsilon>1 and q>=1, the proposed coefficient formula has a direct
prime-peeling proof, without an interchange of infinite Euler products.
Write w(k)=mu(k)/k^s. Absolute convergence follows from the p-series
majorant already used for the expansion. For a prime p not dividing q,
the actual Mobius identity gives

    w(p*q*m) = -p^(-s)*w(q*m) if p does not divide m,
    w(p*q*m) = 0 otherwise.

The sum of w(q*m) over p|m is exactly a_epsilon(p*q), by the injective
reindexing m=p*l. Therefore

    a_epsilon(p*q) = -p^(-s)*(a_epsilon(q)-a_epsilon(p*q)),
    (p^s-1)*a_epsilon(p*q) = -a_epsilon(q).

Since p^s-1>0, this determines the new prime factor. Starting at the
already verified a_epsilon(1)=alpha, finite induction on a squarefree q
gives

    a_epsilon(q) = alpha*mu(q)/product_(p|q)(p^s-1).

For nonsquarefree q, every mu(q*m) is zero, so both sides vanish. This
closes the paper evaluation for every positive q. The corpus's
`Sieve.CoprimeMoebiusSeries` proves the analogous reindexing at exponent
two for one deleted prime; its proof confirms the needed support and
summation operations. The exact general-parameter recurrence and finite
  induction above still require Lean formalization. The centered energy
  budget remains open.

- Full scratch1105 passed with empty diagnostics, including all centered
  prefix, cumulative prefix, finite-energy limit and conditional budget
  handoff statements. Promoted/wired `PMPowerDampedMobiusRamanujanExpansion`;
  targeted build and final audits now running. The budget itself is not
  proved, and this card remains in progress.

- Ramanujan leaf:245 lines /21 declarations; targeted old build37s,
  exact-body/exhaustive names/API/unique-import/no-proof-debt audits and
  final actual `lake env lean` with empty diagnostics passed. Twenty-one
  axiom reports now running. Scratch1107 drafts the prime-peeling weight
  recurrence and nonsquarefree vanishing; it is not compiled yet.

- Actual Ramanujan expansion fully audited:
  `PMPowerDampedMobiusRamanujanExpansion` (245 lines /21 declarations),
  targeted old build37s, final actual-leaf check with empty diagnostics,
  all21 standard-axiom reports, exact body, exhaustive names/API, unique
  import and no-proof-debt checks passed. The literal coefficient has an
  absolutely convergent Ramanujan expansion; centered natural-denominator
  prefixes converge, as do every fixed cumulative sum and finite energy.
  A common cutoff-energy budget would give actual PM admission, but that
  budget remains unproved. Combined: thirty-five leaves /8485 lines /625
  audited declarations. Global lint reports eleven unrelated unwired
  leaves and stale API/overview, no owned/proof-debt finding; no global
  pass claimed. The explicit multiple-weight Euler formula has a paper
  proof and a draft Lean proof, not yet checked. RH remains open.

## Finite-cutoff cofactor mechanism to audit next

For the natural denominator cutoff Q>=1, expand each Ramanujan partial
sum by its divisor formula. The coefficient multiplying floor(N/d) is

    z_(epsilon,Q)(d) = d * sum_(m<=Q/d) mu(m)*a_epsilon(d*m).

Finite Mobius inversion gives the exact density constraint
sum_(d<=Q) z_(epsilon,Q)(d)/d=alpha. Thus the centered cumulative cutoff
is also -sum_(d<=Q) z_(epsilon,Q)(d)*frac(N/d), with no residual linear
density term. Inserting the paper multiple-weight formula makes each
nonzero z coefficient its original Mobius sign times an incomplete
positive coprime cofactor sum. Its relation to the corpus's Selberg
quadratic minimizers needs an exact carrier audit (search1108).

This finite reorganization is a candidate analysis tool. Even an exact
Selberg optimality identity for a divisor/lcm quadratic does not supply
the fixed-origin weighted cumulative energy. No comparison of those
  two quadratic forms is assumed. The finite rewrite, the cofactor
  normalization and any useful energy comparison still need verification.

- First scratch1107 check accepted the recurrence and full Euler formula
  apart from two API errors: an unavailable zero-tsum shortcut and an
  implicit Mobius argument supplied positionally. Replaced the first by
  explicit termwise vanishing and named the second argument. Added the
  actual density's strict positivity and the Mobius-aligned sign of every
  expansion weight; corrected full check now running.
- Search1108 (`Selberg optimal weights Ramanujan divisor quadratic`,
  deep): all20 candidate/all20 source statements, the proposed transfer
  and both ingredient steps reviewed. The Selberg inversion leaf gives
  exact diagonal variables, inverse transform and optimal sieve main
  term. These concern the sieve's divisor/lcm quadratic and retain an
  arithmetic remainder. Neither bounded sieve coefficients nor divisor
  counts bound the PM anchored cumulative energy. Quadratic character
  averages and CGL traces use different carriers. The generated transfer
  does not supply the required comparison or remainder bound.
  Partial=false;63976files;index1177155,coverage1177158/current1177159;
  semantic coverage unmeasured and background refresh incomplete.

- Corrected scratch1107 passed with empty diagnostics: actual prime
  recurrence, nonsquarefree vanishing, finite Euler denominator, its
  positivity, full multiple-weight formula, realness, positive density
  and Mobius-aligned signs. Added the exact probability normalization:
  r_q(1)=mu(q), the already verified expansion at n=1 sums to c(1)=1,
  and the aligned sign makes mu(q)*a(q)=|a(q)|. Therefore sum_q|a(q)|=1.
  The extended normalization proof is now checking. This scalar l1 norm
  does not bound cumulative kernels whose physical norms grow with q.

- The normalization extension reduced to one sum-congruence API issue:
  `HasSum.congr_fun` takes the replacement equality in the reverse
  direction. Supplied the symmetric termwise equality; full recheck
  running. No mathematical change or heartbeat adjustment.

- Scratch1107 normalization passed with empty diagnostics. Promoted and
  wired `PMPowerDampedMobiusRamanujanWeights` (230 lines /17 declarations);
  targeted old build and formal audits underway. The exact formula,
  positivity, signs and total absolute mass one are unconditional for
  positive damping. They do not supply the anchored energy budget.
- Search1109 (`Ramanujan primitive fractional part`, deep): all20
  candidate/all20 source statements and both ingredient steps reviewed.
  The actual PM expansion is already proved; zeta fractional-part
  integrals and individual cell formulas do not evaluate the finite
  Ramanujan primitive. The suggested Niven rational-angle step has no
  applicable premise here. Other hits concern unrelated ramified fields,
  character slopes or arithmetic representations. No cutoff identity or
  energy bound returned. Partial=false;63978files;index1177229,
  coverage1177231/current1177232; semantic coverage unmeasured and
  background refresh incomplete. Search1111 broadens to the finite
  divisor/floor-sum mechanism.

- Search1111 (`sum Ramanujan coefficients divisors floor natural cutoff`,
  deep): all20 candidate/all20 source statements and both ingredient
  steps reviewed. Exact divisor inversion/gcd formula and PM floor
  summation apply to the finite rewrite. The lcm quadratic computes
  local divisor-coefficient squares, not cumulative-prefix energy; CGL
  and Kloosterman identities retain their own remainder terms. The
  generated affine-Poisson step does not remove a cutoff remainder.
  Partial=false;63982files;index1177287,coverage1177297/current1177298;
  semantic coverage unmeasured, background refresh incomplete.
- Weight leaf targeted build passed; exact-body, exhaustive names/API,
  unique-import and no-proof-debt audits passed. Global lint has twelve
  unrelated unwired leaves, no owned/proof-debt issue; no global pass
  claimed. Final actual-leaf and all17 axiom checks remain.

- Actual Ramanujan weights fully audited:
  `PMPowerDampedMobiusRamanujanWeights` (230 lines /17 declarations),
  targeted old build160s, final actual-leaf check with empty diagnostics,
  all17 standard-axiom reports, exact-body/exhaustive names/API/unique
  import/no-proof-debt checks passed. The coefficient is exactly
  alpha*mu(q)/product_(p|q)(p^(1+epsilon)-1), is real with Mobius-aligned
  sign, and has total absolute mass one. These are unconditional for
  every positive damping, including nonsquarefree vanishing and q=0.
  Combined: thirty-six leaves /8715 lines /642 audited declarations.
  Global lint reports twelve unrelated unwired leaves, no owned or
  proof-debt finding; no global pass claimed. The finite cofactor rewrite
  is checking next. No small-positive anchored energy budget or RH proof.

## Full cofactor normalization candidate

For fixed d>=1, absolute multiple inversion should give

    sum_(m>=1) mu(m)*a_epsilon(d*m) = mu(d)/d^(1+epsilon).

Expand a and group by k=m*l. Absolute convergence follows from the
product p-series majorant (or the already summable Ramanujan pair at
n=1 restricted through (m,l)->(m,d*l)). Each k-fiber contributes
w(d*k)*sum_(m|k)mu(m); only k=1 remains. For squarefree d,
mu(d)*mu(m)*a(d*m)=|a(d*m)|: noncoprime products vanish, and coprime
products use multiplicativity. Thus the total mass on multiples of a
squarefree d is exactly d^(-1-epsilon). Every finite cofactor z_Q(d)
then has its original Mobius sign and |z_Q(d)|<=d^(-epsilon). This
would identify the finite cutoff as an exact positive attenuation of
the original signed divisor weights. It is not a bound on their
cumulative physical energy. Search1113 checks prior multiple inversion
before this extension is formalized.

- Search1113 (`Mobius Ramanujan multiple inversion cofactor mass`, deep):
  all20 candidate/all20 source statements, one proposed transfer and both
  ingredient steps reviewed. The actual useful hit is the general
  `DeletionMixedRefinement.moebius_multiples_inversion`, reached through
  its remainder specialization: it already proves positive-index
  inversion under absolute product-index summability. The weighted
  Lambert variant proves the same cancellation with extra weights.
  Finite incidence-algebra inversion alone does not justify an infinite
  swap, and prime-power conservation has a different carrier. The
  general inversion can be reused after the actual PM power majorant
  discharges its summability premise. Partial=false;63985files;
  index1177368,coverage1177383/current1177385; semantic coverage
  unmeasured and background refresh incomplete. No energy bound returned.

- First finite-cofactor scratch1112 check found three elaboration issues
  (an implicit bivariate function, an unspecified integer argument, and
  an implicit cast function). Corrected them and added the literal
  centered-prefix floor/fractional-part identities. The next check
  accepted the finite expansion, exact floor sum and density constraint;
  its extension needed an explicitly selected interval endpoint and
  explicit real-to-complex casts. Corrected full recheck running.
- Draft1114 reuses the existing general infinite multiples inversion,
  with the actual double absolute convergence proved from product
  p-series. Its target is the exact multiple mass and cofactor
  attenuation above. It has not been checked yet.

- Finite cofactor scratch1112 passed (one unused `congr` removed in the
  combined draft). The literal natural-denominator cumulative prefix is
  exactly minus the finite cofactor-weighted fractional-part sum; the
  linear density term cancels by finite Mobius inversion.
- Combined scratch1114 accepted the actual double absolute convergence,
  infinite multiples inversion and pointwise Mobius-aligned pair
  identity. Two downstream elaboration issues remained: unfolding a
  composed summable function and restricting the real-part rewrite to
  its outer product. Corrected recheck running, with the resulting exact
  multiple mass and finite cofactor norm bound included. No producer
  bound is inferred before this check or from the coefficient bound.

- Search1115 (`Ramanujan cumulative energy signed mixed denominator
  cancellation`, deep): all20 candidate/all20 source statements and
  both proposed steps reviewed. The actual Ramanujan summability is
  pointwise. Euler-deletion cumulative energies, reflected-source
  identities and martingale/drift decompositions retain their distinct
  carriers and boundary/drift terms. Eta finite-energy differences and
  elementary pair-energy identities do not compare with the PM
  denominator cutoff. No signed common energy bound or applicable
  producer returned. Partial=false;63988files;index1177519,
  coverage1177527/current1177531; semantic coverage unmeasured and
  background refresh incomplete.

- Combined scratch1114 passed with empty diagnostics. Promoted/wired
  `PMPowerDampedMobiusRamanujanCofactors`; targeted old build and audits
  now running. Exact finite expansion, cumulative floor/fractional-part
  identities, density cancellation, full multiples inversion and exact
  multiple mass are proved. The finite cofactor is Mobius-aligned and
  has norm at most d^(-epsilon) for d>=1. Its absolute-value energy
  estimate still has the existing half-damping barrier; the signed
  common cutoff-energy budget remains open.

## Next proposed comparison: logarithmic denominator square mass

Test whether the actual natural-denominator family satisfies a uniform
comparison of its cumulative energy with

    sum_(2<=q<=Q) q*log(2*q)*|a_epsilon(q)|^2.

A constant independent of Q and T is required; dependence on epsilon
would still suffice for the PM budget. The exact multiple-mass formula
implies |a_epsilon(q)|<=q^(-1-epsilon) for q>=1 (use its m=1 term),
so this proposed right side is summable for every epsilon>0. The
comparison itself remains wholly unproved. Search1117 checks prior
Ramanujan/Hilbert/logarithmic Gram bounds before pursuing it.

Do not generalize the proposed comparison to arbitrary coefficients,
arbitrary retained denominator sets or finite-prime apertures: those
are different carriers, and the existing finite-aperture no-go must be
audited before any such transfer. The needed estimate must retain the
actual Mobius/Euler coefficients and natural denominator cutoff.

- Search1117 (`Ramanujan partial sums Hilbert inequality logarithmic
  weighted Gram`, deep): all20 candidate/all20 source statements and
  both proposed steps reviewed. Scalar log/power bounds support the
  proposed coefficient square-mass summability. Montgomery--Vaughan
  eigenvalue bounds need their frequency/separation carrier; no
  identification with the PM primitive Gram was returned. Riesz
  partial-sum estimates retain unproved sum/increment premises; other
  Hilbert/trace identities have different carriers or encode RH. The
  generated log-decay chain proves no physical-energy comparison.
  Partial=false;63990files;index1177583,coverage1177591/current1177592;
  semantic coverage unmeasured and background refresh incomplete.
- Draft1118 proves the coefficient side using the exact cofactor
  bound at Q=d and log(2q)<=2^epsilon*q^epsilon/epsilon. This gives
  q*log(2q)*|a(q)|^2 <= (2^epsilon/epsilon)/q^(1+epsilon), an absolute
  p-series majorant. The scratch has not been checked; the proposed
  physical Gram comparison has no proof.

- Actual Ramanujan cofactors fully audited:
  `PMPowerDampedMobiusRamanujanCofactors` (286 lines /18 declarations),
  targeted old build49s, final actual-leaf check with empty diagnostics,
  all18 standard-axiom reports, exact-body/exhaustive names/API/unique
  import/no-proof-debt checks passed. Natural-denominator cumulative
  prefixes are exactly finite cofactor-weighted fractional-part sums,
  with exact density cancellation. Absolute multiples inversion gives
  the exact mass on squarefree multiples; cofactors preserve Mobius
  signs and have norm at most d^(-epsilon). Combined: thirty-seven
  leaves /9001 lines /660 audited declarations. Global lint has ten
  unrelated unwired leaves and no owned/proof-debt finding; no global
  pass claimed. A proposed logarithmic coefficient-square comparison
  remains unproved; its summable coefficient side is being checked.
  No small-positive anchored energy budget or RH proof.

## Primitive-period mechanism to audit

For q>1, let R_q(N)=sum_(1<=n<=N)r_q(n). The candidate exact period
identity is

    sum_(1<=N<=q) R_q(N) = -q*phi(q)/2.

The proposed proof uses only the Ramanujan divisor formula: each d|q
has sum_(N=1..q)floor(N/d)=q^2/(2d)+q/d-q/2; the constant terms cancel
by sum_(m|q)mu(m)=0, leaving the totient convolution. Equivalently the
even symmetry of r_q pairs its first moment around q/2. This predicts
a nonzero negative mean of the primitive although r_q itself has mean
zero. Hence replacing the cumulative primitive Gram by averaged
Ramanujan orthogonality loses a term even before the common cutoff
limit. Search1119 checks prior period/totient identities. No new energy
bound or asymptotic mixed-term estimate is asserted.

- Scratch1118 first check found an explicit natural division rewrite
  was needed to reduce q/q to one, plus a redundant final tactic.
  Corrected recheck running.

- Search1119 (`Ramanujan totient period summatory`, deep): all20
  candidate/all20 source statements and both ingredient steps reviewed.
  The Ramanujan divisor formula and totient divisor convolution are
  applicable; complete-residue norm squares concern r_q, not its
  cumulative primitive. Gcd interval masses, reciprocal-phase bounds
  and totient inequalities do not yield the proposed primitive mean or
  an anchored energy estimate. No exact primitive-period mean returned.
  Partial=false;63992files;index1177673,coverage1177682/current1177683;
  semantic coverage unmeasured and background refresh incomplete.

- Corrected log-mass scratch1118 passed with empty diagnostics. Promoted
  and wired `PMPowerDampedMobiusRamanujanLogMass` (59 lines /5
  declarations); targeted old build47s, final actual leaf empty, exact
  bodies/exhaustive names/API/import/no-proof-debt passed. All5 axiom
  reports running. Global lint has eleven unrelated unwired leaves,
  no owned/proof-debt issue; no global pass claimed.
- Draft1121 makes the primitive-period calculation explicit using
  weighted divisor reindexing, the exact sum of integers, Mobius
  cancellation and the corpus's totient inversion. It targets the
  actual r_q carrier and is not yet checked.

- Actual Ramanujan logarithmic square mass fully audited:
  `PMPowerDampedMobiusRamanujanLogMass` (59 lines /5 declarations),
  targeted old build47s, final actual leaf empty, all5 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Pointwise |a(q)|<=q^(-1-epsilon); the proposed
  logarithmic square mass is dominated by
  (2^epsilon/epsilon)*q^(-1-epsilon), hence summable for every positive
  damping. Combined: thirty-eight leaves /9060 lines /665 audited
  declarations. Global lint has eleven unrelated unwired leaves, no
  owned/proof-debt finding; no global pass claimed. The energy
  comparison remains unproved. The actual primitive-period mean is
  the next check; no small-positive energy bound or RH proof.

## Proposed long-range primitive Gram law

If the primitive-period identity passes, test the sharper fixed-q law
for q>1 and primes p tending to infinity:

    K(p,q)/log(p) -> phi(q)/2,
    K(p,q) = sum_(N>=1) R_p(N)*R_q(N)/(N*(N+1)).

This is a new paper candidate, not a verified theorem. For N<p the
prime primitive is exactly -N. Thus the head of K is
-sum_(N<p)R_q(N)/(N+1), whose logarithmic mean should be minus the
period mean. Periodicity bounds |R_q| by a fixed C_q; |R_p|<=p
bounds the entire N>=p tail by C_q using the exact reciprocal telescope.
This would identify a logarithmic mixed term that survives despite
Ramanujan coefficient orthogonality. Multiplication by the actual
weights gives opposite signs according to mu(q), since a(p)<0. It
does not give a uniform estimate while q also grows or while all
denominators are summed. Search1123 checks the needed harmonic mean
and periodic-prefix infrastructure before further Lean work.

- Search1123 (`periodic cumulative Ramanujan harmonic logarithmic mean`,
  deep): all20 candidate/all20 source statements and both ingredient
  steps reviewed. The corpus has a generic zero-period-sum to periodic
  prefix theorem, and PM33 already supplies the exact Cesaro-to-harmonic
  mean transfer. Harmonic sum identities alone do not establish the
  primitive's mean. No fixed-q prime Gram asymptotic returned.
  Partial=false;63996files;index1177820,coverage1177834/current1177837;
  semantic coverage unmeasured and background refresh incomplete.
- Scratch1121 first check accepted the weighted sums and exact first
  moment; its final primitive-mean theorem needed `simp only` to unfold
  the definition under the sum binder. Corrected that and added actual
  coefficient/primitive periodicity. The extended recheck is running.

- Corrected primitive scratch1121 passed with empty diagnostics,
  including the exact period mean and actual periodicity. Added the
  explicit finite-period norm bound for all integer arguments; that
  extension is now checking.
- Search1124 (`periodic Cesaro mean finite period sum limit`, deep):
  all20 candidate/all20 source statements and both ingredient steps
  reviewed. `DeletionChronologicalLimit.periodic_zero_sum_prefix_bound`
  is directly reusable after subtracting the exact primitive mean; its
  bounded centered prefix divided by N tends to zero. Ordinary Cesaro
  convergence cannot be applied directly to a nonconstant periodic
  sequence; the generated step retains that missing convergence
  premise. Other periodic/averaged carriers do not prove the PM Gram
  law. Partial=false;63996files;index1177868,coverage1177871/current1177872;
  semantic coverage unmeasured and background refresh incomplete.

- Primitive bound extension passed with empty diagnostics. Added the
  actual Cesaro and logarithmic harmonic limits using the existing
  periodic zero-sum bound and PM33 transfer. The first check accepted
  the analytic reduction; two final algebra/cast goals remained. Added
  ring normalization and an explicit real-part identity for the limit.
  Corrected full scratch1121 check now running.

- Extended primitive scratch1121 passed. Removed a tactic Lean marked
  unreachable, then promoted/wired `PMPowerDampedMobiusRamanujanPrimitive`.
  Targeted build/audits now running. The actual periodic primitive has
  bounded norm, exact period mean -phi(q)/2, and the same Cesaro and
  logarithmic harmonic limits for q>1. The fixed-q prime Gram law and
  common cutoff-energy budget still require proof.

- Primitive leaf targeted old build37s and structural audits passed;
  final actual-leaf check is running. Draft1125 targets the literal
  prime primitive -N mod p, its uniform p bound, the shifted logarithmic
  mean, and absolute summability of each fixed primitive Gram pair.
  The reciprocal telescope is already proved in the corpus as
  `GaloisForLFunctions.hasSum_one_div_shift_mul_succ`. Draft1125 has
  not been checked; neither the Gram law nor the energy producer is
  claimed.

- Primitive leaf final actual check passed with empty diagnostics.
  All18 axiom reports now running. Global lint has twelve unrelated
  unwired leaves, no owned/proof-debt finding; no global pass claimed.
  The next Gram proof will use the exact decomposition into the
  N<p harmonic head and the bounded N>=p tail; its coefficient-side
  summability is not being substituted for that decomposition.

- Actual Ramanujan primitive fully audited:
  `PMPowerDampedMobiusRamanujanPrimitive` (206 lines /18 declarations),
  targeted old build37s, final actual leaf empty, all18 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. The primitive is periodic and bounded for q>1. Its
  exact period mean is -phi(q)/2, also its Cesaro and logarithmic
  harmonic limits. Combined: thirty-nine leaves /9266 lines /683
  audited declarations. Global lint has twelve unrelated unwired
  leaves, no owned/proof-debt finding; no global pass claimed. The
  fixed-q prime Gram asymptotic is checking next. No common cutoff
  energy comparison, small-positive admission or RH proof.

- Search1127 (`Ramanujan primitive Gram logarithmic denominator signed
  energy`, deep): all20 candidate/all20 source statements, the returned
  proof method and both proposed ingredient steps reviewed. Existing PM
  pointwise expansion/cofactor identities apply. The other primitive
  energies, positive Gram carriers and two-level Mobius conservation
  have different carriers; the proposed E4 differential-identity chain
  supplies no PM comparison. No common signed denominator-energy
  bound returned. Partial=false;64005files;index1178218,
  coverage1178224/current1178226; semantic coverage unmeasured and
  background refresh incomplete.

## Exact finite denominator Gram reduction

Next paper target: remove the physical cutoff T at each fixed Q,
without exchanging two infinite sums. All q=2,...,Q+1 primitives are
real and bounded. Expanding the finite square and summing the absolutely
convergent fixed-pair Gram series gives

    lim_(T->infinity) E_epsilon(Q,T)
      = sum_(i,j<Q) a_epsilon(i+2)*a_epsilon(j+2)*K(i+2,j+2).

Every summand of the physical energy is nonnegative. Therefore a common
upper bound on these actual finite signed quadratic forms is equivalent
to the existing common Q,T budget. The proposed logarithmic coefficient
square-mass comparison is now a concrete finite matrix inequality for
the actual Euler/Mobius vector; it is still unproved. No arbitrary-vector
operator bound, orthogonality cancellation, or infinite interchange is
being assumed. Formalise this exact reduction after the fixed-q Gram
law passes, then attack its signed quadratic form.

- Corrected full Gram scratch1125 passed with empty diagnostics.
  Promoted/wired `PMPowerDampedMobiusRamanujanGram`; targeted build
  and audits pending. Exact prime primitive, reciprocal-tail bound
  and shifted harmonic mean give K(p,q)/log(p)->phi(q)/2 for fixed
  q>1 along primes. No bound uniform in growing q is inferred.

- Gram leaf targeted old build9.9s and structural audits passed; final
  actual-leaf check passed with empty diagnostics. All13 axiom reports
  now running. Lint1129 reports fourteen unrelated unwired modules
  and shared API/overview staleness after concurrent edits; no owned
  module or proof-debt finding. No global lint pass claimed.
- Draft1128 expresses the fixed-Q energy as a finite signed Gram
  quadratic form, proves its T-limit and exact common-budget
  equivalence, and connects that budget to the existing admission
  receiver. The draft has not been checked; the quadratic bound itself
  remains an explicit open obligation.

- Search1130 (`Mobius totient Ramanujan cumulative primitive signed
  quadratic bound`, deep): all20 candidate/all20 source statements,
  all returned proof methods and both proposed steps reviewed. Exact
  totient convolutions and the owned primitive identities apply. The
  inclusive gcd Gram has a positive totient-square factorization and
  an explicit late-prime lower bound on a different Abel channel;
  read its complete170-line source before rejecting transfer. Reciprocal
  totient estimates, finite-field character bounds, Gaussian moments,
  and clock-energy estimates retain their different carriers or scale
  hypotheses. No PM signed quadratic upper bound returned.
  Partial=false;64009files;index1178312,coverage1178321/current1178322;
  semantic coverage unmeasured and background refresh incomplete.

- Actual primitive Gram fully audited:
  `PMPowerDampedMobiusRamanujanGram` (188 lines /13 declarations),
  targeted old build9.9s, final actual leaf empty, all13 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Every fixed pair is absolutely summable; for fixed
  q>1, K(p,q)/log(p)->phi(q)/2 along primes. The exact harmonic head
  has a tail error bounded by the finite-period primitive norm bound.
  Combined: forty leaves /9454 lines /696 audited declarations.
  Lint1129 has fourteen unrelated unwired modules and two shared
  generated-file staleness findings after concurrent changes; no owned
  or proof-debt finding and no global pass claimed. Finite signed Gram
  reduction draft1128 is next; common quadratic bound, small-positive
  admission and RH remain unproved.

## Next kernel invariant: von Mangoldt first moment

Test the exact arithmetic identity, for q>1,

    sum_(N>=1) R_q(N)/(N*(N+1)) = -Lambda(q).

Paper mechanism: finite summation by parts changes the left side to
`sum_(n<=T) r_q(n)/n - R_q(T)/(T+1)`. The bounded primitive makes
the boundary vanish. The divisor formula makes the harmonic term
`sum_(d|q) mu(q/d)*H_floor(T/d)`. Subtract H_T times the zero Mobius
sum, take the finite divisor limit `H_floor(T/d)-H_T -> -log(d)`,
and use the exact von Mangoldt convolution. Absolute convergence of
the primitive side is immediate from boundedness and the reciprocal
telescope. Search1131 checks the required harmonic/Dirichlet tools.

If established, set H_q=R_q+phi(q)/2. Completing the finite Gram form
then gives an exact correction

    K(p,q) = <H_p,H_q> + phi(p)*Lambda(q)/2
               + phi(q)*Lambda(p)/2 - phi(p)*phi(q)/4,

where the inner product uses weights 1/(N*(N+1)), N>=1. This retains
the nonzero primitive means and identifies an arithmetic rank-one
subtraction. For the actual squarefree-supported coefficients, only
prime denominators contribute to the Lambda first moment. The identity
and completion are paper targets, not yet Lean-proved here. Neither
positivity of the residual nor any uniform quadratic upper bound is
assumed.

- Full finite quadratic scratch1128 passed first check with empty
  diagnostics. Promoted/wired `PMPowerDampedMobiusRamanujanQuadratic`;
  targeted build/audits pending. Exact pointwise square expansion,
  absolute fixed-Q energy summability, T-limit, and common-budget
  equivalence are proved. Actual signed quadratic upper bound remains
  wholly unproved.

- Search1131 (`Ramanujan harmonic sum von Mangoldt primitive reciprocal
  logarithm`, deep): all20 candidate/all20 source statements, all
  returned proof methods and both ingredient steps reviewed. Harmonic
  reindexing and far-right von Mangoldt series are available; no direct
  primitive first moment returned. The suggested primitive-root chain
  does not bridge the actual series. Focused source search located
  `HTGeometry.tendsto_harmonic_natDiv_sub_log` and the real multiple
  harmonic identity in `RegularizedDivisorHarmonicLimit`, plus mathlib's
  exact log*Mobius=vonMangoldt convolution. Those prove the paper
  mechanism without an infinite denominator interchange.
  Partial=false;64012files;index1178401,coverage1178411/current1178412;
  semantic coverage unmeasured and background refresh incomplete.

- Quadratic leaf targeted old build238s and structural audits passed;
  final actual-leaf check passed with empty diagnostics. All12 axiom
  reports now running. Lint1132 reports ten unrelated unwired modules
  and three shared generated-file staleness findings; no owned-module
  or proof-debt finding. No global lint pass claimed.
- Draft1133 includes the full reciprocal first-moment proof, exact
  total reciprocal weight1, and the resulting totient/vonMangoldt
  correction to the mean-centered primitive Gram. Not checked yet.

## Energy centering versus period centering

The proposed first moment exposes a sharper positive survivor: the
actual energy probability weights are lambda_N=1/(N*(N+1)), N>=1,
whose total mass is1. Their mean of R_q is -Lambda(q), not the period
mean -phi(q)/2. Thus U_q=R_q+Lambda(q) has zero energy mean and

    K(p,q) = Lambda(p)*Lambda(q) + sum_N lambda_N*U_p(N)*U_q(N).

This is an exact orthogonal constant projection if the first moment
is verified. For the actual finite Euler vector, the scalar mean is
`-sum a(q)*Lambda(q)` and total energy equals its square plus the
nonnegative centered variance. This canonical variance, not merely
Bohr-period orthogonality, is the remaining signed quadratic object
to bound. Add the energy-centered pair identity to draft1133 after
its first-moment mechanism; no upper bound follows from positivity.

- Actual finite signed Ramanujan quadratic fully audited:
  `PMPowerDampedMobiusRamanujanQuadratic` (107 lines /12 declarations),
  targeted old build238s, final actual leaf empty, all12 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Each fixed natural denominator cutoff has finite
  total energy equal to its exact signed primitive Gram quadratic.
  The common Q,T energy budget is equivalent to a common Q bound
  on those literal quadratic forms. Combined: forty-one leaves
  /9561 lines /708 audited declarations. Lint1132 has ten unrelated
  unwired modules and three shared generated-file staleness findings;
  no owned/proof-debt finding and no global pass claimed.
  First-moment/centering draft1133 is checking. Uniform quadratic
  upper bound, small-positive admission and RH remain unproved.

## Finite actual variance reduction after the moment theorem

Pending verification of draft1133, define

    M_epsilon(Q) = -sum_(i<Q) a_epsilon(i+2)*Lambda(i+2),
    V_epsilon(Q) = sum_(N>=1) lambda_N*(D_epsilon,Q(N)-M_epsilon(Q))^2.

Finite linearity of the proved primitive first moments would give
mean M. Expanding the square with mass1 then gives the exact identity
`G_epsilon(Q)=M_epsilon(Q)^2+V_epsilon(Q)`, V>=0. Absolute summability
of `Lambda(q)*q^(-1-epsilon)` and the proved |a(q)| bound give a common
finite upper bound on |M(Q)| for each epsilon>0. Therefore the common
Gram bound is equivalent to a common bound on the actual centered
variance V(Q). This removes a provably bounded scalar channel; it
does not establish the variance estimate. Search1134 checks prior
source-faithful centered-variance and coefficient moment work before
new Lean code.

- Moment scratch1133 first check found an over-broad complex inverse
  simplification, a heartbeat timeout while inferring the shifted
  reciprocal series, and a rewrite requiring the Gram definition
  folded explicitly. Replaced the broad simp with an exact real-part
  simp set, supplied the series function explicitly, and folded the
  Gram target. Corrected full recheck running; heartbeat limits
  unchanged. No first-moment theorem claimed before success.

- Search1134 (`Mobius vonMangoldt Ramanujan weight energy centered
  variance`, deep): all20 candidate/all20 source statements, both
  returned proof methods and both proposed ingredient steps reviewed.
  Actual PM divisor identities apply; finite weighted variance algebra
  is available, but Euler-clock moments, Bohr-period variance, Selberg
  source variance, and other Abel/Mellin carriers do not bound this
  canonical PM variance. The generated clock-moment chain does not
  identify its probability weights with reciprocal energy weights.
  No uniform actual variance producer returned.
  Partial=false;64016files;index1178532,coverage/current1178545;
  semantic coverage unmeasured and background refresh incomplete.

- Corrected full moment scratch1133 passed with empty diagnostics.
  Promoted/wired `PMPowerDampedMobiusRamanujanMoment`; targeted build
  and audits pending. Exact harmonic limit, absolutely summable
  reciprocal first moment -Lambda(q), total reciprocal mass1, and both
  period-centered and energy-centered Gram identities are proved.
  The energy-centered primitive R_q+Lambda(q) has weighted mean0.
  Common actual variance upper bound remains unproved.

- Moment leaf targeted old build43s and structural audits passed;
  final actual-leaf check passed with empty diagnostics. All17 axiom
  reports now running. Lint1135 reports eleven unrelated unwired
  modules and two shared generated-file staleness findings; no owned
  module/proof-debt finding and no global pass claimed.
- Draft1136 targets the actual finite-cutoff weighted mean, absolute
  vonMangoldt coefficient summability, common scalar-mean bound,
  Pythagorean energy/variance identity, and exact equivalence of
  common Gram and common centered-variance budgets. Draft unchecked;
  variance bound remains open.

## Long-range correlation survives energy centering

The proved fixed-q prime Gram law and the new exact constant projection
force the paper consequence

    K_energy_centered(p,q)/log(p) -> phi(q)/2-Lambda(q)

for fixed q>1 and primes p->infinity, using Lambda(p)=log(p). Thus
removing the scalar energy mean does not generally remove logarithmic
mixed correlations. Add this exact consequence to the variance draft
and check it in Lean; do not replace the remaining covariance by a
diagonal or invoke ordinary period orthogonality.

- Actual primitive reciprocal first moment fully audited:
  `PMPowerDampedMobiusRamanujanMoment` (200 lines /17 declarations),
  targeted old build43s, final actual leaf empty, all17 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. The primitive first moment under reciprocal energy
  weights is exactly -Lambda(q), and their mass is1. Period centering
  yields the explicit totient/Lambda correction; energy centering
  R_q+Lambda(q) has weighted mean0 and splits K into Lambda(p)*Lambda(q)
  plus its centered Gram. Combined: forty-two leaves /9761 lines /725
  audited declarations. Lint1135 has eleven unrelated unwired modules
  and two shared generated-file staleness findings; no owned/proof-debt
  finding and no global pass claimed. Actual finite variance reduction
  and centered mixed-Gram law draft1136 are checking. No uniform actual
  variance bound, small-positive admission or RH proof.

- Search1137 (`Ramanujan coefficient vonMangoldt reciprocal zeta
  derivative sum`, deep): all20 candidate/all20 source statements,
  all returned proof methods and both ingredient steps reviewed.
  Far-right Lambda Dirichlet series/log-derivative identities are
  available, but no literal A_epsilon-weighted Lambda sum identity
  returned. Prime-lattice frequency support, Selberg coefficient
  bounds and Ramanujan residue norm identities do not establish it.
  Paper candidate for a later scalar refinement: regrouping the
  absolutely convergent divisor pairs gives
  `sum_q A(q)*Lambda(q)=sum_n mu(n)*log(n)/n^(1+epsilon)`, hence the
  negative sum is the derivative of reciprocal zeta. The draft's
  uniform scalar bound needs only absolute summability, so this
  refinement is deferred while testing the actual variance estimate.
  Partial=false;64017files;index1178599,coverage1178611/current1178612;
  semantic coverage unmeasured and background refresh incomplete.

- Variance scratch1136 first check exposed a `convert` instance-diamond
  mismatch in the mean proof and a heartbeat timeout inferring the
  shifted summable function. Replaced `convert` by an exact HasSum
  congruence and specified the shifted function explicitly. Full
  recheck running; heartbeat limits unchanged. The remaining variance
  algebra and centered prime Gram consequence produced no first-check
  error, but no full-pass claim is made yet.

## Control regime for the literal natural denominator cutoff

Before attempting small-positive damping, prove the actual common
cutoff budget for epsilon>1/2 directly from the audited finite
cofactor representation. Choose a real exponent
`max(0,1-epsilon)<a<1/2`. For x>=0,
`0<=fract(x)<=min(x,1)<=x^a`. Hence

    |D_epsilon,Q(N)| <= N^a * sum_(d>=1) d^(-epsilon-a),

using |Z_epsilon(Q+1,d)|<=d^(-epsilon). The divisor sum is finite
because epsilon+a>1. Squaring and summing the reciprocal energy
weights is finite because 2a<1. This supplies a common Q,T bound
for the literal natural denominator family, not a transfer from a
prime-aperture carrier. The choice of a fails when epsilon<=1/2;
no improvement below that boundary follows from this absolute
argument. Search1138 checks prior generic fractional-power bounds
and half-damping norm estimates before new code.

- Corrected full variance scratch1136 passed with empty diagnostics.
  Promoted/wired `PMPowerDampedMobiusRamanujanVariance`; targeted
  build/audits pending. Exact finite weighted mean, common scalar bound,
  G=M^2+V, V>=0, and common Gram/variance budget equivalence are proved.
  The centered mixed prime Gram/log(p) tends to phi(q)/2-Lambda(q).
  No uniform variance upper bound for small-positive damping.
- Search1138 (`power damped fractional part sum uniform norm half
  damping`, deep): all20 candidate/all20 source statements, all returned
  methods and both proposed steps reviewed. Existing half-damping
  Fermi-prefix admission and prime-aperture term bounds concern other
  cutoffs; no literal natural-denominator uniform estimate returned.
  Unrelated oscillator damping and fractional-field matches do not
  apply. The direct finite-cofactor proof above remains the plan.
  Partial=false;64020files;index1178666,coverage/current1178673;
  semantic coverage unmeasured and background refresh incomplete.

- Variance leaf targeted old build43s and structural audits passed;
  final actual-leaf check passed with empty diagnostics. All12 axiom
  reports now running. Draft1140 formalises the common natural-cutoff
  power bound and energy/Gram/variance budgets for epsilon>1/2.
  Draft1140 unchecked; the strict absolute boundary is retained.

- Actual finite energy-centered variance fully audited:
  `PMPowerDampedMobiusRamanujanVariance` (129 lines /12 declarations),
  targeted old build43s, final actual leaf empty, all12 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Actual weighted mean M has a common finite bound at
  each positive damping; G=M^2+V with V>=0, and common Gram/variance
  budgets are equivalent. Centered prime Gram/log(p) tends to
  phi(q)/2-Lambda(q), so logarithmic cross terms survive centering.
  Combined: forty-three leaves /9890 lines /737 audited declarations.
  Lint1139 has twelve unrelated unwired modules and two shared
  generated-file staleness findings; no owned/proof-debt finding and
  no global pass claimed. Absolute natural-cutoff control for damping
  above1/2 is checking in draft1140. Uniform small-positive variance
  upper bound, admission and RH remain unproved.

## Candidate endpoint transfer from the actual Mobius prefixes

The existing half-damping Fermi-prefix bound uses Abel summation of
raw Mobius prefixes with a logarithmic norm saving. It does not
automatically apply to the new denominator cutoff. A possible exact
transfer keeps its triangular dm<=Q cutoff. Write s=1+epsilon,
J_m=product_(p|m)(p^s-1), and B_d=product_(p|d)(1-p^(-s))^(-1).
The finite cofactor Fermi source `-sum_d Z(Q,d)*FermiGen(d*t)` can be written

    -alpha * sum_(m<=Q) mu(m)^2/J_m
      * sum_(d<=Q/m, (d,m)=1) mu(d)*d^(-epsilon)*B_d*FermiGen(d*t).

For fixed squarefree m, its inner coefficient is a Dirichlet
convolution of the actual base mu(d)*d^(-epsilon) with h_m. Local
factors of h_m, in a formal prime variable X, would be

    p|m:      1/(1-p^(-epsilon)*X),
    p not|m: 1-(B_p-1)*sum_(k>=1) p^(-k*epsilon)*X^k.

Finite divisor reindexing then expresses the negative inner prefix as
`sum_(r<=Q/m) h_m(r)*P_epsilon,floor(Q/(m*r))(r*t)`. A common L2
base-prefix bound B would yield the norm bound

    alpha*B*sum_m mu(m)^2/J_m * sum_r |h_m(r)|/sqrt(r).

The proposed absolute Euler mass is finite for every epsilon>0:
with v=epsilon+1/2, p|m contributes (1-p^(-v))^(-1), while p not|m
contributes 1+(B_p-1)*p^(-v)/(1-p^(-v)). The combined m/r local
correction is O(p^(-1-epsilon))+O(p^(-3/2-2*epsilon)). All constants
may depend on epsilon. This is a paper candidate, not a formal bound.
It must include exact coefficient convolution, absolute mass proof,
finite cutoff reindexing, dilation norms, and the Fermi-to-centered
source/discrete-energy bridge. At epsilon=1/2 the required base
prefix bound is already proved; at smaller epsilon it is not supplied
by this transfer. Search1141 checks endpoint/cofactor prior work.

- Absolute-budget draft1140 first check accepted the fractional-power
  bound, finite summation/energy estimates and endpoint selection,
  except one scalar normalization where `rpow_neg` rewrote -epsilon
  instead of -a. Specified exponent a explicitly. Full recheck running.

- Search1141 (`Ramanujan cofactor cutoff half damping energy boundary`,
  deep): all20 candidate/all20 source statements, all returned proof
  methods and both proposed steps reviewed. Exact owned finite
  cofactor identities apply. Ramaré energy, spectral cutoff and
  quartic-cusp cutoffs have different carriers; the generated quartic
  derivative chain supplies no endpoint transfer.
  Partial=false;64022files;index1178814,coverage1178816/current1178823;
  semantic coverage unmeasured and background refresh incomplete.

- Endpoint transfer paper audit: restored the overall minus sign to
  match the actual Mobius Fermi prefix. Here Q denotes the maximum
  denominator; the existing Lean prefix parameter is Q-1. The combined
  m/r local absolute mass has a sharper simplification. Set
  u=p^(-1-epsilon), r=p^(-epsilon-1/2). Before multiplying alpha its
  local factor is `1+u*(1+r)/((1-u)*(1-r))`; after the density factor
  (1-u), it is exactly `1+2*u*r/(1-r)`. Thus the proposed transfer
  constant is

      product_p (1+2*p^(-3/2-2*epsilon)/(1-p^(-1/2-epsilon))).

  This has a summable p^(-3/2) majorant uniform over epsilon>0. No
  literal epsilon=0 density value is used. This stronger paper claim
  requires its own absolute Euler-product audit and exact finite
  coefficient transfer; neither is yet formalised.

- Corrected full absolute-budget scratch1140 passed with empty
  diagnostics. Promoted/wired `PMPowerDampedMobiusRamanujanAbsolute`;
  targeted build/audits pending. Literal natural-denominator Q,T
  energy, Gram and centered-variance budgets are proved for every
  epsilon>1/2. The proof keeps the exact finite cofactor formula and
  both convergent power sums; it makes no claim at epsilon=1/2.

- Strict absolute natural-denominator budget fully audited:
  `PMPowerDampedMobiusRamanujanAbsolute` (111 lines /7 declarations),
  targeted old build103s, final actual leaf empty, all7 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Common Q,T energy, Gram and centered-variance bounds
  hold for epsilon>1/2 by the exact cofactor fractional-part bound and
  two convergent power sums. No assertion at epsilon<=1/2.
  Combined: forty-four leaves /10001 lines /744 audited declarations.
  Lint1144 has ten unrelated unwired modules; no owned/proof-debt
  finding and no global pass claimed. Endpoint transfer via finite
  Dirichlet convolution remains a paper candidate. Small-positive
  admission and RH remain unproved.

- Search1142 (`Dirichlet convolution finite prefix dilation norm
  summable`, deep): all20 candidates/all20 source statements, every
  returned method and both proposed ingredient steps reviewed.
  FiniteDirichletConvolutionOverflow supplies the exact hyperbola
  cutoff, not norm preservation. Scalar Mellin dilation characters
  are not L2 dilation operators. Dirichlet convolution/Mobius inversion
  and BivariateConvolutionSummatorySwap can support the finite identity;
  no actual Ramanujan endpoint upper bound returned. The generated
  dirichletInverse assumption summary is not authoritative; use its
  source signature. Partial=false;64024files;index1178868,
  coverage/current1178874; semantic coverage unmeasured and background
  refresh incomplete.

- Next exact finite transfer kernel (without division by alpha):
  f_m(d)=d*mu(m)*A_epsilon(d*m),
  k_m(r)=sum_(a*b=r) a^(-epsilon)*f_m(b).
  The base mu(d)*d^(-epsilon) convolved with a^(-epsilon) is the
  Dirichlet unit, so f_m=base*k_m. The cofactor Fermi prefix is exactly
  sum_(m<=Q)sum_(r<=Q/m) k_m(r)*P_epsilon,floor(Q/(m*r))(r*t).
  This retains finite cutoffs and all signs. Formalise this identity
  before the local-factor and absolute-mass estimate. The explicit
  paper formula for squarefree m is
  k_m(r)=alpha*mu(m)^2/J_m * r^(-epsilon)
    *product_(p|r,p not|m)(-1/(p^(1+epsilon)-1)).
  Nonsquarefree m gives zero. No common norm bound follows until the
  weighted absolute double mass is proved finite.

- Exact finite transfer scratch1145 corrected cast elaboration,
  explicit hyperbola-reindexing function and implicit map-swap index.
  Full recheck1147 passed with empty diagnostics. Promoted/wired
  `PMPowerDampedMobiusRamanujanTransfer`; targeted build/audits pending.
  The theorem uses the actual cofactor Fermi prefix and actual Mobius
  prefixes, retaining the triangular cutoff Q/(m*r) and dilation r*t.
  It has no norm hypothesis and asserts no unproved norm bound.

- Search1146 (`multiplicative divisor sum coprime prime factors product
  Mobius`, deep): all20 candidates/all20 source statements, every
  returned method and both proposed ingredient steps reviewed.
  DampedMobius.divisorSum and its multiplicativity directly support
  the kernel product. Coprime residue channels and quadratic interval
  estimates have different carriers; no missing endpoint budget was
  supplied. Partial=false;64025files;index1178997,
  coverage/current1178998; semantic coverage unmeasured and refresh
  incomplete. Read the exact DampedMobius convolution and Euler-product
  summability proof; scalar finite product control alone cannot be
  promoted to an infinite norm claim.

- Stronger paper kernel-mass identity: for each positive r, the exact
  multiple mass sum_m |A(d*m)|=mu(d)^2*d^(-1-epsilon) implies

      sum_m |k_m(r)| = r^(-epsilon)
        *product_(p|r)(2*p^(-1-epsilon)).

  Under probability mass |A(m)|, squarefree divisibility indicators
  have joint moments d^(-1-epsilon). For c_p=1/(p^(1+epsilon)-1),
  E[c_p+(1-c_p)*1_(p|m)]=2*p^(-1-epsilon); the joint moments factor.
  A finite product expansion proves the displayed identity, keeping
  every squarefree divisor. This converts the double weighted mass
  to one multiplicative series with local tail
  2*p^(-3/2-2*epsilon)/(1-p^(-1/2-epsilon)). Its absolute summability
  follows from finite Euler products bounded by exp of the convergent
  prime-tail sum. Paper proof dependency-closed given the existing
  exact multiple mass, but finite expectation/product and summability
  formalisation remain pending. Kernel product draft1149 is written;
  its check follows the exact-transfer leaf audits.

- Search1151 (`summable multiplicative function prime power local
  factors finite Euler product bound`, deep): all20 candidates/all20
  source statements, all returned methods and both proposed ingredient
  steps reviewed. DampedMobius.summable_divisorSum_div gives the
  appropriate finite-Euler/exponential-majorant proof pattern at weight
  1/n. Existing EulerProduct_hasProd already assumes global summability,
  so using it to obtain that hypothesis would be circular. The returned
  inner-product proposal has an unrelated summable carrier.
  Partial=false;64028files;index1179094,coverage/current1179102;
  semantic coverage unmeasured and background refresh incomplete.
  Plan: prove positive multiplicative summability from summable local
  tails via finite factored-number sums; apply to the kernel mass.

- Exact finite Ramanujan-to-Mobius prefix transfer fully audited:
  `PMPowerDampedMobiusRamanujanTransfer` (132 lines /14 declarations),
  targeted old build55s, final actual leaf empty, all14 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. Cofactor Fermi prefix equals the triangular sum of
  actual dilated Mobius prefixes with the explicit convolution kernel;
  no norm bound inferred before the kernel-mass audit.
  Combined: forty-five leaves /10133 lines /758 audited declarations.
  Lint1150 has ten unrelated unwired modules and three shared generated
  file staleness findings; no owned/proof-debt finding, no global pass.
  Kernel prime-factor formula is checking in draft1149. Endpoint and
  small-positive natural-cutoff budgets remain open; RH unproved.

- More economical exact-mass proof: put w(n)=|A(n)|,
  H_S(n)=product_(p in S)(if p|n then 1 else c_p), c_p=1/J_p.
  For a prime p outside S, H_S(p*n)=H_S(n). If X=sum_n w(n)H_S(n)
  and T=sum_(p|n)w(n)H_S(n), the exact weight recurrence gives
  T=c_p*(X-T), since w(p*n)=0 when p|n and c_p*w(n) otherwise.
  Therefore X for S union {p} is T+c_p*(X-T)=2*T=2*p^(-1-epsilon)*X.
  Starting from sum w=1 proves the finite-product expectation directly.
  All H_S lie in [0,1], giving summability before each subtraction and
  reindexing. This avoids a powerset expansion while proving the same
  exact column-summed kernel mass.

- Kernel draft1149 signed formula passed first check, with one unused
  simp argument removed. Added the exact norm product and [0,1] bounds
  on the finite prime product. Full recheck1152 passed with empty
  diagnostics. Promoted/wired `PMPowerDampedMobiusRamanujanKernel`;
  targeted build/audits pending. The formula holds for every positive
  damping and handles zero/repeated-prime columns without a squarefree
  premise on m. Exact summed kernel mass draft1153 awaits this audit.

- Kernel leaf targeted old build62s, structural audit (196 lines /14
  declarations) and final actual-leaf empty check passed. Axiom audit
  running. Exact mass draft1153 and generic Euler-majorant draft1154
  are written but unchecked. For uniform positive-damping mass, use
  the damping-independent arithmetic majorant

      g0(r)=r^(-1/2)*product_(p|r)(2/p), r>0; g0(0)=0.

  Its local Euler tail is 2*p^(-3/2)/(1-p^(-1/2)), dominated by
  [2/(1-2^(-1/2))]*p^(-3/2). Finite Euler sums yield summability.
  This g0 is an arithmetic majorant, not the undefined zero-damping
  density probability. No substitution alpha(0) is made.

- Exact transfer kernel prime-factor/norm formula fully audited:
  `PMPowerDampedMobiusRamanujanKernel` (196 lines /14 declarations),
  targeted old build62s, final actual leaf empty, all14 standard-axiom
  reports and exact-body/exhaustive names/API/import/no-proof-debt
  checks passed. The norm kernel equals |A(m)|*r^(-epsilon) times
  product_(p|r)(if p|m then 1 else 1/(p^(1+epsilon)-1)); the finite
  product lies in [0,1]. No squarefree premise on m is needed.
  Combined: forty-six leaves /10329 lines /772 audited declarations.
  Lint1156 has ten unrelated unwired modules and three shared generated
  file staleness findings; no owned/proof-debt finding, no global pass.
  Combined mass/Euler/budget draft1157 is checking. Uniform transfer
  norm and endpoint natural-cutoff energy remain unproved; RH unproved.

## Resumed audit — 2026-10-01

- Goal remains unconditional RH or its falsification via PM. No subagents,
  numerical experiments, added axioms, full builds, or commits.
- Plan: (1) repair and audit the saved exact kernel-mass draft;
  (2) transfer the existing half-damping Mobius-prefix norm bound to the
  natural-denominator cutoff; (3) investigate the surviving small-positive
  damping estimate through fresh corpus searches and exact conjectures.
- Draft1157's old process has exited. Its diagnostics show local proof
  failures in conditional-sum bounds, an over-broad rewrite of the T
  recurrence, geometric-series elaboration, and an exponential comparison.
  No completed kernel-mass theorem is claimed. Fix these before promotion.
- Current source search returned the actual PM denominator/energy leaves;
  no producer theorem. Compiler metadata was largely source-only, so all
  new dependencies and final statements require local Lean checks.

- Resumed search01 (`Ramanujan transfer kernel mass summable`, PM-filtered):
  all 20 candidate and 20 source entries reviewed. Exact transfer, kernel,
  absolute weight mass, and finite cofactor identities match the proposed
  proof. Conditional Gram/admission handoffs contain the still-open budget;
  none produces it. Search03 (`L2 dilation lpNorm positive half line`):
  all 20 candidate and 20 source entries reviewed. Existing positive-half-line
  dilation and dyadic coercivity are usable; whole-line Sonin dilation and
  abstract operator bounds do not directly replace them. Both searches
  partial=false, no errors; coverage snapshot older and semantic coverage
  unmeasured. Source statements checked directly for required PM lemmas.
- Endpoint paper proof: use the exact finite triangular transfer and
  Minkowski twice. Each term has norm at most
  B*|k(m,r)|/sqrt(r), with B supplied by the already-proved half-damping
  Mobius-prefix bound. The uniform kernel mass gives a common Fermi-prefix
  norm. This proof includes every m,r in its actual cutoff and is independent
  of Q. Draft endpoint04 encodes it; still unchecked. A separate bridge from
  this physical norm to the anchored discrete energy remains to formalize.
- Small-positive damping remains separate: the existing Abel proof supplies
  B at one half, not cofinally near zero. The mass bound does not improve
  that exponent and cannot be used as a replacement for the base-prefix
  bound. Continue with a source cancellation conjecture after endpoint audit.

- Repaired draft check reduced failures to two syntax/normalization details:
  parenthesize the whole summand in the T recurrence, and normalize addition
  order in the exponential comparison. No mathematical gap was reported in
  the other declarations. Corrected draft promoted and umbrella-wired as
  `PMPowerDampedMobiusRamanujanKernelMass`; compilation and audit remain
  pending. No finished result is claimed until both pass.

- User steering: only work that attacks the hard PM admission gap counts as
  route progress. The half-damping transfer draft was therefore withdrawn
  and deleted before compilation. It closes a cutoff endpoint but does not
  lower the admitted damping threshold. Finish the already-added kernel
  module audit, then attack the actual small-damping signed covariance.
  Do not claim the kernel bound advances the RH-critical exponent.

- Kernel-mass module fully audited: `PMPowerDampedMobiusRamanujanKernelMass`
  (349 lines /21 declarations). Targeted `lake --old build` succeeded
  (leaf174s; unrelated dependency diagnostics replayed). Final actual
  `lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusRamanujanKernelMass.lean`
  exited0 with empty diagnostics. All21 axiom reports use only propext,
  Classical.choice, Quot.sound. Exact-body, exhaustive-name/API, unique
  umbrella import and proof-debt checks passed. Index regenerated. Lint
  fails on ten unrelated unreachable modules; no owned/proof-debt finding.
  Exact weighted kernel mass is uniformly bounded for every positive
  damping, but no small-damping prefix bound or admission follows.
  This is auxiliary closure, not a reduction of the hard RH gap.

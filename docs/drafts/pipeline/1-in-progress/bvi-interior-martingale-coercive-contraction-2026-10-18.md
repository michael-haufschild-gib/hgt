# Coercive contraction for the actual BVI interior martingale

- **ID:** BVI-INTERIOR-CONTRACTION-2026-10-18
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / source audit
- **Statement:** For every positive damping parameter, prove a strict contraction of the compensated interior martingale against the actual pronic energy, with a horizon-independent remainder.

## Goal

Build problem 4 of `docs/reports/walls/bezout-wall1-programme.md` as an independent BVI arithmetic theorem. Required conclusion: some delta > 0 and C(epsilon), independent of T, satisfy

    2 M_int(epsilon,T) + 2 c_int(epsilon) H_comp(T)
      <= (1-delta) E(epsilon,T) + C(epsilon).

No assumed analytic budget, numerical experiment, extra axiom, RH work, or use of hgtl7. The field README is read-only. A finite-period identity, conditional criterion, or result restricted to strong damping does not complete this goal.

## Plan and gates

- [x] Read attachment, full field README, project guidance, relevant memories, and current live corpus.
- [x] Locate actual definitions and audit the stated mechanism against source.
- [ ] Form conjectures from source evidence; prove or refute each on paper and retain the strongest positive survivor.
- [ ] Formalize dependency-closed results without open analytic premises.
- [x] Audit the first completed leaf with `lake --old env lean`, audit all public axiom closures, wire umbrella, regenerate index, run formal lint, clean owned scratch. Repeat for later proved leaves.
- [ ] Prove the full uniform strict contraction, then audit every requirement before completion.

## Current checkpoint

The first positive survivor is formalized and wired:
`InteriorJumpOrbitCenteringAndCompensatedBounds.lean`. Its original-source
check exited 0 with no diagnostics (44502); all fourteen public declarations
passed the axiom audit (87987) with only standard Lean axioms. Exact source
hash and evidence are on
`../3-formalized/bvi-interior-jump-orbit-centering-and-compensated-bounds-2026-10-18.md`.
The zero-conditional-mean sub-route is closed, including its positive
survivor, on `../5-failed/bvi-zero-conditional-interior-mean-2026-10-18.md`.

The second positive survivor is also formalized and wired:
`BirthDelayedInteriorJumpCenteringAndUniformPairBounds.lean`. Retaining
the initial anchor and delaying centering to the actual birth threshold
improves the pair bound to `1/d + 2/gcd(d,e)`. The original-source check
passed (67436); all eleven public declarations and eleven existing corpus
APIs passed the axiom audit (45245), using only standard Lean axioms.
Paper proof, exact scope and source hash are on
`../3-formalized/bvi-birth-delayed-interior-centering-2026-10-18.md`;
raw audit evidence is under `logs/bvi-birth-delayed-2026-10-18-*`.

Final index refresh passed. Final lint still reports seven unrelated CHMD
reachability errors, root-module placement, and two generated files made
stale by concurrent changes; no finding names the owned leaf. The exact
ten errors and all certificates are in the manifest. Forty-eight owned
proof/search temporary files were archived and removed. Source and axiom
processes are terminal; subsequent corpus searches are tracked separately.

The programme's problem 4 uses the actual source weight and increment.
README remains unchanged by this task. Full contraction remains open:
the unsigned modulus sum is not uniformly bounded at small damping.

After the user's corpus-search correction, the next route uses existing
signed all-depth Hilbert/Gram identities, the exact integer-jump and
additive-lag bridge, and existing truncated-Gram error bounds. The dyadic
cutoff-error candidate below must be checked against this machinery before
writing another leaf. The signed finite-lag coercivity and its base-modulus
uniformity remain the actual gaps. A better single-pair constant or another
scalar Euler factorization does not close them.

`update_plan` and `multi_tool_use.parallel` are unavailable. This card tracks the plan; independent reads use `Promise.allSettled`. Serena returned no Lean symbols in the active Python project, so Lean source inspection uses corpus search and `rg`.

## Source calibration

The actual `pmBezoutInteriorMartingaleSum` is

    sum_{n=1}^{T-1} a_epsilon(n+1) I_epsilon(n)
      (1/(n+1)-1/(T+1)),

where a is `pmPowerDampedCenteredDivisorCoeff`. It is not the sum with harmonic differences H_T-H_n in the programme prose. Also

    a_epsilon(n+1) = Delta I_epsilon(n) + Delta^2 S_epsilon(n),

where S is `pmActiveSawtoothComponent`. Dropping the second-difference term changes the target. The finite-cutoff interior sawtooth differs from the horizon-free prefix by an explicit affine term; it cannot be silently substituted either.

Verified source locations: `BezoutPronicTotientInteriorMartingaleSynthesis.lean` (definition and affine bridge), `InteriorMartingaleQuadraticGradientAndRenormalizedDriftBudget.lean` (increment law), `CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget.lean` (canonical budget), `PronicPotentialSelfCancellationAndInteriorGradientConservation.lean` (coefficient-one cancellation).

## First conjecture: correct conditional centering before estimating

For a jump modulus d and interior modulus e, test the conditional mean of the actual centered sawtooth, with both endpoint residues deleted, along n = -1 mod d. Coprimality of the endpoint integers does not imply coprimality of these two moduli. Determine the gcd-resonant main term and finite-prefix remainder before claiming orthogonality or summability. A failure of zero conditional mean must retain an exact projection or corrected cancellation theorem as its positive survivor.

## Evidence

## Conditional-centering calculation (paper)

Let psi_e(n) = (n mod e)/e - (e-1)/(2e), and
J_e(n) = -psi_e(n) when e divides neither n nor n+1, and zero otherwise.
For positive d,e, put g=gcd(d,e), m=e/g. The progression n=d-1+dk
runs once through residues g-1+gj (0<=j<m) in m steps. Its mean psi is
(g-1)/(2e). The successor endpoint e-1 is deleted once. The predecessor
endpoint 0 occurs and is deleted precisely when g=1. Therefore

    gamma(d,e) = mean_k J_e(d-1+dk)
      = 0                              if g=1,
      = (e-g)/(2 e^2)                  if g>1.

This is zero exactly when gcd(d,e)=1 or e divides d. Otherwise it is
strictly positive. For the squarefree pair d=3,e=6 it equals 1/24; zero
conditional mean fails even on squarefree moduli. This is not a numerical
experiment: it follows by evaluating the displayed rational formula.

After subtracting gamma, the sequence has period m and zero period sum.
Since |J_e|<=1/2 and 0<=gamma<=1/2, every incomplete period has absolute
sum <=m. Abel summation along the progression then gives, for every L,

    |sum_{k<L} (J_e(d-1+dk)-gamma(d,e))/(d(k+1))| <= m/d.

The same estimate applies to the nonnegative compensated weight
max(1/(d(k+1))-1/(T+1),0). This supplies a genuine bound uniform in the
observation horizon for each pair, not only a cycle identity. Its dependence
e/(d*gcd(d,e)) is not yet summable across the actual growing modulus range;
it does not establish the requested contraction. This exact result is now
formalized and audited in the module listed in the current checkpoint.

The generic fractional-atom gcd orbit mean already exists as
`RHTower.cycleAverage_fracAtom` in `CausalMobiusThetaUniformCycle.lean`.
That input is infrastructure, not a novelty claim. The target here is the
two-endpoint-deleted interior atom, its exact resonant correction, and its
finite compensated progression bound connected to the BVI interior sum.

## Evidence (continued)

### Next conjecture: keep the signed modulus sum intact

The actual weights are `pmPowerDampedRealWeight epsilon e = mu(e) e^(-epsilon)`.
The resonant correction obeys gamma(d,e)<=1/(2e), so its weighted e-series
is absolutely summable for every positive epsilon. The incomplete-orbit
remainder is the difficult term, not the resonant mean itself.

A finite prime-set check gives a further candidate identity. For a finite
set P of primes, D=P intersect primeFactors(d), s=1+epsilon, and
F_s(U)=product_{p in U}(1-p^(-s)), sum over squarefree e supported on P:

    sum_e mu(e)e^(-epsilon) gamma(d,e)
      = (1-F_s(D))/2 * (F_(s+1)(P\D)-F_s(P\D)).

Derivation: split gamma into the difference of the gcd>1 parts of
mu(e)/e^s and mu(e)gcd(d,e)/e^(s+1). Each finite sum factors prime by prime;
the coprime portions cancel. The displayed expression is nonnegative,
and strictly positive when D and P\D are both nonempty. Hence multiplying
by the jump weight mu(d)d^(-epsilon) does not give a uniform negative sign:
the sign alternates with multiplicative depth. This supports preserving
signed cross-depth interactions in the remainder estimate. This calculation
still needs a direct source/Lean audit; a full prime box is not the actual
truncation e<=N and cannot substitute for the required theorem.

Corpus query `moebius gcd Euler product coprime` completed with partial=false;
candidate lemmas and source arguments inspected. It supplies multiplicative
and coprime identities, not an audited instance of this displayed formula.

- Initial hybrid query: `interior martingale contraction coercivity`, filtered to BVI; completed, partial=false, source/compiler freshness mostly pending. Candidate lemmas and source arguments inspected. It finds the exact identities and conditional bridges, not the requested inequality.
- Deep query: `fractional part arithmetic progression gcd sawtooth conditional mean remainder`, session 57183 completed with partial=true after a semantic-retrieval timeout. Returned candidates were inspected; the focused lexical `cycleAverage_fracAtom` query located the reusable exact gcd-orbit mean. Search records are archived under `logs/bvi-interior-orbit-2026-10-18-*`.
- Working tree contains unrelated ongoing work. Preserve it. Existing cofinal arithmetic card is paused and is not this task's write scope.
- `docs/architecture.md` and `docs/testing.md` absent.

## Log

### Second loop: preserve the affine anchor and delay centering until birth

Previous turn classified as **progress**: canonical source, exact positive
survivor and axiom evidence were added. Current hash revalidation matches
the certificate. No owned process was inherited live.

The raw single-pair harmonic estimate can be improved from m/d to
(H_m+1)/d by splitting at one reduced orbit. However, a proposed logarithmic
lower-bound family mostly occupies the interval before the interior modulus
is born. Its contribution is canceled by the affine anchor in the actual
horizon-free prefix. Do not use raw sawtooth coherence as an obstruction to
the actual source without keeping that anchor.

Set A_e=(e-1)/(2e), F_e(n)=J_e(n)-A_e and K=floor(e/d), with d>=2.
The existing affine bridge writes I_epsilon as a finite sum of c(e)F_e plus
the retained linear density correction. For k<K, n=d(k+1)-1 satisfies
1<=n<e and n+1<=e. Hence |F_e(n)|<=d(k+1)/e, including the endpoint
n+1=e. Its entire compensated contribution is bounded by K/e<=1/d.

For k>=K, subtract gamma(d,e)-A_e. The residual becomes J_e-gamma.
Its prefixes starting at K are differences of two bounded prefixes and
therefore have absolute value <=2m, where m=e/gcd(d,e). Antitone-weight
Abel summation gives a tail bound 2m/(d(K+1)). Since d(K+1)>e,

    |sum_{k<L} w_d,T(k) [F_e(d-1+dk)
        - 1_(K<=k)(gamma(d,e)-A_e)]|
      <= K/e + 2m/(d(K+1)) <= 1/d + 2/gcd(d,e).

This is a dependency-closed paper candidate for **birth-delayed conditional
centering**, uniform in the interior modulus after retaining the gcd factor.
It is stronger for the actual anchored observable than the raw logarithmic
estimate. It still does not sum the signed modulus pairs or establish the
strict contraction. The anchored identity, pair inequality, arbitrary-
coefficient BVI bridge and actual-prefix affine correction are now verified
in the second leaf. The remaining signed delayed-drift operator is open.
No numerical experiment is used.

Corpus searches completed for raw harmonic, coprime-coherence and
birth-delayed estimates. All report `partial=false` and no search errors;
both candidate lemmas and source arguments were inspected. Birth-delayed
wording returned mostly unrelated hits; the coprime query returned the
certified orbit-prefix bound, exact interior bridges and nearby harmonic
estimates. Results are source-index evidence, not compiler certificates.
No existing delayed-centering inequality was found in those query results.
The second leaf has since passed its original-source and public-axiom audits.

### Next signed-coupling candidate: the complete prime-box pair drift

**Priority correction after the user's corpus-search reminder:** do not
start another Euler-box formalization before using the existing all-depth
operator and Gram theorems below. The scalar calculation in this section
is a secondary candidate, not a newly established frontier.

The new pair estimate still loses the Mobius signs on summing over e.
Live corpus query `gcd mobius finite Euler product conditional mean`
(`--module BezoutValuationIncidence`) completed with `partial=false`, no
search errors. Candidate lemmas and source arguments were inspected.
The existing finite divisor-polynomial factorization in
`CrossDepthEulerOperatorFactorizationAndPrimePairGramIdentity.lean`
(theorem `dirichlet_moebius_sum_divisors_prime_mul`) supplies relevant
arithmetic infrastructure. It does not itself prove the following claim.

For a finite set P of primes, let Q be its product, s=1+epsilon>1,
u_p=p^(-s), v_p=p^(-s-1), and consider the exact complete-box quantity

    S_P = sum_{d|Q} sum_{e|Q}
      mu(d)mu(e) d^(-s) e^(-epsilon) gamma(d,e).

The candidate factorization, derived symbolically from the certified gamma,
is

    2 S_P = [prod_p (1-2u_p+u_p^2) - prod_p (1-2u_p)]
          - [prod_p (1-u_p-v_p+u_p^2) - prod_p (1-u_p-v_p)].

For the first bracket, the four prime states (neither, d-only, e-only,
both) contribute 1,-u,-u,u^2; removing the both-state gives the coprime
product. For the second bracket, they contribute 1,-u,-v,u^2 because
the gcd factor supplies p on the both-state. Subtracting the two
non-coprime contributions is exactly 2*gamma.

All bases satisfy 0<1-2u_p<1-u_p-v_p. For nonnegative q_p, the polynomial
`prod_p(r_p+q_p)-prod_p r_p` is coordinatewise increasing in nonnegative
r_p: expand over nonempty sets of selected q factors. Taking q_p=u_p^2
therefore predicts S_P<=0, strictly if P contains at least two primes.
This contrasts with the nonnegative fixed-d row mean above: alternating
jump weights are essential to the pair drift.

**Status:** next conjecture with a paper factorization argument; the exact
arithmetic/source bridge and Lean certificate are not yet audited. It is
not substituted for the actual triangular birth cutoff or claimed as the
requested contraction. After completing the delayed-centering certificate,
audit this signed mean and then its finite-cutoff defect. No numerical
experiment or assumption about that defect has been used.

### Expanded corpus audit after user correction

The first ranked pages were insufficient. A lexical OR query for birth,
interior, conditional, cross-depth and contraction was paginated through
all 195 declaration hits across 19 BVI modules. Direct target references
to the interior martingale/counterterm were also mapped (75 source lines).
Two deeper mechanism queries, one in BVI and one across the full corpus,
returned partial results. Their proof ideas, ingredient sets, source
arguments and compiler coverage were inspected; limitations appear below.

Previously underused existing work, now read in source:

- `all_depth_coherent_pmStepVectorTotal_eq`: exact signed Hilbert dilation
  polynomial across every squarefree depth.
- `all_depth_coherent_primitiveGram_cube_eq` and
  `all_depth_coherent_energyCenteredGram_cube_eq_of_not_isPrimePow`:
  exact Gram factorizations retaining all signed cross-depth terms.
- `all_depth_alternating_shell_singularity_cancellation` and
  `all_depth_singularity_cancelled_stepSource_re_eq`: the scalar Euler
  singularity already cancels; the surviving object is a scale-difference
  operator. Reproving a scalar cancellation is not the priority.
- `summable_cross_depth_primitiveGram_prime_shift` and its energy-centered
  counterpart: unconditional single-prime shifted-covariance summability
  for each fixed base modulus. This is stronger infrastructure than the
  bare finite product identity used in the initial search.
- `cross_depth_bandResidue_cancellation_summary`: reciprocal residue
  summability after cross-depth cancellation is already available.
- `sieveVarianceAboveParity_successorPredictor_bounds`: a sharp 1/4
  contraction exists for the same-node coefficient variance after parity
  removal. Its norm and observation operator differ from the requested
  physical finite-horizon interior martingale; a transfer is required.
- `sum_bezout_active_pair_martingale_compensated_le`: an active-pair upper
  bound is already proved. Its statement is not an interior bound.

Next route selection must explain the bridge from these signed operators
to the actual incomplete birth cutoff and retained density correction.
The delayed single-pair estimate remains an auxiliary theorem, not a
replacement for this existing cross-depth machinery or the full goal.

Further lexical search found a direct physical bridge that the first audit
missed: `DilationProfileIntegerJumpCoupling.lean` (read in full, 229 lines).
`pmRamanujanDilationProfile_eq_integerDilationGram` identifies the literal
rational Hilbert profile with the integer-cell pronic pairing.
`abs_dilationProfile_sub_finite_lag_sectors_le` bounds the full additive-lag
cutoff error by `sqrt(p)*sqrt(q)*B_r^2/(H+1)`, and
`dilationProfile_quadratic_horizon_coupling` gives `B_r^2/Q` for p,q<=Q
at physical horizon Q^2. The successor sector retains the exact reciprocal
successor kernel, rather than an averaged surrogate. All 13 hits of the
dilation/finite-horizon lexical query were retrieved without module caps.

**Revised next conjecture:** use the existing profile/lag-sector bridge on
signed dyadic blocks of the all-depth coefficients. For scales
`Q<=p<2Q`, `R<=q<2R` and coefficients `mu(p)p^(-1/2-epsilon)`, the square
roots in the tail cancel the half powers. Triangle inequality only on the
cutoff error predicts a bound

    B_r^2 * Q*R * Q^(-epsilon)*R^(-epsilon)/(H+1).

At H=max(Q,R)^2 this is bounded by
`B_r^2 * min(Q,R)/max(Q,R) * (Q*R)^(-epsilon)`, summable over dyadic pairs
for each positive epsilon and fixed base r. The main finite-lag quadratic
form keeps its signs. This is a candidate error bound, not a contraction:
base-modulus uniformity, the actual coefficient cutoff, and a coercive
bound for the surviving signed lag form still require proof. It supersedes
the scalar prime-box mean as the immediate research priority.

The subsequent `Gram` search scoped to
`TruncatedPronicGramMatrixAndFiniteHorizonVonMangoldtApproximation`
found existing positive-semidefinite truncated Gram forms, their exact
finite-horizon energy representation, monotonicity, and the remainder
bound `sieveVariance * sievePeriodFreeDualCeiling / (H+1)`. Its
`abs_truncatedPronicGram_prime_pair_defect_le` already supplies the
finite-horizon prime-pair recurrence defect. Reuse these statements;
do not present a generic Gram-tail inequality as a missing theorem.

`PronicResidueGapEnergyAndPrimePairDistance.lean` was subsequently read in
full. It already proves the exact pre-overlap prefix energy
`h*harmonic(floor(p/h)) - h^2/p * K^2/(K+1)`, matching lower and upper
harmonic-gap budgets, and the literal centered-prime Gram distance as
residue distance minus the squared logarithmic mean difference. These
are transport bounds for differences of modes; they do not bound an
unmodified signed packet. Reuse them if a transport decomposition is found.

The global deep query `dyadic signed dilation profile cutoff error`
completed without partial stages, but its candidate/source-argument sets
mostly concerned different dilation or collar problems. Its proposed plan
combined unrelated Harman and contour-error results and was rejected.
The narrower `dyadic Schur` lexical query was inspected through all 36
hits; it supplies a geometric renewal-chain Schur lemma but no direct BVI
martingale transfer. Broad OR query results are not an exhaustive novelty
audit; the next search is restricted to the literal BVI profile/error APIs.

Both deep mechanism searches completed partially (local runtime deadlines:
BVI semantic retrieval; global decomposition). Retrieved candidate lemmas,
source arguments and proposed ingredient sets were inspected. The proposed
plans are unverified; the BVI plan includes conditional end criteria and
does not prove a strict contraction. The broad global plan matched
irrelevant meanings of "control" and "cube" and was rejected. Shorter
semantic searches also timed out without candidates. Lexical searches and
direct source verification supplied the useful discoveries above. Search
absence is not a proof that no further existing result applies.

The auxiliary delayed-centering source (385 lines, eleven public
declarations) passed the original-source audit in session 67436, exit 0,
no diagnostics. All public axioms and eleven existing frontier APIs passed
together in session 45245, exit 0, with only `propext`, `Classical.choice`
and `Quot.sound`. Source and fresh artifact evidence are recorded;
no full-contraction claim is made.

### Further corpus reuse: observation geometry and natural cutoffs

The narrowed BVI profile/error deep search completed with no partial stages.
Its candidate lemmas and source arguments confirm the existing literal
integer-jump coupling and truncated-Gram bounds. The separate physical-
coercivity search also completed, returning the existing coefficient-one
interior identity and compensated residual asymptotic, not a new strict
bound. Proposed ingredient sets remain unverified suggestions.

All 42 lexical successor/harmonic hits were inspected. The already compiled
`DilationSuccessorSectorHarmonicClassification` and
`DilationSuccessorDigammaRenormalization` give the exact selected mean
`mu(r)` when both scales are coprime to r (zero otherwise), a uniform
harmonic remainder, and the explicit digamma finite part with inverse-
horizon error. These concern additive lag-one jump sectors; they cannot be
silently identified with the full interior martingale. Nine reused APIs
from these leaves, the residue-gap leaf and truncated-Gram leaf passed a
combined API/axiom audit (55791, exit 0; standard axioms only).

The cofinal physical-cutoff deep search completed without partial stages.
It recovered `cofinal_moebiusPrefixDiscrepancy_sublinear`, exact quotient-
band formulas and renormalized-gradient identities. Sublinear prefix
control alone does not imply pronic square summability. Its proposed plan
calling a subpower divisor bound a horizon-independent constant was not
accepted. The predictor/physical-kernel deep query returned partial results
after its reranking deadline; all 20 candidates and 20 source arguments
were inspected.

That search exposed an important existing positive classification:
`SharpInitialPrefixObservabilityAndExactGramDeterminants.lean` already
classifies the exact kernel at every cutoff/horizon. For T>0, vanishing
initial observations means all coefficients at 2..min(T,N) vanish and the
remaining tail harmonic sum is zero. At T=N-1, all nonconstant coefficients
are recovered; explicit interpolation, sharpness witnesses and positive
definite variance-dual Gram matrices are already formalized. All 49 lexical
prefix/observability hits were inspected. The companion
`TranslatedWindowStrideAnnihilationAndLcmReturnObservability.lean` also
gives the quantitative recovery bound `2*tau(d)*prefix_sup_error`.
Do not reprove an invisible-prefix obstruction without using its existing
classification and positive recovery theorem. Finite injectivity alone
does not give horizon-uniform conditioning, and a short-horizon kernel is
not an obstruction at the actual full cutoff T=N.

The proposed dyadic error summation is therefore auxiliary. At common
physical horizon N^2, the known entrywise tail is already compatible with
a simple finite coefficient-sum bound. The actual target has observation
horizon T and modes born up to T; replacing it by N^2 does not control that
triangular cutoff. A future proof must quantify the signed physical Gram
form at the actual horizon, retaining the affine density term and natural
denominator order. The coefficient-space quarter contraction is not a
proved bound in this physical Gram norm.

The corpus also contains a concurrently written, uncompiled draft,
`NaturalCutoffMultiDepthCofactorAndConditionalTailBridge.lean` (audited
snapshot SHA-256 `4af0f572c40f99c14b0bd52bb4eb3cb8f344d07b195baf3042416088184b3414`).
All 27 natural-cutoff hits were inspected. Its head/tail decomposition is
relevant, but `naturalCutoffTailResidual_eq_uncentered` as written drops
the term `-(H+1)*pmPowerDampedRamanujanEnergyMean epsilon Q`. If f is the
uncentered prefix and m its full pronic mean, the definitions expand to

    residual(n) = f(H+1+n) + (H+1)*sum_{k<=H} f(k)/(k(k+1)) - (H+1)*m.

At H=0 the omitted term is already -m. Jointly shifting f and its mean
does preserve the residual; dropping the mean while holding f fixed does
not. This draft has no compiled artifact and is excluded from dependencies.
It is being edited concurrently, so this audit preserves its source and
records the precise correction rather than overwriting that work. The
scratch Lean check of the exact expansion and zero-mean condition passed,
alongside four existing observability API/axiom checks (35700, exit 0).
All six closures use only standard Lean axioms. Logs, archived inputs and
source/artifact freshness are in
`logs/bvi-corpus-reuse-2026-10-18-audit-manifest.json`. All owned processes
are terminal; fourteen more search files and two API scratch files were
archived and removed. Full contraction remains open.

Subsequent concurrent source snapshot
`42f8df3e1a141f18981acd2b98110aadac27073f780493894947ba9d5e9304ac`
restored exactly the missing `-(H+1)*mean` term and corrected its
documentation. This task did not edit that source. It subsequently acquired
a compiled artifact; its final hash and artifact freshness are in the
corpus-reuse audit manifest. The earlier search results describe the older
draft. Its APIs were not part of the thirteen additional reuse checks.
Concurrent changes also added 29 README lines after the auxiliary theorem's
certificate was created. This task has made no README edit; preserve those
external changes rather than interpreting the earlier empty diff as a
current global invariant.

- 2026-10-18 — Opened before proof implementation; corrected target notation from actual source. Full contraction remains open.
- Scratch checks are terminal; their local elaboration errors were corrected.
  They are superseded by the successful original-source check and complete
  public axiom audit in the current checkpoint. Source assembly files are
  temporary implementation artifacts, not continuation inputs.

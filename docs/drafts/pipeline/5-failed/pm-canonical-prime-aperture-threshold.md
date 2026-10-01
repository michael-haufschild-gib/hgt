# Canonical prime-aperture norm threshold

- **ID:** pm-canonical-prime-aperture-threshold
- **Stage:** 5-failed (canonical prime-budget producer retired; exact strict-interval classification formalized)
- **Type:** PROVED NO-GO with exact positive upper boundary
- **Source:** Route PM / PM-31 literal finite-prime Fermi sources
- **Status:** CLOSED. Both strict threshold intervals proved on paper and formalized in Lean; all actual artifact audits passed. Endpoint1/2 remains unclassified.
- **Target:** For each fixed 0<epsilon<1/2, canonical primes-through-N source
  norms tend to infinity. For epsilon>1/2, all finite prime subsets have an
  explicit finite common norm bound. Endpoint epsilon=1/2 remains unclassified.

## Paper argument for the lower side

Let F_N be the actual finite-prime Fermi source at fixed epsilon and canonical
prime aperture P_N. Its certified finite Euler expansion gives, for 0<Re(s)<1,

`Mellin(F_N)(s) = H(s) zeta(s) product_{p in P_N}(1-p^(-s-epsilon))`,

where `H(s)=(1-2^(1-s))/s`. This is a finite identity, with no convergence
assumption on the full Euler product.

For real s with 1/2<s<1-epsilon, put u=s+epsilon in (0,1). Every factor is
positive and at most 1-1/p. The reciprocal finite product at u=1 dominates
the harmonic sum through N by its smooth-number expansion. Thus the finite
product tends to zero, and Mellin(F_N)(s) tends to zero throughout this real
interval. Only harmonic divergence is needed; no numerical prime estimates.

Suppose some subsequence N_j tending to infinity had uniformly bounded
canonical L2 norms. The exact physical stabilization of finite-prime
coefficients gives F_{N_j}(t) -> A_epsilon(t) for each t>0. Fatou then admits
the actual A_epsilon in canonical L2 with the same bound.

Mellin evaluation passes to this limit for Re(s)>1/2. A direct proof splits
at delta>0: sources stabilize exactly on [delta,1] for sufficiently large
N_j, while Cauchy-Schwarz bounds the head (0,delta) by a constant times
`delta^(Re(s)-1/2)`, uniformly in j. Hence Mellin(A_epsilon)(s)=0 on the
real interval above. Its already-proved analyticity on Re(s)>1/2 forces it
to vanish throughout that connected half-plane, including s=1.

But the certified exact mean is `log(2)/zeta(1+epsilon)`, which is nonzero
for epsilon>0. Contradiction. Absence of any bounded cofinal subsequence
forces the canonical finite-source norms to tend to infinity.

## Positive boundary candidate

For epsilon>1/2, the already-certified individual generator estimate and
|mu(d)|<=1 give, for every finite prime subset S,

`||F_{S,epsilon}||_2 <= 3 sum_{d>=1} d^(-epsilon-1/2) < infinity`.

This separates the two open damping intervals for the prime
aperture approximation mechanism. The positive survivor is the precise
Mellin-limit obstruction together with the explicit unconditional upper
budget above the threshold. No claim at epsilon=1/2 is made.

The literal complete source A_epsilon may still be admitted below 1/2;
unbounded prime-aperture approximants do not refute its admission or RH.
This theorem excludes a producer stronger than the actual admission goal.

## Prior evidence and novelty audit

- Search1048 (`finite prime Fermi Mellin Euler product norm unbounded`): all
  20 candidate and 20 source-argument statements reviewed; no generated
  ingredient sets or ideas. No exact canonical PM norm-threshold theorem
  returned. Results include `finitePrime_lseries_factor`,
  `finiteEulerProduct_eq_sum_powerset` (located by source inspection), and
  phase-sensitive Euler bounds in `ThetaPrimeScheduleSpectralObservation`.
  Those are possible interfaces, not proofs of this physical assertion.
- Partial=false; 63831 files; generation1172947, coverage1172947/current1172948.
  Semantic coverage unmeasured (reporting budget); background refresh incomplete.
  Bounded search coverage is not an exhaustive novelty claim.
- Existing PM leaves supply finite-source admission/stabilization, mean,
  generator norm bounds and Mellin analyticity after actual admission.
- Pending: verify exact finite Euler/Mellin formula, real product decay,
  bounded-subsequence Mellin transfer, analytic identity theorem, and both
  strict threshold intervals. No Lean code has been written for this card.
- Search1049 (`finite Euler product real exponent below one tends to zero via
  harmonic sum lower bound`): all 20 candidate and 20 source-argument statements
  reviewed. Partial=false; 63835 files; generation1173021, coverage1173034,
  current1173040. Semantic coverage unmeasured; background refresh incomplete.
  The generated exponential-decay chain assumes decay and leaves product
  convergence as an obligation; its absolutely summable Euler-product theorem
  does not supply the below-one limit. Rejected as a producer. Direct source
  inspection instead located `PrimeExhaustion.tendsto_prod_one_sub_inv` in
  `ThetaCutoffCommutatorCofinalLimit`, a relevant existing product-limit lemma.

- Further interface tracing located the directly applicable
  `PrimeExhaustion.tendsto_prod_one_sub_rpow` in
  `ThetaPrimeDeletionSpectralEscape`: with `w=u-1/2`, its exact hypotheses
  are `0<u<=1`. Its proof derives decay from divergent prime reciprocal sums.
  Prepared unrun scratch1051: six declarations for the explicit all-subset
  norm budget above1/2, canonical prime exhaustion and real Euler-product
  decay. The finite Mellin identity and norm-divergence argument remain open.

- Search1052 (`bounded L2 pointwise convergence Mellin integral transfer`):
  reviewed all20 candidate/all20 source statements and the generated two-step
  smooth-weight/Cauchy-kernel chain. None supplies the required PM limit
  transfer; the chain changes the carrier and leaves decay/integrability
  premises unproved. Partial=false;63842 files; generation1173222,
  coverage1173239/current1173240; snapshot freshness differs, semantic coverage
  unmeasured and background refresh incomplete. These hits do not certify the
  candidate. Direct mathlib source inspection found generic Lp/Vitali and
  Cauchy-Schwarz interfaces; exact head stabilization remains the simpler
  planned transfer. Prepared unrun scratch1053 for the finite complex Mobius
  powerset identity and exact finite-source Mellin/Euler formula.

- Broadened lexical query1054 (`"mellin" "tendsto"`):208 matches in119
  modules,170 eligible; reviewed all20 returned declarations and5 exploration
  statements directly in source. Existing limits concern different carriers,
  absolute-convergence strips or stronger convergence hypotheses; no exact
  bounded PM approximation transfer returned. Prepared unrun scratch1055 with
  the generic supported-function Mellin cutoff estimate and exact canonical
  source stabilization for `t>1/(N+1)`. These are interfaces, not a completed
  divergence proof.

- Finite-deletion predecessor is now closed with its exact arbitrary-finite-E
  positive survivor:21 fully audited PM-31 leaves /4864 lines /355 declarations.
  This card is the current candidate; no fixed-damping divergence is yet claimed.

- First1051 check elaborated the absolute common budget and canonical Euler
  decay, with one remaining zero-term simplification error and redundant
  congruence tactics. Replaced those directly; corrected full six-declaration
  scratch checks. Scratch1055 now contains five unrun declarations, including
  cofinal Fatou budget transfer and the planned bounded-subsequence Mellin
  limit proof. Scratch1053 remains unrun; no new leaf promoted for this card.

- Corrected six-declaration1051 passed empty. First finite-Mellin check1053
  required only explicit `IntegrableOn` unfolding; after correction all five
  finite-Mellin declarations elaborated in the combined check. The combined
  seventeen-interface check accepted the cutoff estimate/stabilization and
  Fatou transfer, while the convergence/analyticity helpers needed explicit
  composition unfolding, real-cast annotations and both nonnegative arguments
  of `ENNReal.ofReal_add`. Corrected those. Prepared the five-declaration
  capstone: real Euler product cast, finite Mellin decay, no bounded cofinal
  subsequence, eventual exceedance of every real budget, and canonical norms
  tending to infinity. Full22-declaration combined scratch1057 is now checking;
  no capstone result is claimed until that exact file passes.

- Full22-declaration check reached both capstones; only two elaboration issues
  remained: the unspecified constant in the analytic zero-accumulation sequence
  and an implicit aperture in the finite-Mellin rewrite. Both are now explicit;
  corrected full scratch checks. All cutoff/Fatou/Mellin-transfer declarations
  elaborated. The upper-bound proof also covers arbitrary finite integer
  apertures: the retained coefficient is either Mobius or zero, so the same
  absolute generator bound applies. This stronger positive statement has the
  same dependency-closed paper proof; no prime premise is needed there.

- Corrected full22-declaration scratch1057 passed empty. Promoted/wired
  `PMPowerDampedMobiusPrimeThreshold`: fixed `0<epsilon<1/2` forces canonical
  prime-aperture norms to tend to infinity; `epsilon>1/2` has the explicit
  finite common absolute budget for every finite integer aperture. The exact
  finite Mellin/Euler identity, shrinking-support limit transfer, analytic
  uniqueness and nonzero mean are all in the checked dependency chain.
  Targeted build and final actual-leaf/body/name/API/import/axiom audits remain.
  No assertion at epsilon=1/2, or actual small-positive admission/RH, is made.

- Repository promotion has436 lines/22 declarations. Exact-body, exhaustive
  name/API, unique-import and proof-debt checks passed; targeted build remains
  active. Latest lint: eleven unrelated unwired modules and two concurrently
  stale generated files; no owned/proof-debt finding.
- Follow-on admission search1059 (`power damped Mobius Haar canonical L2
  positive damping Abel source admission`): all20 candidate/all20 source
  statements and the generated damping/decay chain reviewed. Partial=true;
  63849 files; generation1173497,coverage1173500/current1173501. Semantic
  coverage unmeasured; background refresh incomplete. The chain supplies
  unrelated damping bounds and assumes an ODE decay premise; it does not
  produce the missing arithmetic source bound. Available hits include the
  already-certified generator norm and different weighted Deninger products,
  with no exact small-positive admission producer. Rephrased query1060 toward
  the weighted-divisor Haar representation and its boundary contribution.

- PM-31 canonical prime threshold fully audited: `PMPowerDampedMobiusPrimeThreshold`
  (436 lines / 22 declarations), targeted old build197s, final actual leaf empty,
  all exact-body/name/API/unique-import/standard-axiom gates passed. For every
  fixed0<epsilon<1/2, canonical prime-aperture norms tend to infinity and
  eventually exceed every finite budget. The exact positive survivor is the
  explicit common finite budget `3 sum_d d^(-epsilon-1/2)` for epsilon>1/2,
  valid for every finite integer aperture, together with the proved finite
  Mellin identity and bounded-cofinal Mellin transfer. Endpoint1/2 unclassified.
  Combined: twenty-two leaves /5300 lines /377 audited declarations. Latest
  global lint: eleven unrelated unwired modules and two concurrently stale
  generated files; no owned/proof-debt finding. Retired canonical prime-budget
  producer with the strict-interval classification fully proved on paper and
  in Lean. Actual source admission at arbitrarily small positive damping and
  unconditional RH/negRH remain open. Next card:
  `pm-centered-divisor-haar-criterion`, an exact mean-centered discrepancy
  energy criterion with paper argument and corpus audit; no new Lean yet.

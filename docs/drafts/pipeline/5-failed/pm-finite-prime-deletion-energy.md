# Finite prime deletion and the full subset budget

- **ID:** pm-finite-prime-deletion-energy
- **Stage:** 5-failed (uniform-budget producer retired; exact positive survivor formalized)
- **Type:** PROVED NO-GO with an exact positive family
- **Source:** Route PM / PM-31, strengthened from prime-two deletion.
- **Target:** Every finite common norm bound over all finite prime subsets fails arbitrarily near zero damping.
- **Status:** CLOSED. Negative capstone and strongest arbitrary-finite-set positive survivor proved on paper and formalized in Lean; all artifact gates audited.

## Exact positive candidate

Write H for Haar supported on (0,1]. For a,b>0 its dilation Gram kernel is

`K(a,b) = integral H(a*t) H(b*t) dt = max(0, 2/max(a,b) - 1/min(a,b))`.

To prove this, assume a<=b and split at 1/(2b), 1/(2a), 1/b and 1/a.
If b>=2a, the coarse Haar is -1 on the whole finer support, whose mean
is zero. If a<=b<=2a the three nonzero intervals give 2/b-1/a.
Thus every Gram entry is nonnegative, and K(a,a)=1/a.

For a finite deleted prime set E, let M(E) be the positive integers whose
prime factors all lie in E, and define

`B_E(t) = sum_{n in M(E)} H(n*t)`.

This is pointwise finite for t>0. The sum of L2 norms is
`sum_{n in M(E)} n^(-1/2) = product_{p in E}(1-p^(-1/2))^(-1) < infinity`.
Consequently the series converges strongly in canonical L2 to the literal
pointwise source, not merely by a one-sided Fatou bound. It has mean zero
and support in (0,1]. Absolute Hilbert summability justifies its exact energy

`||B_E||_2^2 = sum_{m,n in M(E)} K(m,n) >= sum_{n in M(E)} 1/n`.

The positive survivor is this exact nonnegative Gram decomposition and
canonical admission for each finite deletion set. The diagonal equals
`product_{p in E}(1-1/p)^(-1)`. For E containing all primes through N,
M(E) contains every integer 1,...,N, so energy is at least the Nth harmonic
sum. Harmonic divergence suffices; no prime-distribution estimate is needed.

## Arithmetic identification and obstruction

Let mu_E be Mobius restricted to integers with no prime factor in E.
The existing `CoprimeMobius.sum_divisors_mobiusAF` proves that its divisor
sum is the indicator of M(E). Finite divisor reindexing therefore gives

`-sum_d mu_E(d) phi_d(t) = B_E(t)` for t>0.

Equivalently, apply the divisor identity to the two floor sums in phi_d.
All sums involved here stop at floor(1/t); no infinite arithmetic interchange
is needed. Finite prime apertures `(primes through M) \ E` stabilize pointwise
to this source as M tends to infinity.

If C is a common finite norm bound for every finite prime subset at every
sufficiently small positive damping, parameter continuity plus Fatou gives
the same bound at zero for each finite subset. A second Fatou limit gives
`||B_E||_2 <= C` for every finite E. The harmonic energy lower bound then
contradicts finiteness of C. This excludes the entire all-subset uniform
budget mechanism, not a bound restricted to canonical full prime cutoffs.
It does not prove or disprove RH or settle the actual complete source.
The proposed contradiction needs one C independent of damping near zero;
a finite bound C(epsilon) at each fixed positive damping is not excluded.

## Prior research and gates

- Query 1040: all 40 candidate/source statements reviewed. It returned the
  existing dyadic resolvent and unrelated operator carriers, no general
  prime-deletion physical norm theorem. Coverage on the dyadic card.
- Query 1041 (`Haar dilation inner product finite prime deletion Euler product norm`):
  all 20 candidate and 20 source-argument statements reviewed; no generated
  ingredient chains/proof ideas. Returned Euler deletion and Sonin/Deninger
  kernels do not supply this literal Haar kernel or its arithmetic bridge.
  Partial=false; 63808 files, generation/coverage/current 1172362. Semantic
  coverage unmeasured (reporting budget); background refresh incomplete.
- Direct source inspection found finite smooth-monoid power summability in
  `SteinhausEulerSmoothSeries` (used by `SteinhausSmoothPairError`) and
  `ThetaCuspFinitePrimeFluxWindow`, plus the exact coprime-Mobius divisor
  identity in `CoprimeMobiusSumsZeroFree`.
- Completed: exact Haar Gram formula; strong L2 smooth-series identification;
  arithmetic finite-floor reindexing; harmonic lower bound; actual finite
  prime subset exceedance; arbitrary-finite-E energy/admission; all actual-leaf
  and artifact audits. The dated entries below record intermediate progress.
- No numerical experiments, additional axioms, or RH premises are used in
  the paper argument. All Lean interfaces remain to be verified.

## Working log

- First fifteen-declaration Haar-kernel scratch passed empty after resolving
  exact division forms and function-coercion integral rewrites. It proves
  the exact min-expression, symmetry, nonnegative entries and diagonal 1/a.
  Added eleven declarations for the max-expression, separated-support
  orthogonality, dilation admission/energy, and exact finite complex Haar-sum
  energy, diagonal lower bound and monotonicity. Full scratch1042 is checking.
- Search1043 (`coprime Mobius sum floor smooth divisor identity`): all 20
  candidate and 20 source-argument statements reviewed, no generated chains
  or ideas. `coprime_moebius_floor_summatory` and generic
  `Sieve.sum_Icc_divisorsAntidiagonal_swap` supply the actual finite hyperbola
  reindexing; `CoprimeMobius.sum_divisors_mobiusAF` supplies its exact deleted
  coefficients. Other inverse-divisor/LCM statements are distinct carriers.
  Partial=false; 63813 files, generation/coverage/current1172437; semantic
  coverage unmeasured, background refresh incomplete. Applicability still
  requires Lean verification. No infinite arithmetic exchange is needed.

- Full 26-declaration Gram scratch needed three interface fixes: the global
  finite-sum integrability name, splitting the imaginary part of the Haar
  conditional, and pointwise rather than function-valued finite-sum admission.
  All other new declarations elaborated, including exact max kernel and
  finite energy monotonicity. Corrected full scratch is checking.
- Search1044 (`eLpNorm tsum summable Lp strong convergence sum`): all 40
  candidate/source statements reviewed; no generated chains or ideas.
  Mathlib `LpSpace.InfiniteSum` supplies the ae representative of an absolutely
  summable Lp series (`Lp.coeFn_tsum`, inspected at source), which can identify
  the literal smooth series after Hilbert summation. Other lp/orthogonal
  statements do not bypass the actual representative check. Partial=false;
  63813 files; generation1172491, coverage1172488/current1172492; semantic
  coverage unmeasured and background refresh incomplete.

- Full 26-declaration Haar Gram scratch passed empty. Promoted/wired
  `PMPowerDampedMobiusHaarGram`: exact max kernel, nonnegative entries,
  exact finite energy, diagonal lower bound and finite-subset energy
  monotonicity. Targeted build and artifact gates pending. Prepared unrun
  scratch1045 for the actual ae representative of the Hilbert series and
  passage of all finite diagonal lower bounds to the literal infinite sum.

- Haar Gram leaf targeted old build passed (152s). All 26 exact bodies,
  exhaustive unique names, public API entries and unique umbrella import
  passed; final actual leaf is checking, axiom audit remains. Current lint
  reports thirteen unrelated unwired modules and no owned/proof-debt finding.
  Prepared unrun scratch1046 for the fixed smooth-number Haar source,
  canonical admission, harmonic/log energy lower bounds, energy divergence,
  and exact finite physical-cutoff expansion. It depends on unrun1045.

- PM-31 Haar Gram leaf fully audited: `PMPowerDampedMobiusHaarGram`
  (211 lines / 26 declarations), targeted old build 152s, final actual leaf
  empty, all exact-body/name/API/unique-import/standard-axiom gates passed.
  It proves K(a,b)=max(0,2/max(a,b)-1/min(a,b)), finite Haar-sum energy,
  diagonal lower bounds and energy monotonicity under finite inclusion.
  Combined PM-31: seventeen leaves / 4063 lines / 278 audited declarations.
  Latest lint: thirteen unrelated unwired modules; no owned/proof-debt finding.
  Hilbert-series scratch1045 is checking; smooth-source scratch1046 is
  prepared but unrun. The stronger all-subset budget no-go is not closed.
  Canonical small-positive admission and RH remain open.

- Thirteen-declaration Hilbert-series scratch1045 passed empty. Added the
  exact complex vector Gram identity and iterated double-tsum energy identity.
  First extension check needed explicit function-coercion changes and the
  correct inner-map interface; corrected full sixteen-declaration scratch
  is checking. Prepared unrun1047 with five declarations for finite divisor
  floor summation, exact coprime-Mobius counts and the literal deleted Fermi
  source. It will need the smooth-count identification and finite-prime
  stabilization before the budget obstruction can close.

- Full sixteen-declaration Hilbert-series scratch passed empty after explicitly
  setting the scalar field in inner-product symmetry. Exact actual-series
  admission, finite diagonal lower bounds and iterated double-Gram energy
  are proved. Promoted/wired `PMPowerDampedMobiusHaarSeries`; targeted build
  and actual artifact audits remain. Scratch1046 (eight declarations) and
  scratch1047 (five declarations) remain prepared, unrun and unpromoted.

- Hilbert-series leaf targeted old build passed (92s), final actual leaf
  empty and all16 exact-body/name/API/unique-import gates passed; standard
  axiom reports are checking. Extended unrun1046 to sixteen declarations:
  smooth-source admission, exact Gram energy, harmonic/log divergence,
  support and zero mean with proved canonical L1 integrability. Extended
  unrun1047 to nine declarations including exact smooth-count and deleted
  Mobius source identification. Finite-prime stabilization and the uniform
  budget contradiction still need implementation and verification.

- PM-31 Hilbert-series leaf fully audited: `PMPowerDampedMobiusHaarSeries`
  (151 lines / 16 declarations), targeted old build 92s, final actual leaf
  empty, all exact-body/name/API/unique-import/standard-axiom gates passed.
  Summable dilation norms identify the actual pointwise series with its
  Hilbert sum; exact energy is the iterated Gram sum and dominates every
  finite reciprocal diagonal. Combined: eighteen leaves / 4214 lines /
  294 audited declarations. Latest global lint: seventeen unrelated unwired
  modules and three concurrently stale generated files; no owned or proof-debt
  finding. Sixteen-declaration smooth-source scratch1046 checks next;
  nine-declaration arithmetic scratch1047 is prepared and unrun. The broader
  no-go and canonical small-positive admission/RH remain open.

- Full sixteen-declaration smooth-source scratch passed empty after explicit
  cutoff rewrites, subtype arguments and membership annotations. It proves
  canonical L2/L1 admission, zero mean, support, exact Gram energy, harmonic
  lower bound and energy divergence. Promoted/wired
  `PMPowerDampedMobiusSmoothHaar`; targeted build and artifact audits pending.
  Arithmetic scratch1047 now has sixteen unrun declarations, including finite
  prime-difference apertures, exact coefficient/source stabilization and
  their Fatou norm-budget transfer. The final uniform-budget contradiction
  remains to be implemented after these interfaces pass.

- Prepared complete 23-declaration arithmetic/budget scratch1047, still unrun:
  finite divisor counts; literal source = smooth Haar sum; physical L2/L1,
  mean and exact Gram energy; finite prime-difference stabilization; Fatou
  transfer; and the capstone that every finite real budget is exceeded by an
  admitted actual finite prime source arbitrarily near positive zero. The
  capstone uses the proved energy divergence, not a numerical experiment.

- PM-31 smooth-source leaf fully audited: `PMPowerDampedMobiusSmoothHaar`
  (147 lines / 16 declarations), targeted old build 4.6s, final actual leaf
  empty, all exact-body/name/API/unique-import/standard-axiom gates passed.
  Each fixed smooth-number Haar source is canonically L2/L1, supported in
  (0,1], with zero mean and exact nonnegative Gram energy. Its energy
  dominates the harmonic sum and diverges with the prime cutoff. Combined:
  nineteen leaves / 4361 lines / 310 audited declarations. Latest global
  lint: ten unrelated unwired modules and three concurrent generated-file
  changes; no owned/proof-debt finding. Full 23-declaration arithmetic/budget
  scratch1047 checks next. The broader all-subset no-go is not closed yet.
  A separate paper candidate `pm-canonical-prime-aperture-threshold` tests
  divergence at fixed epsilon<1/2 even for canonical prime cutoffs, paired
  with explicit all-subset bounds for epsilon>1/2. No Lean proof of that
  stronger candidate is claimed. Actual small-positive admission/RH stay open.

- First complete 23-declaration arithmetic/budget check found only two
  elaboration issues: rewriting an inequality inside an if-dependent
  Decidable instance, and a beta-redex in the physical energy integrand.
  Replaced the former with simp-only and reduced the latter explicitly.
  All other declarations, including the finite-budget capstone, elaborated.
  Corrected full scratch is checking; no no-go closure is claimed yet.

- Corrected complete 23-declaration arithmetic/budget scratch passed empty.
  Promoted/wired `PMPowerDampedMobiusFiniteDeletion`. Literal prime-deleted
  Mobius sources equal the admitted smooth Haar sources, with zero mean
  and exact Gram energy. Every finite all-subset uniform budget near zero
  is exceeded by an admitted actual finite source. Targeted build and all
  actual artifact audits remain before no-go closure.

- Arithmetic leaf targeted old build passed (115s); final actual leaf passed
  empty, and all23 exact-body/name/API/unique-import checks passed. Standard
  axiom reports remain in progress. Latest global lint reports eleven unrelated
  unwired modules and three concurrently stale generated files; no owned or
  proof-debt finding. The paper survivor covers arbitrary finite deleted-prime
  sets, so closure also requires that generality. Prepared unrun scratch1050
  with22 declarations: finite-set smooth Haar admission, zero mean, exact Gram
  energy, Euler-product diagonal lower bound, and their literal deleted-Mobius
  source identities. It uses mathlib's finite factored-number geometric sum;
  no new analytic premise or computation is introduced.

- PM-31 arithmetic/deletion leaf fully audited: `PMPowerDampedMobiusFiniteDeletion`
  (283 lines / 23 declarations), targeted old build115s, final actual leaf empty,
  every exact-body/name/API/unique-import/standard-axiom gate passed. Literal
  deleted Mobius sources equal smooth Haar sums. For every finite budget and
  every positive damping neighborhood, an admitted actual finite prime source
  exceeds that budget. Combined: twenty leaves / 4644 lines / 333 declarations.
  Global lint: eleven unrelated unwired modules and three concurrently stale
  generated files; no owned/proof-debt finding. The strongest arbitrary-finite-set
  positive survivor is prepared in scratch1050 (22 declarations), now checking.
  No-go closure awaits that exact generality; actual small-positive admission
  and unconditional RH remain open.

- First full arbitrary-finite-set check accepted21/22 declarations. The sole
  issue was reciprocal normalization in the Euler-product diagonal bound.
  Normalized both sides explicitly; corrected full scratch1050 is checking.
  No mathematical gap or additional premise was exposed by that check.

- Corrected full22-declaration arbitrary-finite-set scratch passed empty.
  Promoted/wired `PMPowerDampedMobiusFiniteSmoothSource` (220 lines/22 declarations).
  Every finite deleted-prime source is canonically L2/L1, has zero mean,
  equals its smooth Haar series, and has the exact nonnegative Gram energy
  bounded below by the reciprocal Euler product. Targeted build and final
  actual artifact audits remain before retiring the uniform-budget route.

- PM-31 arbitrary finite-deletion survivor fully audited:
  `PMPowerDampedMobiusFiniteSmoothSource` (220 lines / 22 declarations), targeted
  old build7.7s, final actual leaf empty, all exact-body/name/API/unique-import/
  standard-axiom gates passed. For every finite E, the literal deleted-Mobius
  source equals its strongly summable smooth Haar series, is canonically L2/L1,
  has zero mean and exact nonnegative double-Gram energy, with reciprocal Euler
  product diagonal lower bound. Combined: twenty-one leaves / 4864 lines /
  355 audited declarations. Global lint: thirteen unrelated unwired modules
  and two concurrently stale generated files; no owned/proof-debt finding.
  Retired `pm-finite-prime-deletion-energy`: every finite all-subset bound
  uniform in damping near zero is impossible, with the exact arbitrary-finite-E
  positive survivor now on paper and in Lean. This does not exclude a finite
  C(epsilon), canonical-only bounds, or actual small-positive admission.
  Next candidate: `pm-canonical-prime-aperture-threshold`; scratch1051 checks
  the upper boundary and real Euler decay, while1053/1055 remain unrun.
  Unconditional RH/negRH remain unproved.

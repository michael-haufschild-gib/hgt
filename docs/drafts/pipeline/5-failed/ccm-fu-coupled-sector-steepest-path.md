# CCM-FU: source-directed transverse cost through the coupled prime sector

- Stage: 5-failed — both frozen finite claims numerically falsified; no Lean counterexample asserted.
- Type: [DIAGNOSTIC], aimed at the open exhaustive-selection producer.
- Full chain: actual divisor source → renewable reserve → exhaustive selection → uniform O(M) signed Abel bound → RH.
- Frontier map read only.

## Question frozen before execution

The failed smallest-prime sign rule does not decide whether another
small prime gives descent. The exact helper commutation theorem makes
this a separate arithmetic question: two-coordinate helper operations
do not alter any of the future transverse gains under consideration.

Start with P={3,5,7,11,13}, retain prime two, and consider every unprocessed
prime q with 15≤q and q²≤M. This is the coupled small-prime sector; primes
above the square-root threshold are not accepted as trivial replacement
choices. Repeatedly insert the q giving the least exact-source transverse
energy gain, breaking numerical ties by prime size. Continue until the
whole sector is processed, even if its least gain is positive.

Two competing finite claims are frozen:

1. Every chosen step has nonpositive transverse gain.
2. If the first claim fails, the sum of all positive gains along the
   complete deterministic path is at most the initial transverse energy.

The second claim is a separate proposed cumulative budget, not a renamed
version of the failed nonpositive-step claim. Neither finite claim is RH.
A proof must eventually control every cutoff and both receiving coordinates,
and include the remaining primes above the square-root threshold.

## Frozen experiment and discriminating outcomes

Use the same four physical cutoffs 512,2048,8192,32768, with one complete
steepest path at each. This is a new path-selection question, not a larger
or repeated version of the fixed-prime sign screen. Generate the actual
source using the previously reviewed quotient-block routine. At every
step store every candidate's gain, the selected prime, processed core,
complete transverse energy, receiving coordinates and accumulated positive
cost. Verify each selected paired-cost formula against explicit fibre
merging before continuing.

Tolerance is 1e−10*max(1,Q_empty). A strict local trap requires EVERY
remaining candidate gain to exceed that tolerance. If one occurs, audit
the first by cutoff and path position independently at 80 decimal digits
from the original time-sum source, including every candidate and explicit
merger verification. Otherwise no audit is triggered. Record whether the
complete cumulative positive cost exceeds its proposed initial budget.
No extrapolation, range extension or parameter tuning follows automatically.

Run only on the supplied RunPod, four independent cutoff workers,
numerical-library threads one. Primary and audit each have internal
90-second and external 100-second deadlines, with five-second kill grace.
Download code, results and hashes under computations; remove every owned
remote file and process. No computed result enters Lean.

## Outcome

The first strict trap occurs at M=2048 after processing 43 and 41.
Every remaining candidate 17,19,23,29,31,37 has strictly positive gain.
An independent 80-digit reconstruction from the original time sum
confirms all six gains and their explicit mergers. Prime 37 minimizes
the gain, at 13.20512723206545235753... . Thus choosing a different next
prime within this remaining sector cannot give descent at this state.
This does not exclude avoiding the state by a different earlier order,
processing prime two, or choosing a prime outside the sector.

The complete steepest path at M=32768 has cumulative positive cost
647640.1280592964, exceeding initial transverse energy
573684.4280751749 by a ratio of about 1.12891356. This second claim has
binary64 evidence with explicit merger checks at every step; it was not
the frozen high-precision audit target. No statement about unbounded
growth, every ordering, or the RH endpoint follows.

The [computation record](../2-fully-proven/computations/ccm-fu-coupled-sector-path-2026-09-08/README.md)
contains both scripts, complete paths, independent audit and matching
local/remote hashes. Both jobs used four workers and completed in less
than one second of recorded Python runtime. Owned remote workers exited;
the remote directory, including its import cache, was removed.

## Direct proof attempt and exact remaining obstacle

The corpus supplies the signed identity

    Δ_q T = 2 Σ_{R≠empty,{2}; q∉R} F_R F_{R∪{q}} − F_{q}² − F_{2,q}².

The six positive audited gains occur in this complete expression; small
receiving coordinates do not force its sign. The existing
`mobiusDivisorTwoTransverseEnergy_union_gain_union` theorem makes its
additional-core increments unchanged by every admissible two-coordinate
helper block. Those helpers spend a fixed reserve rather than improving
the next-prime comparison.

Three possible replacements were examined against the corpus:

1. Fixed-core distant-prime orientation: the physical release is
   `2ρ(P+p)p^(-3/2)W_P(p)`, but its eventual sign threshold depends on P.
   Exact renewal includes `−sqrt(p)W_P(Y/p)`. Comparable next primes
   therefore create an actual positive cost of order `1/p`, already
   proved in `MobiusDivisorComparablePrimeCost`; the fixed-core tail
   theorem does not give a uniform changing-core selector.
2. Absolute quotient costs: `MobiusDivisorUniformSuccessorTransport`
   gives `|Δ_q Q| ≤ (6/5) floor(M/q) sqrt(M Q)` uniformly in P. Under a
   quadratic ceiling this is an upper bound proportional to
   `M^(3/2) floor(M/q)`. Charging that upper bound separately across the
   growing sector does not supply the required quadratic total budget.
   The sharper small-core square bound retains a factor
   `4^(card(P below M/q+1)−1)`; that factor is not uniform along the path.
   Neither observation is a lower bound on actual signed costs.
3. Net excursion instead of positive variation: if `g_i=T_{i+1}−T_i`,
   then the energy at a prefix uses the signed sum of the `g_i`, while
   the rejected budget counts every `max(g_i,0)`. A failed positive-
   variation budget does not reject a bound for signed peak excursion.
   No uniform source estimate for that peak, compatible helper capacity,
   or the two receiving coordinates was obtained.

These are failures of specific proof steps, not a falsification of the
remaining bounded-energy construction. The missing arithmetic work is
uniform control of the full signed mixed sum through an exhaustive,
changing processed core, with the actual available reserve charged once.
The square-root terminal ordering theorem still requires its actual
terminal endpoint bound and cannot supply that missing work.

## Strongest positive survivor and audit status

The strongest established survivor remains the
[exact complementary-energy decomposition and reserve commutation](../3-formalized/ccm-fu-transverse-reserve-commutation.md).
It retains every signed transverse pair, proves nonnegativity of the
complete complement, and identifies the same reserve translation for
every additional finite core. Its paper proof and six Lean theorems were
already checked; this experiment adds no numerical premise to them.

NO NEW POSITIVE SALVAGE FOUND in the second pass above. Larger constant
budgets, different earlier orders and signed peak control remain
unproved possibilities, not replacement theorems. No new Lean module was
created or build launched for these numerical rejections. RH remains open.

## Wider corpus comparison

Whole-corpus searches used explicit OR (`--any`) for alternative concepts,
then single-term and selected-module queries. Multi-term defaults are AND;
an empty narrow query is not evidence that a mechanism is absent. Cached
searches returned 994 declarations in 160 modules for
`dissipation passivity martingale coarea`, 1324 in 310 modules for
`amortized reserve excursion Lyapunov`, 225 in 20 modules for `Bellman`,
and 23 in 10 modules for the OR alternatives `"Carleson"`,
`"stopping time"`, `"upcrossing"`, `"energy increment"`, `"square function"`.
These are retrieval counts, not a claim that every matching proof was read.
Selected mechanisms were checked directly in their source:

| Corpus mechanism | Exact useful content | Missing source step for CCM-FU |
|---|---|---|
| `RouteEPhysicalFibreCoarea.predecessorEnergy_eq_successorEnergy_add_dissipation` | Regrouping conditional signed means loses exactly a nonnegative variance; energy is `Σ moment² / mass`. | This is not raw retained energy `Σ F_R²`. A uniform comparison must retain the changing positive fibre masses. |
| `RouteEUniformComparisonEndpoint.abs_mean_le_sqrt_two_reference_add_two_defect_sq` | A reference fibre field and its complete physical comparison defect bound the signed mean. | No small comparison defect for the actual divisor fibres was supplied. Choosing a reference field does not prove the required arithmetic closeness. |
| `GibbsSignedCovarianceAccumulation.gibbsNormalizedCurrentEnergy_insert_add_dissipation` | Signed insertion retains a nonnegative same-sign dilation-coherence loss. | Its normalization includes the partition mass, and its input contains both dilation scales. The same module proves that the proposed accumulated-forcing-minus-baseline bound is exactly the endpoint bound. |
| `GibbsCriticalDissipationAntiscaleResonance.gibbsSameSignDissipation_eq_zero_iff_antiscale` | Exact null direction is reversal of normalized current across the prime dilation. | Nonnegative dissipation alone supplies no quantitative lower loss when that coherence is nearly null. |
| `ConstitutiveCausalJordanFormation.reserve_fuse` | Opposite visible increments create exactly the triangle-inequality defect as additional cancellation reserve. | The identity records cancellation already present; it does not supply future opposite-sign literal prime coefficients. |
| `ExcursionBoundDischarge.absorbingCompletion_excursionBound` | Appending one exact cancelling push bounds every finite excursion by the completed list length. | The appended push is defined from the terminal depth. An available arithmetic prime block realizing it with a uniform cost is still required. |
| `DiscreteLiouvilleGreen.lgNormalizedEnergy_succ_sub` and `lgVirialTerm_succ` | A recurrence-derived virial correction cancels leading signed energy drift. | Its unimodular second-order recurrence has not been realized by this changing divisor-fibre field. Defining a correction from the desired endpoint would not establish that recurrence. |

The normalized-variance identity is the closest alternate way to retain
all signs while guaranteeing local dissipation. Its physical mass
comparison is an explicit additional obligation, rather than an
unconditional route around the signed Abel estimate. The general
absolute-scale requirement is already recorded in
`universal-law-field/STATUS.md` as
`MUST-CONTROL-CANCELLATION-AT-THE-ABSOLUTE-SCALE`; no duplicate ledger
entry or frontier-map edit is needed.

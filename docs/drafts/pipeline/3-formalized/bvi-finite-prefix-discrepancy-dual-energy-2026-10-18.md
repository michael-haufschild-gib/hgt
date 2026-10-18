# Exact dual energy of finite-prefix discrepancy

- **ID:** bvi-finite-prefix-discrepancy-dual-energy-2026-10-18
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper and Lean verified)
- **Contribution:** 004; one connected package, verified total 4/250.
- **Lean:** `formal/GaloisForLFunctions/BezoutValuationIncidence/ExactFinitePrefixDiscrepancyDualityAndReturnTimes.lean`
- **Statement:** Exact best variance-normalized bound for the linear finite-prefix
  discrepancy, with an attaining weight, all-level constant classification, and
  exact common-divisibility return times.

## Motivation

The unrestricted successor moment cone is already classified. Removing divisor six
sharpens its upper endpoint, but neither result controls signed finite-prefix errors.
This package identifies the exact arithmetic quantity controlling each fixed prefix.

## Paper proof [PROVED HERE]

For a level `N`, prefix length `M`, and sieve weight `c`, set

`L(M,N,c) = Σ_{d=1}^N c(d)(⌊M/d⌋ - M/d)`.

Define the real Ramanujan prefix coefficient by the finite divisor formula

`r_e(M) = Σ_{d|e} d μ(e/d) ⌊M/d⌋`.

The existing finite inverse gives the exact identity

`L(M,N,c) = Σ_{e=2}^N r_e(M) Y_N(c,e)`.

Weighted Cauchy–Schwarz gives

`L(M,N,c)² ≤ V(N,c) A(M,N)`,
`A(M,N) = Σ_{e=2}^N r_e(M)²/φ(e)`.

The inverse profile `Y(1)=0`, `Y(e)=r_e(M)/φ(e)` for `e≥2` attains
`L=V=A`. Every denominator in the nonconstant index set is positive.
Thus this is an attained exact operator norm, not merely an upper estimate.

The full boundary-sensitive universal classification is

`(∀ c, L(M,N,c)² ≤ K V(N,c)) ↔ (N≤1 ∨ A(M,N)≤K)`.

For `N≤1`, both forms vanish. Otherwise the extremizer gives `A²≤KA`,
which forces `A≤K` when `A>0`. If `A=0`, the pure divisor-two inverse profile
has variance one; testing it forces `K≥0=A`. Conversely, `A≤K` and nonnegative
variance imply the asserted universal bound by the Cauchy inequality.

The zero set is exactly

`A(M,N)=0 ↔ ∀ d∈[1,N], d∣M`.

If `A=0`, the universal inequality forces `L=0` for every weight. Testing the
weight supported at `d` gives `0=-{M/d}=-(M mod d)/d`. Since `d≥1`, this is
equivalent to `d∣M`. Conversely, common divisibility kills every fractional-part
defect and hence every discrepancy. Applying that fact to the extremizer, whose
discrepancy is `A`, forces `A=0`. This argument includes the empty levels and `M=0`.

For completeness, the coordinate identity is dependency closed. The existing inverse
has prescribed Selberg coordinates. Applied to the coordinates of `c`, its difference
from `c` has zero coordinates on `[1,N]`; the already proved tail-zero equivalence
with cutoff zero makes their original coefficients equal throughout `[1,N]`.
The existing `pmRamanujan_sum_primitive_eq_residue` identity then applies to `c`.
Its residue combination is exactly the fractional-part sum, since
`Int.fract(M/d)=(M mod d)/d`. The constant term cancels because the divisor-one
Ramanujan primitive is `M`. The remaining coordinates give the displayed formula
for `L`. The divisor formula for `r_e` is the real part of the existing
`pmRamanujanPrimitive_eq_floor` identity.

Weighted Cauchy follows termwise from
`(r_e Y_e)²=(φ(e)Y_e²)(r_e²/φ(e))`; both factors are nonnegative. Substitution of
the inverse extremizer profile proves `L=V=A` directly. No numerical search,
asymptotic estimate, or unproved cancellation premise is used.

At `M=1`, this specializes to the already present centered Cauchy bound with
`A(1,N)=Σ_{e=2}^N μ(e)²/φ(e)`. That special case is not new and is not counted.
No growth estimate or square-root cancellation claim follows merely from the exact norm.

## Prior-research status

- `PMRamanujanPeriodDiagonal` already provides finite inversion, complete-period
  covariance, and a Ramanujan primitive / residue-combination identity. Reuse those
  mechanisms and do not count their reformulation as new research.
- `ChineseRemainderBezoutPeriodicityAndSawtoothDefect` already provides exact quadratic
  finite-prefix decompositions and an absolute-value remainder estimate.
- A focused lexical corpus search in
  `KerPCenteredSieveAndFirstSecondMomentReciprocity` finds the existing exact first-moment
  identity and its absolute-value estimate. Its endpoint projection theorem invokes
  `sq_div_sum_sqfreeTotientInv_Icc_two_le_selbergTotientDiagonalForm_of_harmonic_eq_zero`
  in `BarbanVehovLogarithmicDiagonalAndKerPCauchyPinch`: the centered `M=1` Cauchy bound
  with denominator `Σ μ(e)²/φ(e)` is already present. Do **not** count that special case
  or the generic Cauchy argument as new. Any contribution must establish the full
  prefix-dependent exact constant, extremizers, and return-time classification.
- Deep corpus searches `Ramanujan shift covariance finite prefix` and
  `Ramanujan prefix dual norm` did not return this exact norm classification.
  The first search was partial; the second reported complete source inventory but
  predominantly unrelated candidates and mostly pending compiler metadata.
  This does **not** establish novelty or lemma applicability.

## Fresh corpus audit

- The deep query `sharp variance normalized sieve finite prefix discrepancy Ramanujan
  partial sums` was partial (reranking deadline); it supplied no competing exact norm.
  Partial retrieval is not evidence of exhaustive absence.
- Focused lexical searches returned all seven `sievedFractSum` hits and all five
  `residueCombination` hits. They provide first-moment identities, absolute-value
  bounds, periodicity, and complete-period covariance, not the sharp prefix constant
  or its return-time classification.
- `CenteredRamanujanVarianceAndAbelCofactorCancellation` concerns damped-source
  sawtooth means and reciprocal-time Gram energies; its centering decompositions do
  not classify the variance dual norm of an arbitrary fixed finite prefix.
- Reuse mathlib's `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` and
  `Int.fract_div_natCast_eq_div_natCast_mod`; do not reprove those facts.

## Plan and gates

1. [x] Renew corpus novelty and dependency audit.
2. [x] Complete the paper argument, including degenerate levels and zero dual energy.
3. [x] Verify APIs and formalize the exact identity, extremizer, optimal constants,
   and return-time classification under the field directory.
4. [x] Named-module audit, scratch axiom audit, umbrella wiring, index, lint,
   ledger registration, and temporary-file cleanup.

`update_plan` is unavailable; this card stores the plan. A shared Lean build remains
active, so use an isolated compiled-import snapshot if needed. One owned Lean process
at a time; no full or umbrella builds.

The scratch proof passed with exit 0. Its unused-variable and redundant-tactic
warnings were removed before the named-source check. The final source contains
12 public theorems, 3 definitions, and 4 private helpers. The named-source check
and full public-theorem axiom audit passed without warnings. Count as one connected
contribution, not as separate credit for the helpers or individual corollaries.

## Verification evidence

- Installed-toolchain API scratch check: exit 0.
- Full public-theorem axiom audit: exit 0. Every one of the 12 public theorems
  depends exactly on `propext`, `Classical.choice`, and `Quot.sound`.
  Raw audit: `logs/bvi-root-2026-10-18-prefix-duality-axioms.txt`.
- Named original-source check: exit 0, no warnings, using `lake --old env lean -j 1`
  with the explicit original package root. The resulting `.olean` was installed
  in the normal build directory; SHA-256 equality and source-relative freshness
  were checked.
- Full proof scratch check: exit 0; final source removes the reported unused binding
  and redundant `ring` tactics.
- `scripts/formal_tools.py index`: exit 0. Focused lexical query returned all 19
  declarations; compared every name against the source, with no omissions or extras.
- All 10 current field modules have umbrella imports.
- `scripts/formal_tools.py lint`: exit 1, with eight unrelated BiScaleUncertainty
  umbrella omissions: `CentralBinomialRatioGrowth`, `EndpointCycleDeterminant`,
  `FactorialPolarGramScaleSeparation`, `FactorialPolarLossAsymptotic`,
  `FactorialPolarLossLowerBound`, `SharpCycleGramRealization`,
  `SharpGramDetectionOrder`, `StationaryResolventMarkovPositivityAndNodalDefectProducer`.
  No field finding or proof-debt violation was reported. Leave those other-agent
  modules untouched.
- The shared long-running Lake build continues changing inherited artifacts.
  Named-source and axiom checks therefore use a cloned compiled-import snapshot,
  with the original source path and explicit original `formal/` package root.
- Cleanup guard: exit 0. All 25 owned temporary paths were removed; original source
  and the installed compiled artifact were preserved and rechecked.

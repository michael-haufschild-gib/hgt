# Fixed logarithmic Möbius convergence forces critical simplicity

- **ID:** pm-log-mobius-boundary-multiplicity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route PM; PM-26 exact scalar normalization budget.
- **Status:** Complete paper proof and audited Lean implication; canonical convergence and unconditional RH remain open.
- **Statement:** If `logMobiusFermiErrorEnergy N → 0`, every zero of zeta on `Re ρ=1/2` has `ζ'(ρ)≠0`.

## Exact question

Does convergence of the literal logarithmic Möbius Fermi approximation in
canonical `L²(dt)` imply simplicity of every critical-line zeta zero, in addition
to RH? This is an audit of the fixed coefficient choice. It is not a proof of
critical simplicity, RH, failure of approximation, or an equivalence with RH.

## Proposed paper proof and obligations

Write `B_N=Σ_(d≤N) μ(d)log(N/d)/d` and
`m(x)=x⁻¹∫_0^x ψ(t)/t dt`. PM-26 proves

`(N+1)(B_N−m(N+1))²/log²N ≤ 6 E_Fermi(N)`.

Thus canonical error convergence would give
`B_N−m(N+1)=o(log N/√N)`. Define the real-cutoff sum
`B(x)=Σ_(d≤x) μ(d)log(x/d)/d`.

For `N≤x<N+1`, the exact cell identity is
`B(x)−B(N)=H_N log(x/N)`, where `H_N=Σ_(d≤N)μ(d)/d`.
The absolute harmonic majorant gives an error `O(log N/N)`. The corpus linear
ψ bound gives `|m(x)−m(N+1)|=O(1/N)`. Consequently

`δ(x):=B(x)−m(x)=o(log x/√x)`.

For `Re s>0`, the proposed exact transform is

`F(s)=∫_1^∞ δ(x)x^(−s−1) dx
     =1/[s²ζ(1+s)] + ζ'(1+s)/[(1+s)²ζ(1+s)]`.

The little-o budget would make the literal integral holomorphic on
`Re s>−1/2`. Analytic continuation of the denominator-free identity would retain

`s²(1+s)² ζ(1+s) F(s) = (1+s)²+s²ζ'(1+s)`.

At a critical zero `ρ`, an Abelian split at a large fixed cutoff should give
`ε² F(ρ−1+ε)→0` for real `ε↓0`: on the tail, the normalized integral of
`log x · x^(−1−ε)` is bounded, while its coefficient is arbitrarily small.

If also `ζ'(ρ)=0`, analyticity makes `ζ(ρ+ε)/ε²` bounded locally. Multiplying
this bound by the vanishing Abel quantity forces the left side of the cleared
identity to tend to zero. Its right side tends to `ρ²≠0`. This contradiction
would establish simplicity without assuming a contour residue expansion or
an unproved bound on the reciprocal zeta function.

Initial proposal recorded above; the dependency audit and paper certificate below
now close the paper implication. The complete Lean transfer remains unfinished.

## Inspected corpus and reuse

- `FermiNymanLogMobiusAuxiliaryVariance` supplies the literal scalar budget.
- `MobiusLaplaceBoundaryMultiplicity.lean`, lines 1–36 and 216–325, already
  proves that exact half-power decay of a different Möbius–Laplace source implies
  RH and boundary simplicity. Its radial-product argument is relevant; its
  source decay premise is not available here. The general mechanism is not new.
- `ChronologicalWeightedMellin.lean`, lines 1–158, supplies absolute Mellin
  interchange for `Σμ(n)w(nt)` at `Re s>1`, requiring actual Mellin convergence
  of `w`. It also proves exact finite cutoff identities. Its bounded-weight
  corollaries do not apply to the unbounded ramp needed here.
- All of `Sieve/MoebiusShiftedLogRealCutoff.lean` was read. Existing
  `moebiusShiftedLogKernelReal 0 x` is precisely the proposed real sum `B(x)`.
- All 189 lines of `RieszMellinPair.lean` were read. In namespace
  `GaloisForLFunctions.RHTower`, `integral_Ioi_log_cpow_neg_succ` and its
  integrability theorem prove `∫_1^∞ log x · x^(−s−1)=1/s²`, `Re s>0`.
- Mathlib Mellin transform source supplies `mellin_comp_inv`,
  `MellinConvergent.cpow_smul`, `mellin_cpow_smul`, and indicator power transforms.
  Exact signatures must still be exercised in scratch Lean before reuse.

A concrete coefficient-transform construction is to take
`L(x)=log x` for `x>1`, zero otherwise, and `w(t)=L(1/t)/t`.
Then `B(1/t)=t·Σμ(n)w(nt)` for `t>0`. Mellin inversion of the argument and the
existing logarithmic integral should give `mellin(w)(s+1)=1/s²`; the actual
Möbius-weighted source theorem then supplies the reciprocal-zeta factor.
The prime mean needs its own exact logarithmic prime-sum or integral transform.

## Search coverage

Two completed deep searches were fully reviewed, all 20 candidate and 20
source-argument statements in each: logarithmic approximation/multiplicity
(63,604 files) and logarithmic sum/Mellin/reciprocal-zeta transform (63,609 files).
Both reported `partial=false`, no errors and complete inventory; compiler
metadata remained mostly source-only, pending or stale. Neither returned the
proposed fixed-coefficient simplicity implication. Their suggested ingredient
sets do not establish it. Targeted `rg` located the stronger applicable sources
listed above. No universal novelty claim follows from these searches.

## Gates

- [x] Record exact candidate and distinguish it from known source-decay criteria.
- [x] Initial corpus search and applicability audit.
- [x] Prove the complete paper argument, with exact real-cutoff conventions.
- [x] Formalize literal coefficient and prime-mean Mellin identities.
- [x] Formalize discrete-to-continuous necessary budget.
- [x] Formalize analytic continuation and vanishing quadratic Abel quantity.
- [x] Formalize the boundary simplicity implication with no added axiom.
- [x] Targeted build, actual-leaf, axiom, wiring/index/lint audits and cleanup.

PM-29 and PM-30 audits are complete. The unconditional RH goal remains active.

Further API/source preparation: mathlib `MellinConvergent.comp_rpow` was read
at lines 75–85 and the Mellin shift/inversion identities at lines 99–156.
The logarithmic-ramp transform can reuse the fully inspected Riesz pair via
argument inversion and the power shift, including convergence, without
reproving complex logarithmic integration. No new code for this card yet.

Prime-mean applicability check: inspected the literal formula in
`RiemannXiSuzukiPointwiseChebyshevLogAverageMellinKernel` lines 25–85 and its
transform in `RiemannXiSuzukiPointwiseChebyshevLogAverageMellinTransform`
lines 413–499. That source carries weights `Λ(n)/√n` and a different main term.
It is not the literal mean `m(x)` above; its transform must not be substituted
without a separate source identity. The first 125 lines of
`CCMUnitRieszCausalLaplaceBridge` concern a different causal normalization and
also do not identify this mean. Prefer an exact applicable primitive or a
general absolute Mellin interchange over introducing a normalization mismatch.

Prepared an uncompiled ingredient draft `/tmp/pm_logarithmic_mellin_1009.lean`
for the logarithmic ramp, reciprocal ramp, and literal Möbius-weighted Mellin
identity on `Re s>0`, reusing the inspected Riesz pair and absolute interchange.
It does not yet identify its reciprocal profile with the existing finite
real-cutoff coefficient, nor prove any simplicity implication. PM-29 axiom
audit still owns the only foreground Lean slot; no new source-tree code here.

## Continued formal preparation

PM-29 is fully audited and retired with its positive survivor. All 21 owned
`1008` files are cleaned. No preceding audit remains outstanding.

The first logarithmic Mellin scratch now passes: exact transforms of the ramp,
reciprocal ramp and actual Möbius dilation source, including convergence. A
finite-cutoff bridge is checking next. This is still ingredient work; neither
the complete transform of `δ` nor the simplicity implication is claimed.

A further deep query for von Mangoldt/logarithmic Mellin interchange completed:
63,619 inventoried files, `partial=false`, no errors; all 20 candidate and 20
source statements reviewed. Compiler metadata is source-only. Suggested
`MellinConvolutionTransform` requires an explicit product-integrability premise
and does not discharge the prime-mean identity. Mathlib
`LSeries_eq_mul_integral_of_nonneg` was inspected; it supplies an unsmoothed
summatory transform, with a separate primitive/mean transfer still needed.

## Paper dependency audit, with constants

The following expands the proposed implication; formal transfer gates remain
open. For `N=floor x≥2`, the exact finite-cell identity and `|μ|≤1` give
`|B(x)−B(N)|≤(1+log N)/N`. Write `q=ψ/x`. The corpus bound `0≤q≤7`
gives `0≤m≤7` and, directly from its integral definition,
`|m(x)−m(N+1)|≤14/N`. Thus the discrete normalization budget indeed transfers
to `δ(x)=o(log x/sqrt x)`; replacing `N` by `x` uses `x/N→1`.
Both sources are locally integrable and vanish on `0<x≤1`.

On `Re s>0`, absolute interchange is justified separately by the convergent
series `Σ|μ(n)|n^(−1−Re s)` and `ΣΛ(n)n^(−1−Re s)`. The logarithmic ramp
integral gives respectively `1/[s²ζ(1+s)]` and
`−ζ'(1+s)/[(1+s)²ζ(1+s)]`. The latter source is exactly
`m(x)=x⁻¹Σ_(n≤x)Λ(n)log(x/n)`, by finite Abel summation with weight
`log(x/y)`. Its derivative is `−1/y`, endpoint weight vanishes, and `ψ(1)=0`.
An inspected template is
`RiemannXiSuzukiPointwiseChebyshevCumulative.integral_chebyshevPsi_eq_triangularVonMangoldtSum`:
the same finite Abel API applies after replacing the triangular weight by the
logarithmic weight. The weighted Suzuki transform itself is not used.

For every compact subset of `Re s>−1/2`, a positive margin `η` gives an
integrable tail majorant `C log x / x^(1+η)`, and each complex derivative
adds only a power of `log x`. Hence the literal `F` is analytic there.
Continue the cleared identity on the connected punctured half-plane excluding
`s=0`; no removable-pole assertion at zero is needed for the critical boundary.

For critical `ρ` and any `a>0`, choose `X` with
`|δ(x)|≤a log x/sqrt x` for `x≥X`. Uniformly for `0<ε≤1`, the compact head
of the transform is bounded independently of `ε`, while its tail satisfies
`ε² |F_tail(ρ−1+ε)|≤a ε²∫_1^∞log x·x^(−1−ε)dx=a`.
Taking `ε↓0` and then arbitrary `a↓0` proves the vanishing quadratic Abel
quantity. If `ζ(ρ)=ζ'(ρ)=0`, local analytic factorization yields
`ζ(ρ+ε)=ε²g(ρ+ε)` for analytic `g`, locally bounded. The cleared left side
then tends to zero; its right side tends to `ρ²≠0`. No reciprocal-zeta bound
near a zero, residue sum, numerical premise, RH, or simplicity assumption is
used in this contradiction. Lean must still certify the literal source
identities and every transfer before this becomes a formal implication.

A general absolute dilation/Mellin interchange draft is prepared separately as
`/tmp/pm_dilation_mellin_1009.lean`, for arbitrary absolutely convergent
Dirichlet coefficients. It is intended to instantiate the actual Λ coefficients;
it remains uncompiled while the finite Möbius bridge owns the Lean slot.

The complete finite-cutoff Möbius Mellin scratch passed with empty diagnostics.
It now includes the exact identity with `moebiusShiftedLogKernelReal 0 x`, both
physical and reciprocal-variable transforms, and all convergence assertions.
Promoted `PMLogMobiusMellinPair.lean` (11 declarations), wired it, and started
its targeted old-mode build. Final actual-leaf and axiom audits remain pending.
The missing finite-cutoff dependency target rebuilt successfully first; no
umbrella build was run.

Prepared a separate uncompiled boundary-transfer scratch using the double
`dslope` of an analytic function. This gives an exact quadratic factor whenever
both value and derivative vanish, then combines continuity with the proposed
quadratic Abel limit and cleared identity. It still requires those actual-source
premises and does not assert they have been established.

`PMLogMobiusMellinPair`: targeted old build passed (54s; own leaf only), then
final direct actual-leaf check passed empty. All 11 axiom checks now running.
The arbitrary-coefficient dilation and abstract boundary-transfer drafts remain
uncompiled. A prime-logarithmic mean draft is also prepared, but imports the
planned `PMDilationMellin` leaf, which does not yet exist: compile and build that
prerequisite first. Prime mean integral identification is still to be appended.

Further boundary reuse audit: read `ChronologicalWeightedBoundary` declaration
list and lines 15–100, 240–300. Its general Abel theorem treats an unweighted
half-power source and a linear radial factor. The present logarithmic budget
needs a quadratic factor, so it cannot be applied unchanged. Its compact-head /
small-tail split is an applicable proof template. The existing weighted-source
corollary also requires a bounded weight, unlike the reciprocal logarithmic ramp.
Read mathlib `HasFPowerSeriesAt.has_fpower_series_dslope_fslope` and
`sub_smul_dslope`: iterating the divided slope gives the needed quadratic
factor directly, with continuity at the boundary point and no reciprocal-zeta
estimate.

## First ingredient certificate

`PMLogMobiusMellinPair.lean`: 161 lines / 11 declarations. Targeted build
passed (54s), final direct actual leaf passed empty, all 11 axiom reports
parsed and checked against only `propext`, `Classical.choice`, `Quot.sound`.
Source matches passing scratch; all names/API entries and its import unique.
Index regenerated. `lint --check-generated` reports only 12 unrelated unwired
modules (the prior 11 plus `HamburgerTwistedCriticalLine`); no own, proof-debt
or stale-index error. Full PM-30 implication remains unproved.

The arbitrary-coefficient Mellin scratch first failed only on `IntegrableOn`
unfolding and a real/natural complex cast. Corrected; recheck running. Its
absolute norm-dilation and sum/integral arguments already elaborated.

Discrete-cell reuse found and inspected in full:
`Sieve.coprimeLogMoebius_one_eq_floor` already proves the exact correction
`log(x/floor x) * deningerHarmonicPartial (floor x)`.
`deningerHarmonicPartial_bounded` supplies an unconditional uniform constant,
so the formal cell bound can be `C/N`, sharper and simpler than the paper's
absolute harmonic majorant. `EulerDeletionLogPrimeForcing` also contains a
private elementary bound `|H_N|≤2`, but no need to duplicate it: use the existing
public boundedness theorem. The literal mean's finite Abel identity is drafted
in the pending prime transform scratch.

The general dilation scratch passed empty. Created and wired
`PMDilationMellin.lean` (100 lines / 4 declarations), exposing the norm-scaling
helper for reuse. Targeted old build now running; final actual-leaf/axiom/index
checks remain. The source and inference obligations in the gates above remain
open. Latest continuation memory:
`research/pm_log_mobius_multiplicity_2026_10_01`.

Prepared (not compiled) a small reuse draft for the exact unit-cell formula and
uniform `C/floor(x)` error, importing the existing finite-mean budget. For the
full transfer, a direct squared estimate avoids unnecessary square-root algebra:
for `N=floor(x)≥2`, `x≤N+1` and `log x≥log N`, so the discrete contribution is
at most `6 E_N`; after the two-term square inequality and the cell corrections,
one may bound `x δ(x)²/log²x` by
`12 E_N + 8(C+14)²/(x log²x)`. Both terms tend to zero under the proposed
canonical error premise. This remains a formal obligation, not a claimed bound.

`PMDilationMellin` targeted old build passed (46s; own leaf only), final direct
actual-leaf check passed empty. Source body matches passing scratch after making
the norm-scaling helper public. All four axiom checks now running. Next compile
the prime logarithmic mean against this checked prerequisite.

All four dilation axiom reports parsed: standard three axioms only. The first
prime-mean scratch found four local elaboration issues (unfolding the inverse
ramp, derivative function shape, cast of one in a floor bound, beta reduction
under the integral). Corrections applied; second check running. Both exact
Mellin identities and the finite sum bridge otherwise elaborated. No prime leaf
promoted yet, and no new premise or tactic-limit change introduced.

## Second ingredient certificate

`PMDilationMellin.lean`: 100 lines / 4 declarations. Targeted old build passed
(46s), final actual leaf passed empty, all four axiom reports parsed against the
standard three only. Source matches passing scratch with the helper made public;
all four names/API entries and the import are unique. Index regenerated; lint
again reports only the same 12 unrelated unwired modules, with no own,
proof-debt or stale-index error. No need to repeat these audits.

The second prime scratch left only a final sign simplification in its finite
Abel identity; corrected. Appended the literal mean-defect definition, its exact
Mellin pair and the denominator-cleared identity on `Re s>0`. Third check is
running. There is still no prime source-tree leaf or boundary transfer claim.

Cleanup: 23 completed/audited/incorporated `1009` files removed. Retained only
the active prime draft/output and the uncompiled boundary/unit-cell drafts.
Third prime check verified the exact mean-defect Mellin pair and all earlier
identities; the cleared-identity proof needed `norm_num` for the elementary
contradiction `1<0` when proving `s+1≠0`. Corrected; fourth check running.
No source-tree promotion until the whole scratch passes.

The fourth prime/defect scratch passed with empty diagnostics. Created and
wired `PMPrimeLogMeanMellin.lean` (200 lines / 13 declarations), with exact
actual-Λ transforms, the finite Abel identity, the literal defect transform and
its cleared identity on `Re s>0`. Targeted old build running; final actual-leaf,
axiom and bookkeeping audits pending. No critical continuation claimed.

The still-uncompiled unit-cell draft now also contains the `Ioc(1,x)` to
`Ioo(0,x)` mean bridge, identification at `N+1` with the PM-26 mean, and bounds
`0≤m(x)≤7` for `x≥1`. It imports this new prime leaf and must wait for its build.

## Paper certificate

The paper implication is dependency-closed after the exact source audit. The
real-cutoff sums are continuous on `x>0`: at each integer the newly admitted
logarithmic term is zero. Their compact restrictions are therefore integrable.
The discrete normalization inequality is the actual PM-26 theorem. The exact
Möbius cell identity is already in the corpus, and the mean cell estimate follows
from `0≤ψ(x)/x≤7`. Absolute Dirichlet/Mellin interchange proves both source
transforms; their exact formal scratch now passes. The compact/tail argument
above supplies holomorphy and the vanishing quadratic Abel quantity.

For completeness, the punctured complex half-plane `Re s>−1/2`, `s≠0` is
path connected: join two points by segments through a third point in the
half-plane chosen off the two lines through the origin. Thus the analytic
identity theorem applies. For `0<ε<1/2`, `s=ρ−1+ε` lies in this punctured
domain. The analytic double divided slope gives the exact quadratic factor at
a multiple zero; continuity and the cleared identity yield the contradiction
`0=ρ²`. This establishes the **paper necessary condition** that convergence of
the fixed logarithmic approximation forces critical-line simplicity. It neither
proves that convergence occurs nor proves RH or simplicity unconditionally.
The full Lean implication and its audits remain open.

A sharper mean estimate is available directly on paper: for `1≤x≤y`, write
`J=∫_x^y ψ(t)/t dt`. Both `J` and `(y−x)m(x)` lie in `[0,7(y−x)]`, hence
`|m(y)−m(x)|≤7(y−x)/y`. The pending unit-cell scratch uses this bound and
therefore gives `7/floor x` instead of the earlier sufficient `14/floor x`.

The pending mean/unit-cell draft now includes exact weighted-mean increments,
`0≤y m(y)−x m(x)≤7(y−x)`, the sharper variation bound and the resulting
`7/floor x` cell estimate. These have not been compiled. The next squared-budget
proof will combine both cell errors with PM-26, use `x≤N+1≤2N` and
`log x≥log N`, then extract little-o from the vanishing nonnegative square.

Prime leaf targeted old build passed (175s; owned leaf only). Final direct
actual-leaf check running, all 13 axiom checks prepared. Source matches passing
scratch; all 13 names/API entries and the import are unique; index regenerated.
The mean/unit-cell draft now has 264 lines, including the complete proposed
squared continuous budget with an unconditional constant. It remains uncompiled
and must not be cited as a theorem yet.

Prime leaf final direct actual-leaf check passed empty. All 13 axiom checks now
running. Latest lint reports only ten unrelated unwired modules: the two
concurrent `HamburgerTwistedCriticalLine` and `WeilConeMultiplesOfPrimeLaw`
findings have disappeared. No owned-leaf, proof-debt or stale-index finding.

The pending mean/unit-cell draft now has 314 lines / 15 declarations. It also
contains the proposed normalized-square limit and extraction of
`δ=o(log x/sqrt x)` from the canonical error premise. The proof uses only the
explicit squared budget, floor cofinality, `C/x→0`, and the square-root map.
This entire draft remains uncompiled; actual Lean certification is the next gate.

## Third ingredient certificate

`PMPrimeLogMeanMellin.lean`: 200 lines / 13 declarations. Targeted old build
passed (175s), final direct actual leaf passed empty, all 13 axiom reports
parsed and standard-only. Source/body/names/API/import checks passed, index
regenerated. Lint only ten unrelated unwired modules, no own/proof-debt/stale
finding. Together the three Mellin leaves now have 28 fully audited declarations
in 461 lines. The first continuous-budget scratch check has started; no fourth
source leaf yet. The unconditional RH goal remains open.

First full-budget check found five local elaboration issues: pointwise negation,
application of the interval-integrability equivalence, a natural-cast lower
bound, real type annotation for the floor limit, and function composition in the
square-root limit. Corrected; second check running. The finite mean variation,
cell comparison, squared budget and little-o ratio algebra otherwise elaborated.
No mathematical obstruction reported; no source-tree promotion yet.

Second budget check narrowed to three elaboration issues: simplifying an
unapplied negated function, an incorrect named cast argument, and an unapplied
function composition. Replaced them by pointwise integrability congruence,
an explicit real cast proposition, and `Function.comp_def`. Third check running;
all substantive finite-cell, mean and square-budget inequalities elaborate.

The third full-budget scratch passed empty. Created and wired
`PMLogMobiusContinuousBudget.lean` (15 declarations). Its capstone proves the
literal continuous defect is `o(log x/sqrt x)` if the canonical fixed-coefficient
Fermi error tends to zero. The finite source/mean identification and quantitative
squared budget are included. Targeted build started; final actual-leaf and
axiom audits pending. The convergence premise itself remains unproved.

For analytic continuation, the existing entire residue unit offers a cleaner
formal route than a punctured domain. With `U(z)=(z−1)ζ(z)` (entire extension),
the same exact identity is
`s(s+1)² U(s+1)F(s)=(s+1)²+s U'(s+1)−U(s+1)`.
Both sides are analytic on the entire half-plane `Re s>−1/2` once the literal
transform is shown holomorphic. Read `ZetaLogDerivResidue` lines 54–132 and
`ChronologicalWeightedBoundary` lines 184–239, 349–356 for the actual APIs.
This algebraic re-expression changes no source premise or paper conclusion.

## Fourth ingredient certificate

`PMLogMobiusContinuousBudget.lean`: 327 lines / 15 declarations. Targeted old
build passed (80s); final direct actual leaf passed empty. All 15 axiom reports
parsed and standard-only. All source/API names and the umbrella import are
unique; source matches passing scratch. Index regenerated. Subsequent lint
reported 13 unrelated unwired modules and generated-file staleness following
concurrent tree changes; no owned-leaf or proof-debt finding. Regenerate again
at the next completed leaf. Four audited leaves now contain 43 declarations.

The exact-transform continuation draft is checking. The quadratic Abel estimate
can avoid an explicit compact integral split: use the already integrable fixed
weight `|δ(x)|/x²` as a global head majorant. For a cutoff `X≥1`, the head kernel
is bounded by `X²|δ(x)|/x²`; beyond `X`, the little-o budget gives
`a log(x)x^(-1-ε)`. Adding these positive majorants globally gives
`ε²|F(ρ−1+ε)|≤a+ε²X²∫_1^∞|δ(x)|/x²`, hence the required limit. This is a
paper simplification only; its Lean implementation remains pending.

Further Abel search reviewed all 20 candidate and 20 source-argument statements.
Inventory: 63,646 files; `partial=true` from semantic/reranking timeouts, complete
inventory but predominantly pending/stale compiler metadata. The returned
Mellin/Laplace Plancherel ingredient set requires `L¹`/`L²` premises and does not
establish this radial quadratic limit. Targeted source search found the exact
real logarithmic moment `integral_rpow_mul_log_Ioi_one` and its integrability
theorem in `PrimeLogZetaAbelPole`; both proofs were read. The new draft combines
them with the fixed integrable head majorant and the actual defect budget.

The continuation scratch passed empty after local function-unfolding and analytic
composition fixes. Promoted and wired `PMLogMobiusContinuation.lean` (164 lines).
It proves the literal reciprocal source is Mellin-convergent and analytic on
`Re s>−1/2` under canonical error convergence, continues the entire-residue-unit
identity, then recovers the cleared zeta identity away from `s=0`. Targeted old
build running; final actual-leaf and axiom audits pending. The separate quadratic
Abel and double-divided-slope drafts remain uncompiled. The actual-source
simplicity assembly is drafted but depends on those unchecked ingredients.

## Fifth ingredient certificate

`PMLogMobiusContinuation.lean`: 164 lines / 13 declarations. Targeted old
build passed (50s; other dependencies replayed), final actual-leaf check passed
empty, all 13 axiom reports standard-only. Body matches passing scratch;
source/API names and the import are unique. Index regenerated. Lint reports
12 unrelated unwired modules and concurrent staleness of API/overview, with
no owned-leaf or proof-debt finding. Five certified leaves now have 56 declarations
in 952 lines. The first quadratic Abel scratch check is running; full conditional
simplicity and the unconditional RH goal remain unproved.

The first Abel scratch check accepted the global pointwise majorant, exact
logarithmic moment and radial normalization algebra. Two local errors remained:
the identity limit needed an explicit real filter type, and the base norm
integral needed an `IntegrableOn` annotation. Corrected. Assembled a 223-line
scratch with the general Abel theorem, actual defect corollary, exact quadratic
factor, boundary contradiction, physical/reciprocal integral bridge and complete
conditional simplicity statement. This combined draft is checking; none of its
new statements is yet claimed as a formal theorem. Fifth-leaf audits are fully
parsed; all completed fifth-leaf scratch files cleaned, parent/frontier summaries
synchronized to the 56 audited declarations.

The complete combined scratch passed. Promoted and wired
`PMLogMobiusBoundaryMultiplicity.lean` (242 lines / 8 declarations), including
`pmLogMobius_critical_simple_of_error`. A redundant denominator-discharge search
was replaced by the explicit already-proved `r≠0` when promoting. Targeted old
build running, followed by final actual-leaf and axiom audits. This closes the
full implication at scratch level; do not infer canonical convergence or RH.

The first targeted build and final actual-leaf check both passed, with one
algebra-normalization hint. Replaced that local rearrangement by explicit
division unfolding and associativity/commutativity; the optimized leaf is
rebuilding before its final audit. No statement changed.

Preparation for the next conjecture: a variable/higher logarithmic-smoothing
search completed with `partial=true` (reranking deadline), full 63,661-file
inventory and source-only returned statements. All 20 candidates and 20 source
arguments were reviewed. The suggested Barnes-product ingredient is unrelated
to Fermi approximation and supplies no smoothing theorem. Targeted source reads
of `MobiusLaplacePolylogBoundaryMultiplicity` (1–70, 140–187) and
`MobiusLaplacePolylogSharpCoefficientLaw` (469–511) show that fixed-polylog
multiplicity caps and maximal-order coefficient bounds are already proved for
the distinct Möbius–Laplace source. Any higher-log Fermi proposal must identify
its literal source and add more than that existing general mechanism. No next
conjecture has been accepted or implemented yet.

A second preparation query for damped Möbius/Nyman approximation returned
`partial=true` from its reranking deadline, complete 63,661-file inventory, and
source-only statements. All 20 candidates, 20 source arguments, the heat-flow
proposal and ingredient set were reviewed. The heat-flow and future-pulse
coefficient bounds do not identify the literal arithmetic approximation.
`Sieve.DampedTwist` concerns `dampedOmegaMoebius`, so its smoothing estimate
cannot be substituted for a degree-damped Möbius Fermi norm. Existing general
finite-error and Haar-approximation primitives remain relevant, but no needed
canonical convergence bound was supplied. No PM-31 claim follows from this search.

## Final Lean certificate

Capstone: `RHTower.pmLogMobius_critical_simple_of_error` in
`PMLogMobiusBoundaryMultiplicity.lean`. Six leaves / 64 declarations / 1,196
lines certify the literal transforms, finite and continuous budgets, analytic
continuation, quadratic Abel limit and critical simplicity implication.

The last leaf has 244 lines / 8 declarations. Its optimized targeted old build
passed (203s; own leaf rebuilt), final direct actual-leaf check passed with empty
diagnostics, and all eight axiom reports were parsed against only `propext`,
`Classical.choice`, `Quot.sound`. All 64 declarations across the six leaves have
completed these audits. Source/body/API names and umbrella imports checked;
indexes regenerated. Final lint reports eleven unrelated unwired modules plus
concurrent API staleness, with no owned-leaf or proof-debt finding. No global
lint pass is claimed. Owned finished scratch files cleaned after certification.

This answers the card's necessary-condition question. It does not prove that
the fixed approximation converges, that a multiple critical zero exists, that
RH implies simplicity, or that RH is true or false. The result explains why
proving this fixed approximation asks for critical simplicity as well as the
previously established RH consequence. The arithmetic convergence producer
remains missing; investigate alternate literal approximations without silently
assuming that additional boundary condition.

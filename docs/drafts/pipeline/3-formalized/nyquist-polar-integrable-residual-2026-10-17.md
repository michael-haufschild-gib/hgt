# Explicit Nyquist polar producer modulo an integrable residual

- **ID:** nyquist-polar-integrable-residual-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scope:** Infinite-Grid Tail Rigidity Beyond Trap 5; general signed correlations.
- **Status:** Certified package 14 of 100; counted once. Global lint has unrelated import errors.
- **Paper:** `docs/reports/BiScaleUncertainty/NyquistPolarIntegrableResidual.md`
- **Guide:** `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` (read-only).

## Positive survivor

For cell I_n=[log n,log(n+1)], n>=1, reuse the existing explicit producer
C_n=nyquistPolarConstant(n). For bounded continuous real H, define

    r_n(H)=integral_I_n H(x)(cosh(x/2)-C_n) dx.

These actual residuals are absolutely summable, with an explicit
uniform tail bound |sum_(n>=N) r_n(H)|<=||H||_infinity/sqrt(N), N>=1.
The residual defines a bounded linear functional, Lipschitz in
the global correlation norm, with a vanishing operator norm on distant tails.

For compactly supported H, the exact actual polar integral decomposition is

    integral_(0,infinity) H(x)cosh(x/2) dx
      = sum_(n>=1) C_n integral_I_n H(x) dx + sum_(n>=1) r_n(H).

The first series is finite for each such H. This locates every discontinuity
of the polar functional in the explicitly produced cell-average term, while the
weight-approximation residual is uniformly controlled independently of support,
energy or source count. The decomposition is certified for actual normalized
correlations and for the diffuse producer.

## Paper proof mechanism

Existing pointwise producer error and cell length bounds give

    |r_n(H)| <= ||H||_infinity/(4 n sqrt(n)).

An elementary radical comparison bounds 1/(4 n sqrt(n)) by
1/sqrt(n)-1/sqrt(n+1) for n>=1. Finite telescoping and the vanishing reciprocal
square root then give the full summable tail. The paper checks endpoint conventions,
interval orientation, operator linearity, the infinite sum and exact compact-support
decomposition. Lean must formalize these actual integrals, not an assumed interface.

## Corpus boundary and Trap 10

Search logs: `/tmp/nyquist-integrable-residual-frontier.txt` (one unrelated
factorial-producer tail), `/tmp/nyquist-integrable-residual-nearby.txt` and
`/tmp/nyquist-integrable-residual-nearby-20.txt` (all 37 declarations across five
modules inspected). Existing `ExplicitNyquistPolarAndChebyshevFactorialProducer`
already proves the pointwise cell error, O(n^-2) cell L2 error, consumer residual
and O(N^-1) dyadic L2 sum; none is new here. Existing Euler–Maclaurin quadrature
retains the polar density cost and is a different approximation.

This candidate uses the explicit producer with an unconditional all-tail bound.
It concerns exact cell averages, not point samples or prime-weighted sums. It
does not assert global polar closedness from unweighted trace decay, a Chebyshev
bound, or an arithmetic coercivity inequality. No floor counterterm subtraction.
The scientific target is the stable remainder operator and exact source of polar
escape, rather than another assumed positivity receiver.

## Gates

- [x] Focused prior-corpus search; existing producer identified.
- [x] Dependency-closed paper proof and strongest positive-survivor audit.
- [x] Exact Lean formalization with actual integrals and explicit bounds.
- [x] Direct leaves, exhaustive axiom/API checks and umbrella wiring; lint executed.
- [x] Count the full connected result once, as package 14.

## Strongest paper survivor

The actual all-tail residual is a positive bounded linear functional R_N, with
exact operator norm A_N=sum_(n>=N) integral_I_n (cosh-C_n)<=1/sqrt(N), attained
by the constant function one. It is represented by an actual nonnegative L1
kernel. Compact-source polar integrals split exactly into the explicit weighted
cell-average producer and this stable residual. The diffuse train paper forces
the producer term to diverge under compact correlations and convergent energies;
the new uniformly bounded correction cannot explain that escape. All details,
including absolute summation and endpoint conventions, are proved in the paper.
## Formal execution plan

1. Revalidate prior corpus and actual producer bounds; check the required mathlib APIs.
2. Prove the radical telescoping majorant and cell residual mass bounds.
3. Construct the actual integrable tail kernel and positive bounded residual operator,
   with exact norm and explicit vanishing tail bound.
4. Prove the compact-source polar decomposition and apply it to the diffuse producer.
5. Check every new leaf, all public axiom dependencies, imports/API entries and lint;
   then update the ledger. Count the entire connected result once. `update_plan`
   is unavailable; this card carries the plan. The field README remains read-only.

The refreshed deep search `/tmp/nyquist-residual-deep.json` completed with
`partial=false`, complete inventory and no unfinished stage or search error.
All 20 candidate lemmas and 20 source arguments were inspected; their compiler
status is source-only. The proposed ingredient set repeats the existing cell L2
bounds; it supplies no all-tail operator theorem. The six-hit current lexical
check is `/tmp/nyquist-residual-current-lexical.txt`. Actual input bounds were
read directly, and new mathlib APIs are being verified in a scratch Lean file.

Implementation uses zero-based cell k=[log(k+1),log(k+2)] and tail N starting
at log(N+1), so its unconditional rate is 1/sqrt(N+1). This is exactly the
paper's positive-integer indexing. The kernel is the pointwise sum of the
disjoint cell indicators times their explicit residual densities; its local
form and integrability are proved before the operator construction.

The six formal leaves are `NyquistResidualMass`, `NyquistResidualPartition`,
`NyquistResidualKernel`, `NyquistResidualOperator`, `NyquistPolarDecomposition`
and `NyquistPolarSourceEscape`. All six pass their direct leaf checks without
diagnostics and are wired into the umbrella. All 81 public declarations
(67 theorems, 14 definitions) have exhaustive axiom checks, with only
`propext`, `Classical.choice` and `Quot.sound`. The premise-free endpoint
`exists_smooth_diffuse_nyquistProducer_escape` constructs actual smooth sources
whose producer diverges while their residuals converge.

The follow-up search `/tmp/nyquist-point-producer-deep.json` completed with
`partial=false`, no errors and a complete file inventory. Its coverage snapshot
was five generations behind and semantic coverage was unavailable; every returned
candidate was source-only. All 20 candidate statements and 20 source arguments
were inspected. Several hits are this package's own newly indexed drafts, not
independent evidence. Existing point-sample quadrature retains the polar-density
cost in `EulerMaclaurinLevyQuadratureAndSFreeCellBounds`; its generated ingredient
proposal does not discharge a bounded all-tail node-quadrature estimate.

## Certificate

- All six direct `lake --old env lean` checks pass; the final four use `-j 1`.
- All 81 exact API name/module pairs and six unique imports verified.
- Source hashes unchanged throughout the final axiom/API audit.
- The read-only guide retains SHA256
  `dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933`.
- Index refresh exits 0. Authoritative lint exits 1 solely for nine foreign
  modules missing umbrella reachability: `ExponentialTentMoments`,
  `PhysicalCollarMixture`, `PhysicalPriceResponse`, `RegularizedGramDescent`,
  `RegularizedGramGeometry`, `RegularizedGramIteration`, `RegularizedPhysicalGram`,
  `SawtoothPhaseCancellationAndBandSpectralProducer`,
  `SignedPrimePolarSourceParameters`. No error concerns this package, and this
  lint snapshot reports no active proof hole. No repository-wide green claim.

Leaf logs: `/tmp/nyquist-residual-{mass,partition,kernel,operator}-leaf.log` and
`/tmp/nyquist-polar-{decomposition,source-escape}-leaf.log`.
Final audit logs: `/tmp/nyquist-residual-{axioms,index,lint}.log`.
Complete manifests: `/tmp/nyquist_residual_{declarations,source_hashes,axiom_coverage,verification}.json`.
Scratch axiom audit: `/tmp/nyquist_residual_axioms.lean`.

## Connected extension

The complete certificate `nyquist-weight-order-threshold-2026-10-17.md`
proves the exact growth threshold and minimal Taylor order of an integrable
weight residual, with actual smooth low-energy source sharpness. Its complete
Lean formalization is certified as package 15.

# Finite Weil joint quantile realization

Status: FORMALIZED — 2026-10-11.

Objective: realize every canonical joint law and its diagonal Gaussian
on one uniform probability space, using the existing quantile lift, and
prove pointwise convergence for every probability parameter in (0,1).
Identify the resulting pair law with the previously verified joint coupling.

Sources: local Lean corpus and installed Lean dependencies only. Corpus
quantile Galois connection and Gaussian quantile convergence are available.
Global `quantile atom` discovery returned many unrelated prime-atom routes;
scoped HTGeometry search and direct QuantileCoupling source provide the
relevant inverse-CDF and pushforward tools. No external sources consulted.

Dependency-closed proof:

1. Canonical observable CDF is a finite weighted indicator sum. At an
   interior probability p, its quantile q satisfies p<=CDF(q). There is
   an atom <=q. The largest such atom m has CDF(m)=CDF(q), hence q<=m
   by the Galois connection. Since m<=q, q is an actual atom.
2. At quadratic width the raw index/correction discrepancy is <=1 in
   absolute value. Its weighted mean is also <=1, hence the centered
   residual is <=2 at every atom. Transverse Euclidean distance is
   therefore <=2/sqrt(r+1), uniformly in the chosen quantile level.
3. Compose scalar quantile with the measurable joint lift; compose the
   Gaussian quantile with the diagonal embedding. Their uniform-space
   pushforwards are exactly the joint and Gaussian laws, and their pair
   pushforward is the existing joint Gaussian coupling.
4. Scalar Gaussian quantiles converge at every interior p. Continuity
   of the diagonal embedding and the vanishing uniform transverse bound
   imply pointwise joint convergence. Thus convergence also holds almost
   everywhere on the uniform space, without a subsequence. Continuous
   test functions inherit pointwise convergence; common-L rank-dependent
   Lipschitz tests have vanishing pointwise value differences.

Plan: verify APIs; prove finite-atom quantile range and uniform residual
bound; construct and identify the common-space laws; close pointwise and
almost-everywhere roots; wire modules; native-build and axiom-audit all
declarations; run formal lint and record unrelated failures. Goal active.

Result: canonical joint laws and their diagonal Gaussian limit have an
explicit realization on the same uniform space. Their pair law equals
the previously constructed joint Gaussian coupling exactly. For every
interior probability level p, the joint realization converges to its
Gaussian value along every natural offset sequence, without a subsequence.
Consequently convergence holds almost everywhere on the uniform space.

Every fixed continuous real test inherits pointwise convergence, without
a boundedness assumption. Rank-dependent common-L Lipschitz test families
have vanishing pointwise differences between the coupled values. These
pointwise statements use the same coupling as the existing mean-square
results. Uniformity in p is proved for transverse displacement, bounded
by 2/sqrt(r+1); no uniform full-quantile limit is asserted here.

The finite-atom theorem applies to every real canonical observable map,
including maps with coincident atom values. It uses the largest atom below
the quantile and equality of the two finite CDF sums, then the inverse-CDF
Galois connection. No analytic support premise remains.

Formal leaves in `formal/GaloisForLFunctions/RHTower/`:

- `WeilLogShiftObservableQuantileAtoms.lean`: finite CDF formula and
  interior quantile membership in the actual finite atom range.
- `WeilLogShiftUniformResidual.lean`: quadratic-width raw discrepancy,
  weighted-mean and centered residual bounds; uniform transverse distance.
- `WeilLogShiftJointQuantileLaw.lean`: projected quantile atom recovery,
  explicit joint and Gaussian quantile maps, measurability, both laws,
  exact pair law, atom identity and first-coordinate identity.
- `WeilLogShiftJointQuantileLimit.lean`: scalar quantile convergence,
  transverse bound and decay, pointwise joint convergence, almost-everywhere
  convergence, continuous tests and rank-dependent Lipschitz gaps.

Verification: four native leaf builds exited zero with empty logs.
Metadata found no issues: 23 declarations (21 theorems, 2 definitions),
8 direct imports, 7 incoming imports, each umbrella import exactly once,
fresh leaf/direct-dependency objects. Final audit used
`lake --old env lean /tmp/hgt-joint-quantile-final-audit.lean` and exited zero.
All 23 declarations use only `propext`, `Classical.choice`, and `Quot.sound`;
all 19 API references passed. All seven limit-module search hits were
inspected, including the four principal convergence/test roots; the exact
pair-law query returned one hit. No search markers. Scoped whitespace
check passed; all owned jobs exited.

Scoped `quantile finite` discovery returned seven HTGeometry hits, all
inspected; none supplied finite-atom range membership. Global discovery
reported 165 hits, chiefly unrelated prime-atom routes; coverage was
narrowed to the relevant theorem area before implementation.

Global formal lint exited 1: 5 unrelated errors, 367 warnings; no finding
in these four leaves. Unreachable modules: RHTower.CCMPolarOddPrimeJumps,
JointAncestryClusterTwoSided, PaperThetaSchurModeCharge;
HTGeometry.QKrawtchoukCompanionTriangular. Remaining error: existing `sorry`
at `CCMPolarOddPrimeJumps.lean:104`, `ccmPolarOddSource_eq_core_add_atoms`.

Artifacts use `/tmp/hgt-joint-quantile-`: `prior-search.json`,
`scoped-search.json`, `residual-candidates.txt`, `api.lean`, `api.log`,
`metadata.py`, `metadata.json`, `declarations.json`, `incoming-imports.txt`,
`final-audit.lean`, `final-audit.log`, `roots-search.json`,
`pair-root-search.json`, `lint.log`; leaf logs `/tmp/hgt-<leaf>.log`.
Only local Lean mathematical sources were used.

Possible next conjecture, unproved here: uniform joint quantile convergence
on compact probability intervals contained in (0,1), hence convergence
for rank-varying levels bounded away from both endpoints. It needs separate
corpus, paper-proof and Lean audits. The broader research goal remains active.

# Finite Weil Gaussian Wasserstein and Lipschitz convergence

Status: FORMALIZED — 2026-10-11.

Objective: discharge bounded-observable restrictions using the verified
Gaussian mean-square coupling. Prove actual Wasserstein-one convergence
and convergence of integral gaps for arbitrary rank-dependent real test
functions with one common Lipschitz constant. Cover every fixed projection
a,b, every natural offset sequence t, and the zero-variance direction.

Sources: local Lean corpus and installed Lean dependencies only. Prior
lexical search `Lipschitz integral coupling` in HTGeometry returned the
compact-space KantorovichRubinsteinDuality receiver and existence theorem.
The existing generic marginal-integral identities and coupling upper bound
remain applicable on R. GaussianQuadraticLimit supplies the new input.

Dependency-closed paper proof:

1. For the actual Gaussian probability coupling pi, let D=|fst-snd|.
   Its square is already integrable. Therefore D is in L2 and L1, and
   variance positivity gives (E D)^2 <= E D^2. Hence E D <= sqrt(cost).
2. Every real L-Lipschitz f obeys |f(x)| <= |f(0)|+L|x|. Gaussian first
   moments are finite, so f is integrable even when unbounded. The finite
   projected law also integrates f. Pull both integrability statements
   through the coupling marginals.
3. Integrating |f(x)-f(y)| <= L|x-y| gives the absolute expectation gap
   <= L E D <= L sqrt(cost), uniformly over all tests with that L.
4. Wasserstein one is nonnegative and bounded by this coupling's E D.
   Existing quadratic-cost convergence and continuity of sqrt force both
   E D and Wasserstein one to zero. The uniform bound also handles tests
   f_r that vary with rank, with no boundedness assumption.

Plan: verify APIs; formalize mean-gap bounds and test integrability;
compose quantitative Lipschitz/Wasserstein bounds and unconditional
limits; wire imports; native-build and axiom-audit all declarations;
run formal lint and document unrelated failures. No compactness or
new analytic premise may remain in the final finite Weil roots.

Result: Gaussian mean-square coupling convergence now yields actual
Wasserstein-one convergence and uniform convergence of expectation gaps
for arbitrary rank-dependent tests with a common Lipschitz constant.
Tests may be unbounded. Every fixed real projection and every natural
offset sequence are admitted, including the zero-variance Gaussian.
All analytic integrability and moment premises are discharged at the
finite Weil roots.

Formal leaves in `formal/GaloisForLFunctions/RHTower/`:

- `WeilLogShiftGaussianMeanGap.lean`: square and first-moment
  integrability, nonnegative mean distance, variance bound, and
  mean distance <= square root of quadratic cost.
- `WeilLogShiftGaussianTestIntegrability.lean`: Gaussian integrability
  of every Lipschitz test and integrability through both coupling marginals.
- `WeilLogShiftGaussianLipschitzBound.lean`: absolute expectation gap
  <= L times mean distance <= L times square root of quadratic cost.
- `WeilLogShiftGaussianWasserstein.lean`: actual Wasserstein one is
  nonnegative and bounded by mean distance and root-mean-square distance.
- `WeilLogShiftGaussianTransportLimit.lean`: mean distance, Wasserstein
  one, and all common-L rank-dependent Lipschitz expectation gaps tend to zero.

Verification: all five native leaf builds exited zero with empty logs.
The 18 declarations comprise 16 theorems and 2 definitions. Final audit
used `lake --old env lean /tmp/hgt-gaussian-lipschitz-final-audit.lean`:
all 18 declarations use only `propext`, `Classical.choice`, and `Quot.sound`;
all 23 API checks passed. Metadata audit found no issues: 9 direct imports,
10 incoming imports, every new leaf wired once into the RHTower umbrella,
all source and direct-dependency objects fresh. Scoped whitespace check
passed. All three convergence roots are indexed; scoped lexical search
returned exactly three declarations, no markers. All owned jobs exited.
No external source was consulted.

Global formal lint exited 1: 10 unrelated errors, 367 warnings, no finding
in these five leaves. Nine unrelated modules were unreachable from their
umbrellas: RHTower.CCMPolarOddPrimeJumps, JointAncestryClusterTwoSided,
ZetaCriticalCountControl, ZetaCriticalGoodRows, ZetaCriticalPairDecomposition,
ZetaCriticalRowBound, ZetaCriticalWindowStructure; HTGeometry.BoxPartitionSums,
QKrawtchoukCompanionTriangular. The remaining error was the existing `sorry`
in `CCMPolarOddPrimeJumps.lean:104`, `ccmPolarOddSource_eq_core_add_atoms`.

Audit artifacts use `/tmp/hgt-gaussian-lipschitz-`: `api.lean`, `api.log`,
`metadata.py`, `metadata.json`, `declarations.json`, `incoming-imports.txt`,
`final-audit.lean`, `final-audit.log`, `roots-search.json`, `lint.log`.
Leaf logs use `/tmp/hgt-<leaf>.log`. The broader research goal remains active.

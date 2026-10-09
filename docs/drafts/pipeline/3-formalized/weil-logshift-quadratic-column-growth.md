# Quadratic-exponent growth of late inverse columns

Status: formalized and kernel-audited. Corpus-only research, 2026-10-09. Latest global lint has 12 unrelated HTGeometry umbrella-reachability errors.

## Native frontier and target

`exists_weilLogShiftRecoveryCoefficientColumn_growth` currently proves a common `K≥625` and, for `k≥K` and `k+2≤j≤n`,
`exp((j+1)*(n-j)) * |C(k,j)| ≤ |C(k,n)|`.
Here `C` is `weilLogShiftRecoveryCoefficientColumn`. Taking adjacent indices gives
`exp(n+1)*|C(k,n)| ≤ |C(k,n+1)|`.
The existing public lower-envelope theorem fixes `j=k+2`, retaining only a linear exponent. Multiplying the adjacent estimates retains all their growth.

Target stronger comparison, with the same native threshold and no analytic premise:
`exp((n*(n+1)-j*(j+1))/2) * |C(k,j)| ≤ |C(k,n)|`.
Consequently, for every sufficiently late fixed column there is `c>0` such that
`c*exp(n*(n+1)/2) ≤ |C(k,n)|` for every `n≥k+2`.
The coefficient sequence therefore escapes every exponential envelope. Every fixed moment-response column should likewise escape every exponential damping factor.

## Local corpus audit

- `research 'column quadratic growth' --any --mode lexical --module WeilLogShift --no-refresh --json`: fts5, 41 matches, 27 eligible, 18 modules. Main native hit is the existing column growth theorem; related hits concern subexponential domains and subdiagonal amplification.
- Read `WeilLogShiftLateColumnRunaway.lean:1–205`. The internal adjacent inequality is explicit in its proof. The exported comparison and lower-envelope theorem retain the coarser linear exponent.
- Exhaustive WeilLogShift source scan for quadratic and superexponential terminology found only unrelated quadratic prefactors in `WeilLogShiftSubdiagonalAmplification`; no quadratic-exponent column theorem.
- Native seed positivity is `weilLogShiftRecoveryCoefficientColumn_seed_pos`. Native moment-response factorization is `weilLogShiftRecoveryMomentResponse_eq_coefficientColumn`. Before implementation, inspect exact signatures and recheck the proposed new declaration names against the current corpus.

## Dependency-closed paper proof

1. Obtain the threshold `K` from the existing growth theorem. Its adjacent case yields `exp(m+1)|C(k,m)|≤|C(k,m+1)|` for every `m≥k+2`.
2. Fix `j≥k+2` and induct on `n≥j`. The base exponent is zero. The step uses
   `((n+1)*(n+2)-j*(j+1))/2 = (n+1)+(n*(n+1)-j*(j+1))/2`.
   Exponential addition and multiplication of nonnegative inequalities prove the exact triangular-sum exponent. No new estimate on the recovery weights is required.
3. Put `s=k+2` and `c=|C(k,s)|*exp(-s*(s+1)/2)>0`. The positivity is native seed positivity. The stronger comparison at `j=s` gives the quadratic lower envelope.
4. For arbitrary real `A`, eventually `n*(n+1)/2-A*n≥n` (take `n≥max(0,2*A+1)`). Hence `exp(-A*n)|C(k,n)|≥c*exp(n)` eventually, so the exponentially damped absolute coefficients tend to infinity. This is an elementary bound, not a numerical experiment or an asymptotic premise.
5. Existing paired-log-kernel lower bounds used in `WeilLogShiftLateColumnRunaway` give, for each fixed real shift `y`, constants `D>0` and `N` with kernel at least `D*exp(-(2*pi+1)*n)` eventually. The exact response is `(C(k,n)/sqrt(n))*pairedLogKernel(y,n)` for `n≥2`; the square-root normalization must be retained. Combining this factorization with step 3 and `sqrt(n)≤n+1` gives the lower envelope `(c*D/(n+1))*exp(n*(n+1)/2-(2*pi+1)*n)`. After extra damping `exp(-A*n)`, the remaining exponent is eventually at least `n`, so the damped response dominates `c*D*exp(n)/(n+1)`, which tends to infinity by the elementary exponential-over-linear argument already formalized in the current runaway proof. Hence every such signed damped response series is nonsummable.

All five paper steps now use checked local statements. `WeilLogShiftRecoveryColumns.lean:81` supplies the factorization including `sqrt(n)`; `WeilLogShiftLocalDecayThreshold.lean:77` supplies the eventual kernel lower bound; `WeilLogShiftLateColumnRunaway.lean:206–264` supplies the exponential-over-linear comparison pattern. Scratch Lean API checks remain before implementation. No early-column result is claimed: column zero remains outside this native tail threshold.

## Follow-up questions and status

- Does an upper bound match the leading quadratic exponent? No matching upper estimate has been audited; do not call `1/2` a sharp growth constant.
- Every finite natural factorial-power normalization still diverges: now formalized in `WeilLogShiftFactorialRegularization.lean`. A bridge to a library definition of real-order Gevrey classes remains unaudited.
- Does the late-column threshold extend to the first column? Current proof gives no such extension.

## Plan

Formalize the exact accumulated growth and positive quadratic envelope first. Then prove escape from all exponential envelopes and, after signature checks, the damped response and nonsummability consequences. Wire only new leaves, compile them sequentially, audit every public declaration in scratch Lean, refresh index, run lint, and clean owned scratch files.

## Current implementation log — 2026-10-09

- Fresh local lexical query `column growth exponential damping` (`--any`, `--module WeilLogShift`, `--no-refresh`) returned 91 matches, 46 eligible, 27 modules. Hits include the existing coarse column growth and subexponential-domain equivalences; no stronger quadratic-exponent column theorem was found.
- Reserved new leaf paths `WeilLogShiftQuadraticColumnGrowth.lean` and `WeilLogShiftSuperexponentialResponse.lean`; both were absent before implementation.
- Current native threshold and seed-positivity signatures rechecked directly. Scratch checks cover induction, exponential algebra, real cast limits, and the exact polynomial inequalities needed for damping.
- For responses, the denominator can be absorbed without a new asymptotic argument: local mathlib `Real.add_one_le_exp` gives `n+1≤exp(n)`. Arrange the remaining quadratic exponent to exceed `2*n`; then `(c/(n+1))*exp(2*n)≥c*exp(n)`. This retains the verified square-root normalization and avoids repeating the older exponential-over-linear limit proof.

### Verified first leaf

`WeilLogShiftQuadraticColumnGrowth.lean` compiled/exported cleanly. It proves exact accumulated quadratic-exponent comparison, the positive `c*exp(n*(n+1)/2)` lower envelope, and divergence to infinity after every fixed real exponential damping. Scratch API check also passed after using this toolchain's `Nat.cast_nonneg (α := ℝ)` parameter name.

`WeilLogShiftSuperexponentialResponse.lean` is compiling. It retains the `/sqrt(n)` factor, uses the eventual paired-kernel lower bound, and absorbs the remaining `n+1` denominator via `Real.add_one_le_exp`. Both leaves are wired into the umbrella; axiom audit, index, and lint follow final successful compilation.

## Final audit — 2026-10-09

Both new leaves compile and export cleanly with `lake --old env lean <leaf> -o <olean>`, sequentially and without full or umbrella builds. All six public theorems passed the exhaustive scratch `#print axioms` audit, using exactly `propext`, `Classical.choice`, and `Quot.sound`; no compiler warnings or errors. Both umbrella imports are unique. Index refresh succeeded, and every public theorem was checked against its module's index rows. No existing theorem API or resource limit changed.

Formalized outcomes:

- Exact accumulated quadratic-exponent comparison between every pair of indices after a sufficiently late seed.
- Positive coefficient envelope `c*exp(n*(n+1)/2)` and divergence after every fixed real exponential damping.
- Response envelope `(C/(n+1))*exp(n*(n+1)/2-(2*pi+1)*n)`, preserving the verified square-root normalization.
- Every fixed exponentially damped response magnitude tends to infinity at every real shift; every corresponding signed response series is nonsummable.

Latest formal lint exited 1 with only these 12 unrelated HTGeometry umbrella-reachability errors:

- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.HankelIncidenceRing
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperDeterminantUnitRigidity
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperQuadricLineObstruction
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperStableCoordinate.AmbientMaps
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperStableCoordinate.NonnegativeWeights
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperStableCoordinate.PicardUFD
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperStableCoordinate.PolynomialChartIntersection
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperStableCoordinate.ReesCoefficientKernel
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperStableCoordinate.SourceFiltrationProper
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperStableCoordinate.UnitCocycle
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperStableCoordinate.ZeroLocusInterface
- owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionTriangular

No finding concerns the new leaves. Early columns and matching upper growth estimates remain unresolved. The subsequent finite factorial-power regularization result is now formalized and audited in `docs/drafts/pipeline/3-formalized/weil-logshift-factorial-regularization.md`. Its next exposed task is amplitude rigidity when factorial order, exponential rate, and shift may all vary, recorded separately in `1-in-progress`.

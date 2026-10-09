# Canonical Gram coordinates and exact cost-gauge geometry

Status: FORMALIZED, 2026-10-09. Dependency-closed proof and native Lean verification complete for this increment.

## Formalization and verification

- `WeilLogShiftGramCoordinates.lean` constructs `FiniteWeilGramCoordinates` unconditionally from the existing ray dictionary. Canonical weights are positively homogeneous and componentwise subadditive; their addition defect is a nonnegative multiple of the positive relation. Equality holds exactly when both inputs omit a common dictionary test, with an explicit empty-dictionary exception.
- `WeilLogShiftGramNativeGauge.lean` defines the gauge using actual `finiteWeilGramTailCost 1`. It proves nonnegativity, vanishing exactly at the zero functional, positive homogeneity, the triangle inequality, and the same sharp equality criterion. The unconditional receiver is `exists_finiteWeilGram_native_gauge`; dictionary choice precedes all functional/scalar arguments.
- Promoted the existing weighted-cost equality argument to public `finiteWeilGram_weighted_cost_eq_iff` in `WeilLogShiftGramUniversalCostMinimum.lean`. Rebuilt that leaf and its existing `WeilLogShiftGramNativeCostMinimum.lean` dependent; both passed. Both new leaves also passed native compilation with empty diagnostic logs.
- `/tmp/hgt-weil-gram-gauge-final-audit.lean` passed: all 37 authored/affected public declarations, including the coordinate record, constructor, and projections, depend only on `propext`, `Classical.choice`, and `Quot.sound`. The seven newly used API terms were also checked in this toolchain.
- Source/olean freshness passed for all four affected leaves; both new imports are wired in `RHTower.lean`. Targeted `git diff --check` passed. `scripts/formal_tools.py index` passed; exact local lexical search finds the new unconditional receiver.
- `scripts/formal_tools.py lint` exited 1 with seven unrelated HTGeometry umbrella gaps: `PaperArithmeticFormalFlows`, `PaperFormalExponential`, `PaperFormalPolynomialLocus`, `PaperNativeDiagonalFormalFlows`, `PaperPrimeIndicatorFormalOrbit`, `PaperTerminatingCore`, and `QKrawtchoukCompanionTriangular`. No diagnostics for these four Gram leaves; no placeholder findings. The repository-wide lint gate is therefore not claimed clean.
- Evidence is local Lean corpus only: no web, external papers, or numerics. This proves an asymmetric gauge for a fixed minimal dictionary. Symmetry, a bundled norm, a global cutoff-cost upper bound, and exact single-test image surjectivity remain unproved here.

Logs: `/tmp/hgt-weil-gram-gauge-cost-helper-build.log`, `/tmp/hgt-weil-gram-gauge-native-cost-build.log`, `/tmp/hgt-weil-gram-coordinates-build.log`, `/tmp/hgt-weil-gram-native-gauge-build.log`, `/tmp/hgt-weil-gram-gauge-final-audit.log`, `/tmp/hgt-weil-gram-gauge-index.log`, `/tmp/hgt-weil-gram-gauge-lint.log`, `/tmp/hgt-weil-gram-gauge-search.json`.

## Target

Choose one minimal Gram dictionary and its canonical weights `Q(L)` for every
real linear functional `L`. Prove `Q(0)=0`, positive homogeneity, componentwise
subadditivity, and an exact addition defect in the positive balance direction.
For nonempty support, equality in subadditivity occurs exactly when both
canonical representations omit a common test. Empty dictionary is the explicit
exception: all coordinate vectors are empty and all equalities hold.

For the actual tail cost with normalization `B=1`, define
`G(L) = sum_w Q(L)_w * tailCost(1,w)`. Prove nonnegativity, definiteness
`G(L)=0 iff L=0`, positive homogeneity, triangle inequality, and the exact same
common-omitted-test criterion for triangle equality. This is an asymmetric
cost gauge; symmetry is not asserted.

## Proof argument before Lean

1. Package the already proved unconditional ray dictionary into coordinates
   chosen consistently for all `L`. Every feasible weight vector equals
   `Q(L)+t*a`, `t>=0`, with all coordinates of `a` positive. Thus `Q(L)` is
   componentwise least. Sparsity ensures a zero coordinate unless dictionary
   is empty. Any nonnegative boundary representation must equal `Q(L)`.
2. Zero weights represent the zero functional, proving `Q(0)=0` by leastness.
   For `r>=0`, `r*Q(L)` represents `r*L` and retains a zero coordinate.
   Boundary uniqueness proves positive homogeneity, including `r=0`.
3. `Q(L)+Q(M)` is a nonnegative representation of `L+M`. Leastness gives
   subadditivity; the ray theorem gives its exact defect `t*a`, `t>=0`.
   The sum is on the boundary iff both summands share a zero coordinate.
   This proves the sharp equality criterion, with the empty-dictionary case.
4. Every dictionary test has strictly positive native tail cost, by the
   existing minimal-certificate cost theorem. Weighted sums preserve the
   coordinate inequalities. Zero total cost forces all weights zero and then
   `L=0`. Under strictly positive weights, equality of costs and coordinate
   order forces equality of vectors, giving the triangle equality criterion.

## Implementation plan (completed)

Introduce a coordinate data structure with an unconditional, proved choice
constructor; do not leave a new model premise to users. Reuse the existing
weighted-cost equality lemma by exposing it. Add native gauge and unconditional
geometry receiver. Check prior corpus, APIs in `/tmp`, native leaves one at a
time, all public axioms, freshness, umbrella wiring, index, and formal lint.
No web, external papers, numerics, full builds, or umbrella builds.

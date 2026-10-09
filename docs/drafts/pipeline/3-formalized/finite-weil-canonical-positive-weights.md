# Canonical positive Gram weights and simultaneous cost minimization

Status: formalized; all five affected native leaves and all public axiom audits pass.
Global lint remains red on unrelated unreachable modules.

## Conjecture

For each finite coefficient support there is one minimal Gram dictionary such
that every linear functional has a unique componentwise least nonnegative
representation. For a nonempty dictionary, all other nonnegative
representations lie on one ray from that canonical weight vector. Consequently
the same vector minimizes every nonnegative linear cost on dictionary weights.
This concerns a fixed minimal dictionary; it does not optimize over different
Gram tests and does not give a quantitative cutoff-cost upper bound.

## Proof argument before Lean

1. A relation among a minimal dictionary which has a zero coefficient must be
   zero: erase that test, use the already proved bijective evaluation map, and
   interpolate each remaining coordinate separately.
2. Obtain a strictly positive relation `lambda` from the existing positive
   balance theorem. Given any relation `r`, subtract
   `(r_j / lambda_j) * lambda` to zero one coordinate. Step 1 forces the
   difference to vanish. Thus the entire relation space is one-dimensional.
3. Existing sparse positive representation supplies `q >= 0` with a zero
   coordinate because its support has at most `d` elements in a `d+1`
   dictionary. If `b >= 0` represents the same functional, Step 2 gives
   `b - q = t * lambda`. At a zero coordinate of `q`, positivity implies
   `t >= 0`. Conversely every such ray point is a nonnegative representation.
4. Therefore `q <= b` coordinatewise for every feasible `b`, making `q` the
   unique least feasible weight vector. Every nonnegative linear cost is
   minimized at `q`. If the cost evaluates strictly positively on `lambda`,
   the minimizer is unique. Empty support/dictionary is handled directly.

## Implementation and checks

Native-cost strengthening: for `B > 0`, zero actual Gram tail cost forces the
Gram form to vanish. Indeed, either the outer NNReal scale is zero, or the
nonnegative double sum is zero; its diagonal terms then force every point
weight to be zero. A zero form cannot belong to a nonempty-support minimal
certificate: deleting it preserves the certificate and contradicts the proved
cardinality lower bound. Thus every test in such a minimal dictionary has
strictly positive native tail cost. This discharges the strict-cost condition
and yields the same unique minimizer for every positive tail-cost normalization.

Expose the existing full positive balance/span and finite erased-sum helpers
for reuse; do not duplicate their proofs. Add relation-space and canonical
weight leaves. Verify APIs in `/tmp`, compile one owned Lean process at a time,
audit all public declarations, wire imports, check freshness, index, and lint.
Only local Lean corpus and installed Lean/mathlib may be mathematical sources.
No web, external papers, or numerical experiments.


## Final result and verification — 2026-10-09

The full feasible-weight geometry is formalized: each minimal dictionary has
one strictly positive relation direction. For every target functional, all
nonnegative representations are exactly `q + t*a`, `t >= 0`, where `q` is sparse
and is the unique componentwise least feasible weight vector. The dictionary
and its direction are chosen before the functional. The same `q` minimizes
every nonnegative linear dictionary cost, and strictly positive costs have
`q` as their unique minimizer.

For the actual tail cost, the strict positivity premise is discharged:
zero cost with `B > 0` forces a zero Gram form, and deleting such a test would
contradict minimal cardinality on nonempty support. Thus `q`, chosen before
`B`, uniquely minimizes the weighted native tail cost for every `B > 0`.
Empty support/dictionary is handled explicitly throughout.

Affected modules:
- `WeilLogShiftGramPositiveDictionary.lean`: exposed the existing erased-sum
  and full positive-balance/span helpers; updated every reference, with no
  duplicated proof.
- `WeilLogShiftGramRelations.lean`: zero-coordinate rigidity, the single
  positive relation direction, and exact positive representation rays.
- `WeilLogShiftGramCanonicalDictionary.lean`: unconditional ray dictionary
  and unique least feasible weights.
- `WeilLogShiftGramUniversalCostMinimum.lean`: simultaneous minimization for
  nonnegative costs and uniqueness for strictly positive costs.
- `WeilLogShiftGramNativeCostMinimum.lean`: zero-cost rigidity, strict native
  cost positivity in minimal certificates, and the native minimizer receiver.

All five final native builds exited 0 with empty logs. The deprecated
`push_neg` spelling was replaced with `push Not`, then affected dependencies
were rebuilt. Source/artifact freshness and all direct dependencies passed;
every affected umbrella import occurs exactly once.

The final `/tmp/hgt-weil-gram-canonical-final-audit.lean` exited 0. It checks
14 mathlib API terms, an erased-sum caller with its own equality instance, and
all 14 public declarations across the five affected leaves. All declarations
use only `propext`, `Classical.choice`, `Quot.sound`. Public audit coverage was
compared against the declarations in the actual source files.

`index` exited 0, and an exact local search confirms
`exists_finiteWeilGram_native_cost_minimizer` is indexed at its source.
`lint` exited 1 with eight unreachable modules outside this branch:
RHTower.ModularLambdaCellEnergyBound, RHTower.ModularLambdaOrbitSeparation,
HTGeometry.PaperPrimePolynomialActions, HTGeometry.PaperPrimePolynomialAlgebra,
HTGeometry.PaperPrimePolynomialClocks, HTGeometry.PaperPrimePolynomialDenominators,
HTGeometry.PaperPrimePolynomialExtensionBoundary, and
HTGeometry.QKrawtchoukCompanionTriangular. No branch or forbidden-placeholder
error was reported. These shared worktree failures were left untouched.

Logs: `/tmp/hgt-weil-gram-dictionary-promoted-build.log`,
`/tmp/hgt-weil-gram-relations-build.log`,
`/tmp/hgt-weil-gram-canonical-dictionary-build.log`,
`/tmp/hgt-weil-gram-universal-cost-build.log`,
`/tmp/hgt-weil-gram-native-cost-build.log`,
`/tmp/hgt-weil-gram-canonical-final-audit.log`,
`/tmp/hgt-weil-gram-canonical-index.log`,
`/tmp/hgt-weil-gram-canonical-index-verification.json`, and
`/tmp/hgt-weil-gram-canonical-lint.log`.

Limits: all optimization is within the fixed minimal dictionary. This does
not optimize the choice of Gram tests, prove a cutoff total-cost upper bound,
or establish single-test surjectivity. A further candidate is to classify
arbitrary signed costs by their aggregate slope on the positive relation;
that separate receiver has not been packaged in Lean. The overall corpus
research goal remains active. No web, external papers, or numerical
experiments were used.

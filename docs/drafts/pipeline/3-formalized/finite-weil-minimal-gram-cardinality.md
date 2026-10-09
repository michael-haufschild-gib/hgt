# Minimal number of finite Gram certificate tests

Status: formalized; all four native leaf builds and public-declaration axiom audits pass.
Sources: local Lean corpus and installed Lean dependencies only. No web, papers, or numerics.

## Conjecture and motivation

For every nonempty finite coefficient support s, normalized finite Gram certificates exist with exactly s.card+1 tests, and no certificate has fewer tests. This is compatible with the proved exponential total-cost lower bound: the number of tests and their weighted cost are different quantities. A quantitative upper bound on total cost remains open.

## Proposed dependency-closed argument

1. Represent each actual Gram test by its coefficient vector V(w), so its form on c is the finite pairing V(w) dot c.
2. The closure of the range of V contains zero, is stable under nonnegative scaling, and is closed under addition. For addition, absorb NNReal scales into the real weights by square roots and separate two finite point packets by a translation tending to infinity. Mixed Gram entries tend to zero because every actual paired logarithmic kernel does. The diagonal blocks retain the two original vectors.
3. This closure is therefore a closed convex cone. If proper, separation gives a nonzero real linear functional nonnegative on it. Expressing that functional in coefficient coordinates yields a nonzero c with every actual Gram form nonnegative, contradicting the existing unconditional normalized-certificate theorem. Thus the single-test coefficient image is dense in the entire finite coefficient space.
4. Approximate the d+1 vertices of a sufficiently enlarged coordinate simplex by actual Gram vectors, with fixed small coordinate error. The simplex has a uniform negative margin on every nonzero coefficient direction; the approximation preserves a margin stronger than the required norm. This gives a certificate with at most d+1 tests.
5. Any certificate's evaluation map into its m test values is injective, hence d<=m. If m=d, that map is surjective and some nonzero c maps to the all-ones vector, contradicting the required negative witness. Therefore d+1<=m for d>0, making the constructed upper bound exact. The empty support admits the empty certificate.

For step 4 take A=2(d+1)^2, target vectors A*e_i and -A*1, and approximate each in supremum norm by less than 1. Pairing error is at most d*norm(c). If no actual test is below -norm(c), every A*c_i is at least -(d+1)*norm(c), and A*sum(c_i) is at most (d+1)*norm(c). Omitting one coordinate gives A*c_i<=d(d+1)*norm(c). These two inequalities force A*norm(c)<=d(d+1)*norm(c), impossible for nonzero c. Thus the finite image of these d+1 tests is a normalized certificate.

The required analytic input already exists as `tendsto_pairedLogKernel_cocompact` in `WeilLogShiftVanishingNormalization.lean`. The construction needs no new kernel-decay premise. Local separation and dimension interfaces have been inspected in scratch Lean.

## Audit obligations

- Prove decay of the actual paired kernels from existing corpus envelopes; introduce no analytic premise.
- Build the separated finite Gram packets as actual `FiniteWeilGramTest` values, with all cross terms accounted for.
- Verify the precise local separation and finite-dimensional APIs before use.
- Formalize the positive density statement as well as the exact cardinality classification.
- Preserve all previous cost results, native receivers, and HasSum statements. Leave concurrent unrelated work unchanged.

## Checkpoint

- `WeilLogShiftGramImage.lean` compiles: exact coefficient pairing, finite reindexing, positive rescaling, and the separated-sum limit for actual Gram tests.
- Lower cardinality, image density, and simplex construction are written in separate leaves and undergoing native verification in sequence.
- Prepared `/tmp/hgt-weil-gram-cardinality-final-audit.lean` for all thirteen public declarations (including definitions), the two actual corpus inputs, and twenty-nine API term checks.
- Local API lessons: `Equiv.sum_comp` needs explicit functions here; `Real.sq_sqrt` rewrites with `erw` followed by `rfl` across equivalent real instances; simplify `Function.comp_apply` in composed limits; use canonical `tendsto_finsetSum`.


## Final verification — 2026-10-09

The exact minimum is proved by `exists_finiteWeilGram_minimal_card_certificate`:
zero tests for empty support; exactly `s.card + 1` tests for nonempty support.
Every other normalized finite Gram certificate has at least this cardinality.
The positive geometric theorem `denseRange_finiteWeilGramCoefficientVector`
proves that actual single-test Gram coefficient vectors are dense in the full
finite coefficient space. The separated-packet construction accounts for all
mixed Gram terms; their vanishing follows from the corpus kernel-decay theorem.

Implementation and verification:
- `WeilLogShiftGramImage.lean`: coefficient vectors, finite reindexing, scaling,
  and separated-packet limit; native compilation passed with empty log.
- `WeilLogShiftGramImageDensity.lean`: closed-cone separation and the existing
  unconditional certificate theorem prove density; native compilation passed
  with empty log.
- `WeilLogShiftGramCardinalityLower.lean`: injectivity plus the equal-dimension
  surjectivity obstruction proves the lower bound; native compilation passed
  with empty log.
- `WeilLogShiftGramMinimalCardinality.lean`: enlarged coordinate-simplex
  approximation proves the upper bound and exact minimum; native compilation
  passed with empty log.
- All four imports are wired into `GaloisForLFunctions/RHTower.lean`.
- All 13 public declarations, plus the two source theorems, passed the final
  `/tmp` axiom audit with only `propext`, `Classical.choice`, `Quot.sound`.
- The final audit also verifies 30 mathlib API terms in this toolchain.
- Source/artifact freshness and every direct import of the four leaves passed.
- `scripts/formal_tools.py index` exited 0.
- `scripts/formal_tools.py lint` exited 1: 7,656 unreachable-module errors
  outside these four leaves (7,648 RHTower; 8 HTGeometry). No current-branch
  error and no placeholder/axiom declaration error was reported. These shared
  worktree integration failures were not changed.

Logs: `/tmp/hgt-weil-gram-image-build.log`,
`/tmp/hgt-weil-gram-density-build.log`,
`/tmp/hgt-weil-gram-cardinality-lower-build.log`,
`/tmp/hgt-weil-gram-cardinality-build.log`,
`/tmp/hgt-weil-gram-cardinality-final-audit.log`,
`/tmp/hgt-weil-gram-cardinality-index.log`, and
`/tmp/hgt-weil-gram-cardinality-lint.log`.

Limits: this is an exact test-count classification, not a bound on the number
of points inside each test or on total weighted Gram cost. The previously
proved exponential lower bound for total weighted cost remains intact. A
matching total-cost upper bound remains open. No external paper, web search,
or numerical experiment was used. The overall corpus research goal remains
active; this card records one completed increment.

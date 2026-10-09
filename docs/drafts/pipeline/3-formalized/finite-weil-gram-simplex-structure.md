# Exact simplex structure of minimal finite Gram certificates

Status: formalized; native leaves, caller check, and public axiom audit pass.

## Conjecture and mathematical target

For a support with `d` coefficients, a normalized certificate with `d+1`
tests is a positive simplex: erasing any test leaves an invertible evaluation
map; there is a strictly positive dependence among all tests; every real
coefficient functional is an exact nonnegative combination of at most `d`
tests from this fixed dictionary. Existence of a minimal certificate is already
unconditional in `WeilLogShiftGramMinimalCardinality.lean`.

This is an exact finite-dictionary representation result. Exact realization by
one Gram test remains a separate conjecture: the proved single-test density
does not imply surjectivity. No obstruction or no-go for that conjecture is
claimed. Total weighted cost upper bounds also remain open.

## Dependency-closed argument before Lean

1. Fix a minimal certificate and a distinguished test `w0`. If a coefficient
   vector vanishes under every other test, the strict certificate inequality
   for `c` and `-c` forces opposite strict signs at `w0`, a contradiction.
   Thus evaluation at the remaining `d` tests is injective. Equal finite
   dimensions make it bijective.
2. Invert that evaluation map on each coordinate vector. Each resulting
   coefficient vector has evaluations zero or one on the retained tests, so
   the omitted test must evaluate strictly negatively. Write those negatives
   as `-lambda_j`, with every `lambda_j > 0`. Linear decomposition gives
   `V(w0) + sum_j lambda_j V(j) = 0`.
3. Every target functional has unique signed coordinates in the retained
   basis. Add a sufficiently large multiple of the positive dependence to
   make every coefficient nonnegative. Choose the smallest such multiple:
   at least one resulting coefficient is zero, so at most `d` tests are used.
4. Apply this classification to the existing unconditional minimal certificate.
   Empty support has the empty representation; the nonempty case has exactly
   `d+1` dictionary tests and the basis/dependence properties above.

## Verification obligations

- Search only the local Lean corpus and installed mathlib.
- Compile native leaves, one owned Lean process at a time, no umbrella build.
- Verify all new mathlib API names in `/tmp` against this toolchain.
- Audit every public declaration with `#print axioms` in `/tmp`.
- Wire leaves, check source/artifact freshness, refresh index, run formal lint.
- Keep shared worktree failures outside this branch untouched.


## Verified result — 2026-10-09

`WeilLogShiftGramSimplexBasis.lean` proves that erasing any one test from a
certificate of cardinality `d+1` gives a bijective evaluation map. It constructs
coefficient coordinates and a strictly positive dependence with the omitted
test normalized to weight one. The erasure API accepts the caller's
`DecidableEq` instance; a separate `/tmp` client example verifies this.

`WeilLogShiftGramPositiveDictionary.lean` proves the exact representation:
one fixed minimal dictionary works for every real linear functional on the
coefficient space, with nonnegative weights and at most `s.card` nonzero terms.
The dictionary is chosen before the target functional. The empty support is
handled explicitly. The same leaf packages the unconditional existence of
the simplex certificate with the basis and positive-balance properties.

Verification:
- Both final native leaf builds exited 0 with empty logs.
- Both umbrella imports occur exactly once.
- Source/artifact freshness and all direct dependencies passed.
- `/tmp/hgt-weil-gram-simplex-final-audit.lean` exited 0: a caller with its own
  equality instance, 25 mathlib API terms, and every one of the seven public
  declarations were verified. All seven declarations and the source minimal
  cardinality theorem use only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py index` exited 0. An exact local search confirms
  `exists_finiteWeilGram_positive_dictionary` is indexed at its actual source.
- Global formal lint exited 1 with four unreachable-module errors outside
  these two leaves. There were no current-branch errors and no forbidden
  placeholder/axiom declaration errors. The global integration gate remains
  red; this card records verified local mathematical results.

Logs: `/tmp/hgt-weil-gram-simplex-basis-build.log`,
`/tmp/hgt-weil-gram-positive-dictionary-build.log`,
`/tmp/hgt-weil-gram-simplex-final-audit.log`,
`/tmp/hgt-weil-gram-simplex-index.log`,
`/tmp/hgt-weil-gram-simplex-index-verification.json`, and
`/tmp/hgt-weil-gram-simplex-lint.log`.

Remaining questions: exact realization by one test is still open; no inference
of surjectivity from density was made. No quantitative total-cost upper bound
was proved. A direct receiver phrased as a sum of at most `d` actual scaled
Gram tests can be derived from the dictionary by absorbing its nonnegative
weights into each test's NNReal scale and reindexing the finite support; that
native-sum interface has not yet been formalized. No web, papers, or numerical
experiments were used. The overall corpus research goal remains active.

# Exact simplex structure of minimal finite Gram certificates

Status: dependency-closed argument; Lean implementation pending.

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

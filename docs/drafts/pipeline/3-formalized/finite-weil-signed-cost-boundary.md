# Exact signed-cost boundary for a minimal Gram dictionary

Status: formalized; native compilation, axiom audit, freshness, wiring, and index pass.
Global lint remains red on six unrelated HTGeometry modules.

## Target

Replace coordinatewise nonnegative cost assumptions by the exact scalar
invariant `S = sum_w a_w * kappa_w`, where `a` is the positive relation of a
fixed minimal dictionary. For each target functional let `q` be its canonical
weights and `C = sum_w q_w * kappa_w`.

Prove unconditionally that every real signed cost has precisely this range:
- `S > 0`: all values in `[C, infinity)`; `q` is the unique minimizer.
- `S = 0`: the singleton `{C}`; all feasible weights have the same cost.
- `S < 0`: all values in `(-infinity, C]`; `q` is the unique maximizer and
  cost is unbounded below.

Also prove the exact budget receiver: a feasible representation of cost at
most `R` exists iff `S < 0` or `C <= R`. Boundedness below is equivalent to
`S >= 0`. Empty support must be included without extra mathematical premises.

## Proof argument before Lean

The corpus already proves that all feasible weights are exactly `q + t*a`
for `t >= 0`. Their cost is exactly `C + t*S`, by finite-sum distributivity.
For positive or negative `S`, any value on the corresponding closed half-line
is attained by `t = (R-C)/S`; the sign assumptions ensure `t >= 0`. For zero
`S`, only `C` occurs. At nonzero slope, cost `C` forces `t=0`, hence weights
`q`, proving both endpoint uniqueness statements.

For a negative slope, the value `min C R` is attainable, so every upper budget
is feasible. Otherwise all attainable values are at least `C`, and `q`
attains it. Any putative lower bound under negative slope is contradicted by
applying the budget receiver to that bound minus one.

This is a sharp classification with positive survivors, not merely a negative
result for some signed costs. It concerns weights in one fixed dictionary;
choice of dictionary and quantitative cutoff-cost upper bounds remain open.

## Verification

Use only local Lean and installed Lean/mathlib. Verify new API names in `/tmp`;
compile one owned Lean process at a time; audit all public declarations;
wire imports, verify freshness, refresh index, and run formal lint. No web,
external papers, numerical experiments, full builds, or umbrella builds.


## Verified result — 2026-10-09

`WeilLogShiftGramSignedCostBoundary.lean:41` contains the unconditional theorem
`exists_finiteWeilGram_signed_cost_dictionary`. The minimal dictionary and its
positive relation are chosen before the target functional; the canonical
weights are chosen before the arbitrary signed cost. The result includes:

1. Exact attainable-cost trichotomy: `[C, infinity)` for positive slope,
   `{C}` for zero slope, and `(-infinity, C]` for negative slope.
2. Exact upper-budget feasibility: `S < 0 or C <= R`.
3. Boundedness below iff `0 <= S`.
4. At every nonzero slope, a feasible vector has cost `C` iff it equals the
   canonical vector. Thus the positive-slope minimum and negative-slope
   maximum are both unique.

Empty support is covered through the existing unconditional ray dictionary.
No sign condition is imposed on individual cost coordinates. The negative
branch includes its exact positive survivor: all attainable costs, a unique
maximum, and the full budget classification.

Verification:
- The native leaf build exited 0 with an empty log, on its first attempt.
- Every direct import and source/artifact freshness passed.
- Its umbrella import is present exactly once.
- `/tmp/hgt-weil-gram-signed-cost-final-audit.lean` exited 0, verifying eight
  mathlib API terms and auditing the sole new public theorem plus its source
  ray theorem. Both use only `propext`, `Classical.choice`, `Quot.sound`.
- `index` exited 0; an exact local query confirms the new theorem is indexed
  at its actual source.
- Global `lint` exited 1 with six unreachable HTGeometry modules:
  PaperPrimePolynomialActions, PaperPrimePolynomialAlgebra,
  PaperPrimePolynomialClocks, PaperPrimePolynomialDenominators,
  PaperPrimePolynomialExtensionBoundary, QKrawtchoukCompanionTriangular.
  No current-branch or forbidden-placeholder error was reported.

Logs: `/tmp/hgt-weil-gram-signed-cost-api.log`,
`/tmp/hgt-weil-gram-signed-cost-build.log`,
`/tmp/hgt-weil-gram-signed-cost-final-audit.log`,
`/tmp/hgt-weil-gram-signed-cost-index.log`,
`/tmp/hgt-weil-gram-signed-cost-index-verification.json`, and
`/tmp/hgt-weil-gram-signed-cost-lint.log`.

This completes the signed-cost receiver proposed by the canonical-weight
increment. It does not optimize dictionary choice or provide a quantitative
cutoff-cost upper bound. Single-test surjectivity remains open. The overall
corpus research goal remains active. Only local Lean and installed mathlib
were used; no web, external papers, or numerical experiments.

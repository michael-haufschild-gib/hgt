# Quantitative stability of optimal Gram reversal

Status: FORMALIZED, 2026-10-09. Exact defect and both quantitative implications proved.

## Formalization and verification

`WeilLogShiftGramReversalStability.lean` proves `atomReversalRatio_gap_mul`,
`atom_cost_spread_of_nativeGauge_bound`, and `nativeGauge_bound_of_atom_cost_spread`.
The reusable cardinality helper `tests_card_of_atom` is public. The unconditional
receiver is `exists_finiteWeilGram_reversal_stability`: a dictionary exists for
every support, chosen before all tolerances and functionals.

- Native `lake --old env lean <leaf> -o <leaf.olean>` passed with an empty final
  diagnostic log. The first pass found one addition-order mismatch in the
  converse proof; a direct `linarith only [hsum]` step fixed it.
- `/tmp/hgt-weil-gram-stability-final-audit.lean` passed: six finite-sum/API terms
  verified in this toolchain and all five public declarations audited with
  `#print axioms`. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
  Source-to-audit coverage was checked for every public declaration.
- Source/olean freshness, the single umbrella import, targeted diff check,
  index refresh, and exact indexed receiver search passed.
- Global lint exited 1 with six unrelated HTGeometry umbrella gaps:
  `GaussianLightConeAmplification`, `PaperMoebiusPrimeFlow`,
  `PaperPrimeFlowCoefficients`, `PaperPrimeTerminatingSlice`,
  `PaperPrimeTerminatingSupport`, and `QKrawtchoukCompanionTriangular`.
  No stability-leaf diagnostics or placeholder findings. Global lint is not clean.

Logs: `/tmp/hgt-weil-gram-reversal-stability-build.log`,
`/tmp/hgt-weil-gram-stability-final-audit.log`,
`/tmp/hgt-weil-gram-stability-index.log`, `/tmp/hgt-weil-gram-stability-lint.log`,
`/tmp/hgt-weil-gram-stability-search.json`.

## Next conjecture

The current definitions allow repeated nodes and signed real amplitudes.
Duplicate-node signed splitting may preserve every Gram functional while
increasing actual tail cost by an arbitrary factor at least one. That could
construct balanced actual dictionaries and discharge their existence premise.
This is not proved here. Its separate card is
`../1-in-progress/finite-weil-cost-inflation-and-balanced-dictionaries.md`.

## Target

For the existing unconditional canonical dictionary D, let d=|s|,
p_w=D.balance(w)*finiteWeilGramTailCost(1,w), S=sum p, and G be its
native cost gauge. Local Lean corpus only; no web, papers, or numerics.

1. Exact defect identity for every atom w:
   (R_w-d)*p_w = sum_v (p_v-p_w), where R_w=S/p_w-1.
   For a minimizing atom, every summand is nonnegative.
2. If G(-L)<=(d+epsilon)G(L) for every L, epsilon>=0, then
   p_u<=(1+epsilon)*p_v for every pair of atoms u,v.
3. Conversely, pairwise spread at most 1+epsilon implies
   G(-L)<=d*(1+epsilon)*G(L) for every L.

The empty dictionary must remain valid in both implications. The result
quantifies the previous exact equality criterion; it does not assert
existence of an actual dictionary with a prescribed spread.

## Dependency-closed proof before Lean

Any atom forces the support nonempty, so the dictionary has d+1 members.
Expand R_w=S/p_w-1 and sum the constant p_w over d+1 atoms to obtain (1).
The actual costs and balance are strictly positive, so p_w>0.

Choose a minimizing atom w using the proved optimal-reversal witness.
The hypothesized uniform bound gives R_w<=d+epsilon. Every nonnegative
summand p_u-p_w is at most their sum, which by (1) is at most
epsilon*p_w. Hence p_u<=(1+epsilon)*p_w<=(1+epsilon)*p_v, proving (2).
If the dictionary is empty, there is no pair to check.

For (3), fix any atom w. Remove it from the finite sum S. Exactly d
terms remain, each at most (1+epsilon)*p_w. Thus
S<=p_w+d*(1+epsilon)*p_w. The established sharp finite reversal criterion
gives the claimed uniform bound. In the empty case its atomic criterion
is vacuous. No estimate is obtained by sampling atoms.

## Work plan (completed)

- Verify finite-sum APIs in the installed Lean toolchain.
- Formalize the exact defect and both quantitative implications.
- Package an unconditional receiver with dictionary choice before epsilon.
- Native leaf build, all-public axiom audit, umbrella/freshness checks,
  local index refresh, and formal lint.

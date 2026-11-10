# Greedy carry-free compositions are uniquely optimal

- **Stage:** 3-formalized
- **Owner:** `SignFreePurityMechanisms/CarlitzGoss/`
- **Target:** Combinatorial part of A84; the actual Carlitz–Goss Newton polygon remains separate.

## Theorem

For every integer base `p≥2`, residue degree `s>0`, finite collection of
base-`p` digit occurrences, and number of parts, an admissible composition
is greedy exactly when it maximizes the weighted sum of its parts.
Admissible means every part is positive, every proper part is divisible by
`p^s−1`, and the parts partition the digit occurrences without carrying.
All maximizing compositions have the same numerical part values.

## Proof

A hypothetical nongreedy optimum reduces to an increasing composition
whose last part is a singleton `X=p^e`. The common zeroth inverse content
of its proper parts is one. A competing greedy last part contains a larger
power and has cyclic weight `p^(e mod s)`.

The inverse-prefix carry recursion constructs an actual increasing
composition `Z`. Outside a residue interval its prefixes are unchanged.
Inside the interval, positive prefix counts grow by at least `p−1`;
terminal counts below the singleton residue lose at least `p−1` digits.

Put `q=p^s`, let `P` be the largest digit in `Z`'s last part, and let `V`
sum the largest retained terminal powers in the lower affected residues.
Then `pX≤P` and `q(p−1)V≤pP`. The double-geometric prefix estimate and
exact prefix-weight identity give

`(q−1)²(wt Z−wt O) ≥ (q−1)²(P−X)−(p−1)q(X+V)`.

The right side is positive because `q≥p²≥4` and
`(p−1)(q²−3q+1)>p²`. This contradicts optimality. The one-residue and
short-composition cases are included in the counterexample reduction.
Existence of both finite maxima then gives equivalence and uniqueness.

## Lean declarations and audit

In `CarryWeightComparison.lean`:

- `DigitComposition.exists_strict_weight_improvement`

In `GreedyOptimality.lean`:

- `DigitComposition.optimal_values_eq_greedy`
- `DigitComposition.isOptimal_iff_isGreedy`
- `DigitComposition.IsOptimal.values_eq`
- `DigitComposition.IsGreedy.isOptimal`

Both files passed direct `lake --old env lean` checks. The strict improvement,
equivalence, and uniqueness endpoints depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The programme umbrella imports both files.

## Prefix-cost consequence

Put `v(C)=mN−wt(C)` and let `P(C)` be the proper-prefix value. The greedy
weight bound on its divisible initial composition gives `v(C)<2P(C)`.
For consecutive greedy compositions `C,D` on the same digits, merge the
last two parts of `D`. Comparing its last part with `C` and using the
half-total bound inside `D` gives `2P(C)<P(D)`. Optimality against the
same merge gives `v(D)−v(C)≥P(D)`. Thus `v(D)>2v(C)`, and nonnegative
costs imply strictly increasing successive slopes. When `N` is divisible,
the half-total bound additionally gives `v(C)<N`.

`PrefixCostGrowth.lean` proves `IsGreedy.twice_prefixCost_lt`,
`IsGreedy.prefixCost_strictConvex`, and `IsGreedy.prefixCost_lt_total` in
the `DigitComposition` namespace. The direct check and all three transitive
axiom audits pass with the same three standard axioms. The umbrella imports it.

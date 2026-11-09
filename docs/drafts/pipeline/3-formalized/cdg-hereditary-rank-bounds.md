# Hereditary half-rank bounds for prime-logarithm forms

- **ID:** CDG-HERED
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Below one explicit floor, every coordinate intersection of
  the small-form span has dimension at most half its coordinate support.

## Theorem

For `k≥1` distinct primes, `H≥1`, put
`W=ceil(Σ log p_j)+1`, `U=10⁴(W+1)(k+1)²`, `C=U^(100(k+1))`,
`H′=k!H^k`, `K=k!H^(k−1)`, and

`ε=exp(−C(log(k!H′^k)+2))/(k·k!H′^(k−1)K)`.

Let `S` be any finite family of integer coefficient rows of height at most
`H`, all with prime-logarithm forms of absolute value below `ε`.
For every coordinate set `J`,

`2 dim_ℚ(span_ℚ(S)∩ℚ^J) ≤ |J|`.

In particular, this holds for the span of the entire height-`H` integer
approximation body. The threshold is uniform in `J` and `S`.

## Proof [PROVED HERE]

Write `l=|J|` and `r=dim(span(S)∩ℚ^J)`. Bounded coordinate elimination
gives `r` independent integer rows supported on `J`, with height at most
`H′` and values below `Kε`. Restriction to `J` preserves independence,
so `r≤l`. If `2r>l`, then `r≥1` and `l−r<r`. Hence the collective root
degree for these restricted forms is exactly one.

The restricted logarithmic mass is at most `W`. Its common base is at most
`U`, and its exponent is at most `C`, because `l≤k`. Also
`r!H′^r≤k!H′^k` and `r·r!H′^(r−1)≤k·k!H′^(k−1)`.
The simultaneous logarithm theorem therefore forces some restricted form
to have absolute value at least

`exp(−C(log(k!H′^k)+2))/(k·k!H′^(k−1)) = Kε`,

contradicting strict smallness. Thus `2r≤l`.

## Contribution and boundary

The total rank bound alone permits all exceptional directions to concentrate
on heavily weighted coordinates. This hereditary bound rules out every
coordinate concentration of density above one half, while retaining linear
dimension degree in the collective exponent. Weighted coordinate selection
is proved in [CDG-WEIGHT](cdg-weighted-coordinate-separation.md).
The dimension-degree comparison concerns the earlier formal scalar bound;
it is not a claim of improvement over published scalar estimates.

## Dependencies and formalization

- [CDG-ELIM](cdg-bounded-coordinate-elimination.md): exact
  coordinate intersection with controlled integer height and value.
- [CDG-EXP](cdg-rank-sensitive-exponent.md): simultaneous
  lower bound and exact root-degree-one regime.
- `CollectiveDiophantineGeometry/HereditaryRankBounds.lean`: formalization.

`hereditary_small_forms_finrank_le` proves the finite-family theorem;
`nearRelationBox_hereditary_finrank_le` applies it to the entire integer
approximation body. The direct `lake --old env lean` source check passed.
Both transitive axiom audits contain only `propext`, `Classical.choice`
and `Quot.sound`. The programme umbrella imports the module.

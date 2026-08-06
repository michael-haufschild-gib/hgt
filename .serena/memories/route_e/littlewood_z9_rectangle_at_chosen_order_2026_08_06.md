# Z9 — the rectangle bound at `K = littlewoodOrder t`

`RHTower/Sieve/DirichletSigmaCapstone.lean`. All `[propext, Classical.choice, Quot.sound]`.

## The point

The rectangle (`Re s = sigma`) estimate needs **no separate structural theory**. `splitExponent` and
`topExponent` are the same functions of `t` off the line (see
`mem:route_e/littlewood_z6_sigma_parameter_selection_2026_08_06`), so the line case's discharges
transfer. Only one gap: off the line the split point must be `>= 2`, not `>= 1`.

`two_le_splitExponent` closes it for `K >= 3`: the largeness condition
`(K-1)(K-4/3)log(K-1) + K log 2 <= log(t/2pi)` already implies `1 < x` for the balance point `x`,
because `(K-1) log(K-1) > log 2` when `K-1 >= 2`. Then `ceil x >= 2`.

## Statements

```
norm_dirichlet_sigma_littlewood_capstone   -- general K >= 3
norm_dirichlet_sigma_littlewood_order      -- K = littlewoodOrder t, needs orderThreshold 3 <= L
```

Both conclude
`||sum_{n < 2^(topExponent t + 1)} n^(-sigma-it)|| <= 2 + 2^theta * S * log 2 + R * 2560 * 2^(-theta)`
uniformly for `1 - 1/(6*2^K) <= sigma < 1`.

`orderThreshold_littlewoodOrder_le_of` generalises the Z7 admissibility lemma to an arbitrary witness
order `K0 >= 2` (Z7's version hard-coded `2`); needed to feed `orderThreshold 3 <= L`.

## Width and size

`2^(littlewoodOrder t) <= log(t/2pi)` (Z7) and `log(t/2pi) < 69122*2^(3 littlewoodOrder t)` (Z8), so
the strip width `1/(6*2^(littlewoodOrder t))` is **`≍ 1/log t`** — the classical zero-free region
width.

On that strip `theta = S/(6*2^K) -> 0`, head `~ L/K`, tail `O(L/sqrt K)` (the sigma target's exponent
is half the line's, so the square root). Both `o(log t)`; in particular `O(log t)` uniformly on the
rectangle, which is the Landau / 3-4-1 input.

## Remaining for the zero-free region

Only interface matching: feed this plus the `riemannZeta` tail (`ZetaPartialSumTruncation`, as Z4 did
on the line) into `PNTPlus/ZetaBounds` (read-only vendored). No new analysis.

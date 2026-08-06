# Littlewood's `O(log t / log log t)` is proved in the corpus

`RHTower/Sieve/DirichletOrderChoice.lean` + `RHTower/Sieve/DirichletOrderRate.lean`.
All declarations audit to `[propext, Classical.choice, Quot.sound]`.

```
norm_dirichlet_partial_littlewood_rate :
  16*pi <= t  ->  orderThreshold 2 <= log (t/2pi)  ->  4/3 < orderLowerBound (log (t/2pi))  ->
  ||sum_{n in Ico 1 (2^(topExponent t + 1))} n^(-1-it)||
    <= 1 + log 2 + 2 * log (t/2pi) / (orderLowerBound (log (t/2pi)) - 4/3)

orderLowerBound L := log (L / 69122) / (3 * log 2)
```

`orderLowerBound L ~ (1/3) log_2 L`, so the error term is `O(L / log L) = O(log t / log log t)`.

## The two ideas

**1. The order is a `findGreatest`, and the cap is free.**
`littlewoodOrder t := Nat.findGreatest (fun K => orderThreshold K <= log (t/2pi)) (ceil (log (t/2pi)))`
with `orderThreshold K := max (largenessBound K) (balanceBound K) + 1`.
The cap does not truncate because **an order never exceeds its own threshold**:
`balanceBound K >= 3*2^K*(2/3)*1 = 2*2^K` (the log inside `balanceBound` is `>= 1` since
`7680(K-4/3)/log 2 >= 5120 > e`), and `K < 2^K`. So every admissible `K` satisfies `K <= log(t/2pi)`.
The *same* fact supplies the cap check `K+1 <= ceil L` needed by `Nat.findGreatest_is_greatest`.

**2. Maximality + a crude envelope inverts to a lower bound on `K`.**
`orderThreshold M <= 34561 M^2 2^M` for `M >= 2`, proved from `log x <= x - 1` and
`log 2 > 2/3` (`Real.log_two_gt_d9`) — **no numerical evaluation of any logarithm**.
Then `L < orderThreshold (K+1) <= 34561 (K+1)^2 2^(K+1) <= 69122 * 2^(3K)` after absorbing
`(K+1)^2 <= (2^K)^2`. Taking logs gives `orderLowerBound L < K`.

The factor `3` and the constant `69122` are artefacts of that absorption. The sharp constant needs
bootstrapping on `K <= log_2 L` instead; it changes the constant, not the exponent.

## Lean traps hit

- `Nat.findGreatest_spec` will not higher-order-unify `P (findGreatest P n)` against a goal phrased
  through a wrapper definition. Pass `(P := ...)` (and `(n := ...)`) explicitly.
  `Nat.le_findGreatest` and `Nat.findGreatest_is_greatest` are fine because the supplied `P m`
  argument pins the predicate.
- `push_neg` is deprecated in this toolchain and its warning fails the formal lint gate. Use
  `rcases lt_or_ge a b with h | h` instead of `by_contra` + `push_neg`.
- `lt_or_le` no longer exists; it is `lt_or_ge`.

## Remaining

Only Z9: discharge `hS2`/`hSR`/`hfac` of `norm_dirichlet_sigma_littlewood_assembled` at
`K = littlewoodOrder t` (sigma-analogues of `DirichletTailDominated` /
`norm_dirichlet_partial_littlewood_balanced`), giving a rectangle bound of width
`1 - sigma <= 1/(6*2^K) ~ 1/log t`, then hand off to `PNTPlus/ZetaBounds` (Landau, 3-4-1).
See `mem:route_e/littlewood_z6_sigma_parameter_selection_2026_08_06`.

# Littlewood Z6 — parameter selection off the line is the line's, verbatim

## The finding

The rectangle (`Re s = sigma`) estimate needs **no new split point and no new top exponent**. Set
`C = 2^S` with `S = splitExponent t K` and run the range to `2^(T+1)` with `T = topExponent t`
(so the number of blocks is `R = T + 1 - S`). Then the rectangle shape's two `t`-bounds are
*literally* the two the line case already solved:

- `8*pi*(C*2^(R-1))^(1/3) <= t`  is  `8*pi*(2^T)^(1/3) <= t`  =  `topExponent_bound`
- `t <= 2*pi*2^K*C^(K-1)*C^(-1/3)`  is  `t <= 2*pi*2^(S(K-4/3)+K)`  =  `le_two_pow_splitExponent`

Reason: the derivative-test half of the argument is sigma-independent. All sigma-dependence sits in
(a) the head below the abscissa and (b) the depth bracket, and the strip condition
`1 - sigma <= 1/(6*2^K)` already absorbs (b) (see `mem:route_e/littlewood_z5_uniform_strip_2026_08_06`).

## The head trap, and its resolution

`1 + ((C-1)^(1-sigma) - 1)/(1-sigma) + (C-1)^(-sigma)` — the middle term is a difference quotient
that tends to `log (C-1)` as `sigma -> 1`. Any bound that drops the `1/(1-sigma)` factor loses; any
bound that keeps it blows up. The right elementary inequality is

```
(x^a - 1)/a  <=  x^a * log x          (x >= 1, a > 0)
```

`RHTower.Sieve.rpow_sub_one_div_le`, proved from `exp u - 1 <= u * exp u` (which is
`Real.add_one_le_exp (-u)` multiplied by `exp u`). It collapses the head to `2 + C^(1-sigma) log C`,
which at `sigma = 1` is `2 + log C` — the head on the line. Nothing is lost off the line.

**Reusable**: this is the general "difference quotient of `a |-> x^a` at 0 is below its derivative at
`a`" lemma. Reach for it whenever an integral comparison `sum n^(-sigma)` head has to survive
`sigma -> 1`.

## The trade-off form

With `stripTheta t K := S / (6*2^K)`:

```
||sum_{n < 2^(T+1)} n^(-sigma-it)||  <=  2 + 2^theta * S * log 2  +  R * 2560 * 2^(-theta)
```

`RHTower.Sieve.norm_dirichlet_sigma_littlewood_theta`. **One** exponent governs both terms with
opposite signs. Raising the split point widens the head by `2^theta` and shrinks each block by
`2^(-theta)`. The line case is this with the `2^theta` head factor absent.

## Modules (all `[propext, Classical.choice, Quot.sound]`)

- `RHTower/Sieve/DirichletSigmaTarget.lean` — `stripTargetEps C K = 2560 exp(-log C/(6*2^K))`,
  `stripTargetEps_deep` (equality in the depth check),
  `norm_dirichlet_sigma_littlewood_canonical`
- `RHTower/Sieve/DirichletSigmaHeadSimplify.lean` — `rpow_sub_one_div_le`, `strip_head_le`,
  `norm_dirichlet_sigma_littlewood_strip_head`
- `RHTower/Sieve/DirichletSigmaAssembled.lean` — `norm_dirichlet_sigma_littlewood_assembled`,
  `stripTheta`, `stripTargetEps_two_pow`, `two_pow_rpow_head_le`,
  `norm_dirichlet_sigma_littlewood_theta`

## What remains

Only `K = K(t)`. Thresholds unchanged from the line (`largenessBound`, `balanceBound` in
`DirichletThreshold.lean`); `K ~ log_2 log t` gives `O(log t/log log t)` on the line and
simultaneously fixes the strip width `1 - sigma <= 1/(6*2^K) ~ 1/log t` — the classical zero-free
region width. Then hand off to `PNTPlus/ZetaBounds` (Landau / 3-4-1).

## Lean note

`rw [stripTheta]` unfolds only in the goal; a hypothesis carrying `stripTheta` stays a distinct atom
and `linarith` fails. Use `simp only [stripTheta] at h ⊢`.

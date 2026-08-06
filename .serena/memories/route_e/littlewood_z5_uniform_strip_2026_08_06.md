# Littlewood Z5: a strip of uniform validity (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletSigmaStrip.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

`norm_dirichlet_sigma_littlewood_strip` : the depth bracket `1/(3·2^K) − (1−σ)` degenerates as σ
approaches `1 − 1/(3·2^K)`. Halving the allowance decouples them: on

```
1 − 1/(6·2^K) ≤ σ < 1
```

the bracket is ≥ `1/(6·2^K)`, so a **single σ-free depth check**
`log(2560/ε) ≤ (1/(6·2^K))·log C` replaces the σ-dependent condition, and the rectangle bound holds
uniformly across the strip.

## Why this is the terminal form

**This is exactly what a zero-free region argument consumes**: a growth bound valid uniformly on a
rectangle left of `Re s = 1`, of width `1/(6·2^K)` — a fixed function of the order.
`PNTPlus/ZetaBounds`'s Landau/3-4-1 pipeline takes such a rectangle bound and returns the region.

## Z5 status: structural work finished

Remaining: parameter selection (`C`, `R`, `K`, `ε` as functions of `t`) and the pipeline hand-off.
No new mathematics — the same optimisation already isolated on the line
(`route_e/littlewood_z3_capstone_2026_08_06`).

## Full Z5 module list

`DirichletBlockSigma`, `DirichletSigmaTail`, `DirichletSigmaHead`, `DirichletSigmaUniform`,
`DirichletSigmaShape`, `DirichletSigmaEndpoints`, `DirichletSigmaStrip`.

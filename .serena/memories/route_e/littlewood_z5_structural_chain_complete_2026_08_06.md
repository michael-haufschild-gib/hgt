# Littlewood Z5 structural chain COMPLETE: the rectangle shape (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletSigmaShape.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

`norm_dirichlet_sigma_littlewood_shape` — σ-analogue of `norm_dirichlet_partial_littlewood_shape`.
For `0 < σ < 1`, `t > 0`, `3 ≤ C`, `K ≥ 2`, `ε > 0`, per block `r < R` at `N_r = C·2^r`:

```
(K−1)! ≤ N_r
8π·N_r^{1/3} ≤ t
t ≤ 2π·2^K·N_r^{K−1}·N_r^{−1/3}
log(2560/ε) ≤ (1/(3·2^K) − (1−σ))·log N_r
  ⟹ ‖∑_{n<C·2^R} n^{−σ−It}‖
      ≤ (1 + ((C−1)^{1−σ}−1)/(1−σ) + (C−1)^{−σ}) + R·ε
```

First three hypotheses identical to the line case (they concern `lam` only, which has no σ); the
fourth is the depth criterion carrying the width term `1−σ`.

## Z5 module list

`DirichletBlockSigma` (bound, phase_prefix_bound, full, normalized, saving, saving_of_small_factorial),
`DirichletSigmaTail` (generic dyadic assembly + σ tail), `DirichletSigmaHead` (term modulus, head,
head+tail), `DirichletSigmaUniform` (depth off the line, uniform tail), `DirichletSigmaShape`.

**Cost: eight theorems + five corollaries**, vs ~25 modules for the line case — because everything
about the *phase* is σ-free; only the Abel weighting, the head, and the depth criterion needed
analogues.

## Remaining for the zero-free region

Choose parameters as functions of `(t, σ)` — analogue of `splitExponent`/`topExponent`/`targetEps` —
then feed to `PNTPlus/ZetaBounds`'s Landau/3-4-1 pipeline, which converts a growth bound on a
rectangle left of `Re s = 1` into the region.

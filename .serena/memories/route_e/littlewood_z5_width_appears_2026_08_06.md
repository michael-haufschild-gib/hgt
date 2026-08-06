# Littlewood Z5: depth off the line — the zero-free width appears (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletSigmaUniform.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

- `block_sigma_saving_le_of_log_ge (hN : 1 ≤ N) (hε : 0 < ε)` :
  `log(2560/ε) ≤ (1/(3·2^k) − (1−σ))·log N ⟹ 2560·N^{1−σ}·N^{−1/(3·2^k)} ≤ ε`.
- `norm_dirichlet_sigma_partial_uniform` : head + `R·ε` (σ-analogue of
  `norm_dirichlet_partial_two_regime_uniform`).

## The key structural fact

The bracket `1/(3·2^k) − (1−σ)` is positive **exactly when `1 − σ < 1/(3·2^k)`**. So the rectangle
estimate survives off the line only within that distance of `Re s = 1`.

**The saving exponent `1/(3·2^k)` of the derivative test — the same quantity that produced the
`loglog` gain on the line — is precisely what limits how far left the rectangle may reach. The
region's width and the line's saving are one number, not two.**

Consequence for the region tier: with `2^k ≈ log t` the width is `≈ 1/(3 log t)` (de la Vallée
Poussin shape); Littlewood's `loglog t/log t` needs `2^k` held near `log t/loglog t` rather than
`log t` — exactly the tension the two threshold conditions on `(t,K)` encode
(see `route_e/littlewood_z3_capstone_2026_08_06`).

## Remaining for Z5

Threshold form off the line, then `PNTPlus/ZetaBounds` Landau/3-4-1 pipeline consumes the rectangle
bound.

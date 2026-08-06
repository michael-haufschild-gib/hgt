# Littlewood Z3: endpoint reduction of the schedule hypotheses (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletEndpointReduction.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

`norm_dirichlet_partial_littlewood_endpoints` — with an **antitone** order schedule (`k r ≤ k S` on
`[S,R)`), four of the five hypotheses of `norm_dirichlet_partial_littlewood_shape` become endpoint
checks:

| hypothesis | binds at | reduced form |
|---|---|---|
| `(k r −1)! ≤ N_r` | bottom | `(k S −1)! ≤ A·2^S` |
| `8π·N_r^{1/3} ≤ t` | top | `8π·(A·2^{R−1})^{1/3} ≤ t` |
| depth `3·2^{k r}·log(2560/ε) ≤ log N_r` | bottom | at `r = S` |
| upper `t`-bound | — | stays per-block |

Mechanism: raising the block raises `N_r` and lowers `k r`, so both monotonicities point the same
way. Needs `ε ≤ 2560` so `log(2560/ε) ≥ 0` (otherwise `2^{k r} ≤ 2^{k S}` multiplies the wrong way).

## Consistency of the regime (paper — confirms non-vacuity)

With `L = log N`, `T = log t`:
`(3) L ≤ 3(T − log 8π)`; `(4) k ≳ T/L + 4/3`; `(5) 2^k ≤ L/(3 log(2560/ε))`.
Substituting (4) into (5) with `L = T/m`, `ε = 1/m` gives
`2^m · m · log(2560 m) ≲ T/(3·2^{4/3})`, i.e. **`m ≈ log₂ T = log₂ log t`**.
Final bound `1 + T/m + (log₂ t)/m ≈ C·log t/log₂ log t` — Littlewood. The regime is consistent, so
the packaged theorem is not vacuous.

## Remaining

Realise that regime with explicit naturals (`A`, `S`, `R`, `k : ℕ → ℕ`, `ε` as functions of `t`),
discharging the two endpoint checks and the per-block upper `t`-bound. Then Z4, Z5.

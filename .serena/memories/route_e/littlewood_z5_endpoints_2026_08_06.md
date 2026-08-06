# Littlewood Z5: endpoint reduction off the line (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletSigmaEndpoints.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

`norm_dirichlet_sigma_littlewood_endpoints` — with a constant order, all four per-block hypotheses
of the rectangle shape become endpoint checks:

| hypothesis | binds at | reduced form |
|---|---|---|
| `(K−1)! ≤ N_r` | bottom | `(K−1)! ≤ C` |
| upper `t`-bound | bottom | at `N = C` |
| depth | bottom | at `N = C` |
| lower `t`-bound | top | at `N = C·2^{R−1}` |

**`schedule_upper_bound_mono` from the line case is reused verbatim** for the upper `t`-bound row —
it never mentioned σ.

## The width is now an explicit hypothesis

The depth criterion is monotone only when its bracket is nonnegative, i.e. `1 − σ ≤ 1/(3·2^K)`,
which appears as the hypothesis `hwidth`. That is the width of the strip on which the estimate holds
at all; it now sits in the statement rather than being implicit in the arithmetic.

## Remaining before the region

Constant-order / power-of-two / exponent-form layer off the line (mechanical — those steps only
rearrange the same inequalities), parameter choices as functions of `(t, σ)`, then
`PNTPlus/ZetaBounds`'s Landau/3-4-1 pipeline.

# The archimedean wall mass controls the left asymptotic

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); auxiliary strengthening of accepted contribution 5.
- **Target:** ECS Q9; leading asymptotics of the charge-subtracted balance.

For the actual state, write `M=Re LF(1/2)`, `r_k=2(k+1)+1/2` and
`b_k=M Re LF(r_k)>0`. Let

`B(t)=M Re[-a stateMeromorphic(-t-8)-primeHead(-t)-LF(-1/2)/(-t+1/2)]`.

The resolvent identity gives `B(t)=Σ_k b_k/(r_k+t)` for `t>1/2`.
Exactly one of the following alternatives holds:

1. `Σ_k b_k` converges, and `t B(t) → Σ_k b_k > 0`.
2. `Σ_k b_k` diverges, and `t B(t) → +∞`.

Thus the actual balance cannot be `o(1/t)`. This supplies a leading-mass law
without assuming a boundary trace of `F` or summability of its positive-real samples.

## Proof

The ECS resolvent expansion and zero-free positive-real Laplace samples give
`b_k>0` and summability of `b_k/(r_k+t)` for every `t>0`. Each multiplier
`t/(r_k+t)` lies between zero and one and tends to one. If the masses are
summable, dominated convergence gives the finite limit, which is positive.
Otherwise their finite subsums exceed every bound. Each scaled finite subsum
tends to its unscaled mass; positivity of the remaining terms bounds the full
scaled sum below it, proving divergence. The exact continuation formula
identifies this sum with `t B(t)` eventually. Both alternatives give an eventual
strictly positive lower bound and exclude convergence to zero.

## Lean and scope

`ExclusionOfTheCriticalState/TheArchimedeanWallMassControlsTheLeftAsymptotic.lean`
passed its final plain `lake --old env lean` check and is umbrella-wired.
Main declarations: `criticalState_archimedeanWall_asymptotic`,
`criticalState_scaled_wall_eventually_pos`,
`criticalState_scaled_wall_not_tendsto_zero`.

Which mass alternative the actual state would satisfy remains undetermined.
This classifies the archimedean balance; it supplies neither an asymptotic for
the prime head alone nor the arithmetic contradiction required by Q8.
No additional contribution counted. No axiom checks or external searches.

# The archimedean wall mass controls the left asymptotic

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** ECS Q9; leading asymptotics of the charge-subtracted balance.

For the actual state, write `M=Re LF(1/2)`, `r_k=2(k+1)+1/2` and
`b_k=M Re LF(r_k)>0`. Let

`B(t)=M Re[-a stateMeromorphic(-t-8)-primeHead(-t)-LF(-1/2)/(-t+1/2)]`.

The verified resolvent identity gives `B(t)=Σ_k b_k/(r_k+t)` for `t>1/2`.
Conjecture: exactly one of the following alternatives holds:

1. `Σ_k b_k` converges, and `t B(t) → Σ_k b_k > 0`.
2. `Σ_k b_k` diverges, and `t B(t) → +∞`.

Thus the actual balance cannot be `o(1/t)`. This supplies a leading-mass law
without assuming a boundary trace of `F` or summability of its positive-real samples.

## Connection and proof route

The ECS resolvent expansion and zero-free Laplace samples supply positive masses.
The corpus Cauchy-transform mass theorem recovers finite mass by dominated
convergence. Here each multiplier `t/(r_k+t)` increases to one. In the summable
case, series dominated convergence gives the limit. Otherwise finite subsums of
the positive masses exceed every bound; convergence of each finite subsum and
positivity of the remaining terms force divergence of the scaled balance.

## Status

The resolvent identity and positivity are verified inputs. The finite/infinite
mass classification and its actual-state specialization remain to formalize.
No contribution counted.

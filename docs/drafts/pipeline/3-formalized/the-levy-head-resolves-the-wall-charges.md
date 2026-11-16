# The Lévy head resolves the wall charges

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** ECS Q9; exact head coordinates, a sign restriction and uniform left decay.

## Statement

For every energy-domain profile and `Re p<1/2`, the absolutely convergent expansion is

`JF(p)=Σ(k≥0) LF(2k+1/2)/(2k+1/2-p)`.

Its first mode cancels `LF(1/2)/(p-1/2)` exactly. For an actual critical state and
`Re p<-1/2`, the remaining balance satisfies

`Re LF(1/2) · Re(-a stateMeromorphic(p-8)-primeHead(p)-LF(-1/2)/(p+1/2))>0`.

For every energy-domain profile, `JF`, the prime heads, the left remainder and
`stateMeromorphic` tend to zero as the real part tends to minus infinity, uniformly
in imaginary part. In particular, for every `ε>0` there is `A` such that
`Re w≤A` implies `‖stateMeromorphic W₀ F w‖<ε`.

## Proof

Resolve the Lévy density into `Σ exp(-(2k+1/2)x)` using the corpus archimedean
mode expansion. Fubini on `x>0, -x<u<0` gives
`∫ exp((p-r)x)H_x(p) dx=LF(r)/(r-p)` for `r>0, Re p<r`.
Existing near/far head bounds dominate the mode sum and justify the interchange.
The mode at `r=1/2` cancels the positive half-charge.

On the positive real axis, the actual state's transform is real, continuous and
zero-free. Its samples at `2k+1/2` therefore share the sign of `LF(1/2)`.
Every denominator `2k+1/2-p` has positive real part on `Re p<1/2`; taking real
parts of the absolutely convergent tail proves the strict sign restriction.

Write each compensated head as `∫(u>-x) exp(p(x+u))F(u) du`. For `Re p≤0` its
integrand is bounded by `|F(u)|`, and tends to zero as `Re p→-∞` for `u>-x`.
Dominated convergence removes each head. The existing Lévy dominator at real
part zero removes the outer integral; the summable prime dominator at real part
minus one removes the prime sum. The fixed affine charges vanish uniformly in
height. Translation by eight gives the continuation's limit.

## Lean

Both modules passed final plain `lake --old env lean` checks and are umbrella-wired:

- `ExclusionOfTheCriticalState/TheLevyHeadResolvesTheWallCharges.lean`:
  `hasSum_levyHead_resolvents`, `leftRemainder_eq_resolvents`,
  `stateMeromorphic_eq_resolvents`, `criticalState_left_prime_balance_re_pos`.
- `ExclusionOfTheCriticalState/TheTransformOfTheStateVanishesUniformlyToTheLeft.lean`:
  `tendsto_levyHeadTerm_left`, `tendsto_primeHead_left`,
  `tendsto_stateMeromorphic_left`, `exists_left_halfPlane_norm_stateMeromorphic_lt`.

No trace or pointwise boundary value of the profile is assumed. Leading rates,
vertical square-integrability and an arithmetic contradiction remain open.

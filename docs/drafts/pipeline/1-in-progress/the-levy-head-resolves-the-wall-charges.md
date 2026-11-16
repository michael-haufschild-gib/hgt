# The Lévy head resolves the wall charges

- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), with the uniform-decay endpoint pending
- **Target:** ECS Q9; exact head coordinates and left asymptotics, also supporting Q2 contour bounds.
- **Verified statement:** For every actual energy-domain profile and `Re p < 1/2`,
  `JF(p) = Σ(k≥0) LF(2k+1/2)/(2k+1/2-p)`, absolutely convergently.

## Mathematical connection

`RHTower.ArchimedeanAnomaly.hasSum_archLevyDensity` resolves the Lévy density into
`exp(-(2k+1/2)x)`. Swapping the head integral with one exponential mode gives
`LF(λ)/(λ-p)`. Existing head domination supplies absolute integration and justifies
the full geometric-mode interchange.

The `k=0` term cancels `LF(1/2)/(p-1/2)` in `leftRemainder`. Thus left of the strip,
`-a LF(w)` equals the remaining archimedean modes, prime heads and the single
charge `LF(-1/2)/(w+17/2)`. This is an exact state identity, not an exclusion claim.

For the actual state, the positive-real Laplace values are real, nonzero and have
one sign. Consequently the mode weights share that sign: after orientation, the
remaining archimedean sum has strictly positive real part throughout `Re p<1/2`,
despite the profile changing sign on every ray. For `Re p<-1/2`, Lean proves

`Re LF(1/2) · Re(-a stateMeromorphic(p-8) - primeHead(p) - LF(-1/2)/(p+1/2)) > 0`.

## Lean verification and remaining endpoint

`ExclusionOfTheCriticalState/TheLevyHeadResolvesTheWallCharges.lean` passed its final
plain `lake --old env lean` check and is umbrella-wired. Declarations:
`integral_exponential_mul_levyHead`, `hasSum_levyHead_resolvents`,
`stateMeromorphic_eq_resolvents`, `criticalState_left_prime_balance_re_pos`.

Uniform decay as the real part tends left remains to be formalized. No pointwise
values or boundary trace of the profile are assumed.

The complete Q9 package will count once after that endpoint closes. No external
novelty or axiom checks.

# Exact successor-fiber threshold and touching decay

- **ID:** successor-fiber-open-threshold-and-touching-decay
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** At positive overlap `c` and positive horizon `N`, the explicit plateau's
  actual successor divisor fiber is positive exactly when `N log(1+1/N)<c`.
  At `c=1`, it is positive at every finite horizon but is `O(log N/N²)` and tends to zero.
- **Module:** `TransMetzlerWeilPositivity/TheSuccessorFiberHasAnExactOpenThreshold.lean`.

## Proof

The plateau autocorrelation is positive exactly on `(-1,1)`. Positivity in the interior
comes from a common interval where both profile factors are positive. Outside this interval,
support forces zero; at its endpoints, the quadratic endpoint bound forces zero as well.

The exact successor-fiber formula is
`√(N/(N+1)) log(N+1) Cφ(t_N/c)/∫φ²`, where `t_N=N log(1+1/N)`.
Every other factor is positive. Thus the actual positivity threshold is open,
whereas geometric eligibility has a closed endpoint.

Since `1-1/N<t_N<1`, the quadratic endpoint bound gives
`Cφ(t_N)≤8000²/(4N²)`. Therefore

`0<fiber(1,N)≤8000² log(N+1)/(4N²∫φ²)`.

The bound `log(N+1)≤N` supplies a constant times `1/N`, proving convergence to zero.
For fixed `0<c<1`, eventually `c<t_N`, so the fiber is exactly zero. For fixed `c>1`,
the previously audited theorem `tendsto_plateauSuccessorFiber_div_log` gives a positive
limiting coefficient after division by `log(N+1)`, hence divergence of the fiber.
This is a statement in the corpus's weighted Schur row, not an unweighted operator norm.

## Lean declarations

- `transMetzlerProfile_bumpCorr_eq_zero`, `transMetzlerProfile_bumpCorr_pos_iff`
- `plateauSuccessorFiber_eq_zero_of_le`, `plateauSuccessorFiber_pos_iff`
- `plateauSuccessorFiber_one_pos`, `plateauSuccessorFiber_one_le`
- `plateauSuccessorFiber_one_le_inv`, `tendsto_plateauSuccessorFiber_one`
- `eventually_plateauSuccessorFiber_eq_zero`

Direct `lake --old env lean` check and all six transitive axiom audits passed with default
limits. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Umbrella import is wired.
The imported divisor-fiber asymptotic also passed its direct check and axiom audits.

# The Möbius exceptional set is comeager and Haar-null

- **ID:** acg-comeager-null-2026-10-26
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ArithmeticCorrelationGeometry (typicality of the point 0, contribution 1)
- **Statement:** The gauge points where the half-power law for `μχ_x` fails form a residual set of
  Haar measure zero; every neighbourhood of `0` contains such points (twin tails).

## Proof
Twin tail of `x₀` beyond `I`: keep `x₀` on `I`, put `½` on all other primes. On squarefree `n`,
`μ(n)χ(n) = ψ(gcd(n,Q))`; the twisted Mertens sum is `Σ_{d|Q} ψ(d)·C_Q(N/d)` with `C_Q` the count of
squarefree integers coprime to `Q`; by the coprime squarefree density it is
`δ_Q ∏_{p|Q}(1−e(x_p)/p)·N + o(N)`, nonzero constant. Strongly exceptional points (beating every
multiple of `(N+1)^{3/4}`) are a `G_δ` containing a twin tail in every basic open set.

## Lean
`formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheMoebiusExceptionalSetIsComeagerAndNull.lean`:
`moebius_mul_twist_twinTail`, `card_gcd_eq`, `moebiusGaugeSum_twinTail`,
`tendsto_moebiusGaugeSum_twinTail_div`, `dense_strongExceptional`,
`moebius_exceptional_residual_and_null`, `zero_mem_closure_exceptional`.

## Insight
RH asks whether 0 lies in a meager set of full measure. No argument that is stable under small
perturbations of the gauge point (finitely many prime phases to finite precision) can decide it.

# Weighted orthogonality for the current power core

- **Stage:** 1-in-progress.
- **Goal:** Prove a weighted polynomial inequality valid at every degree, retaining endpoint constraints.
- **Corpus inputs:** `legP_orthog`, `legP_sq_integral`, `LegendrePolynomialKernel`, `PowerPolynomialKernel`.

The current power energy uses weight `(1−x²)^8`. Embedding `(1−x²)^4P` in the unweighted degree-`n+8` Legendre space discards its endpoint constraints.

The shifted Legendre derivative basis is orthogonal for weight `(1−x²)^s`. Its squared leading coefficient divided by squared norm is

`(n+s+1/2)c_(n+s)² · ((n+s)!)²/[n!(n+2s)!]`,

where `c_j` is the existing Legendre leading coefficient. The factorial ratio retains the constraints lost by the embedding. `WeightedLegendreNorms.lean` has verified this identity and monotonicity in degree using only standard axioms; its final individual audit remains pending. Required remaining proofs: degree-preserving expansion and the exterior kernel bound. Any resulting tail charge still requires payment by the actual source.

The proposed recurrence is
`I_(r+1)(n,m)=(m(m+1)−r(r+1))I_r(n,m)`,
where `I_r(n,m)=∫₋₁¹(1−x²)^r P_n^(r)(x)P_m^(r)(x)dx`.
It follows by differentiating the existing Legendre equation and one integration by parts; every boundary term contains `(1−x²)^(r+1)`. Iteration retains orthogonality and gives the exact weighted norms. `WeightedLegendreDerivatives.lean` has passed its production check with only standard axioms; its final individual audit remains pending.

For `G_n=P_(n+r)^(r)`, differentiating Bonnet's recurrence together with the adjacent derivative difference gives
`(n+1)G_(n+1)=(2n+2r+1)xG_n−(n+2r)G_(n−1)`.
The existing exterior monotonicity argument should therefore bound `G_n` by its leading monomial. Its squared leading coefficient divided by norm has consecutive ratio
`(2n+2r+3)(2n+2r+1)/((n+1)(n+2r+1))`.
This retains a degree-preserving kernel without dividing by an exterior endpoint weight. The target is the degree-uniform inequality, not another isolated rank certificate. Its growth must also identify whether a fixed-radius core and fixed verified height can support an all-rank payment.

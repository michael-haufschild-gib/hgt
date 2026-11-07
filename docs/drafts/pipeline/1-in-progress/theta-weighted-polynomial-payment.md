# Weighted orthogonality for the current power core

- **Stage:** 1-in-progress.
- **Goal:** Improve finite-rank payment beyond the unweighted Legendre embedding.
- **Corpus inputs:** `legP_orthog`, `legP_sq_integral`, `LegendrePolynomialKernel`, `PowerPolynomialKernel`.

The current power energy uses weight `(1−x²)^8`. Embedding `(1−x²)^4P` in the unweighted degree-`n+8` Legendre space discards its endpoint constraints.

Candidate replacement: orthogonal degree-`n` polynomials for weight `(1−x²)^s`. A Rodrigues construction should give squared leading coefficient divided by squared norm

`(n+s+1/2)c_(n+s)² · ((n+s)!)²/[n!(n+2s)!]`,

where `c_j` is the existing Legendre leading coefficient. The factorial ratio retains the constraints lost by the embedding. Required proofs: weighted orthogonality and norm, a degree-preserving expansion, and an exterior bound with this coefficient. No new rank is claimed from this candidate. The resulting explicit tail charge must still be paid by the complete current core.

The proposed recurrence is
`I_(r+1)(n,m)=(m(m+1)−r(r+1))I_r(n,m)`,
where `I_r(n,m)=∫₋₁¹(1−x²)^r P_n^(r)(x)P_m^(r)(x)dx`.
It follows by differentiating the existing Legendre equation and one integration by parts; every boundary term contains `(1−x²)^(r+1)`. Iteration would retain orthogonality and give the exact weighted norms. This derivation is written in `WeightedLegendreDerivatives.lean` but not yet Lean-checked.

For `G_n=P_(n+r)^(r)`, differentiating Bonnet's recurrence together with the adjacent derivative difference gives
`(n+1)G_(n+1)=(2n+2r+1)xG_n−(n+2r)G_(n−1)`.
The existing exterior monotonicity argument should therefore bound `G_n` by its leading monomial. Its squared leading coefficient divided by norm has consecutive ratio
`(2n+2r+3)(2n+2r+1)/((n+1)(n+2r+1))`.
This retains a degree-preserving kernel without dividing by an exterior endpoint weight. The next concrete payment target is rank fifteen with `r=8`, core radius twelve, and the already audited current floor `a/185`.

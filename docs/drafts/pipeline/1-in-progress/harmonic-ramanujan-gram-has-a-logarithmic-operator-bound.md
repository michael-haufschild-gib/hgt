# The harmonic Ramanujan Gram has a logarithmic operator bound

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `ramanujan-harmonic-gram-finite-parts-are-prime-local.md`; Q1/O1.
- **Target:** A common finite-horizon Gram expansion for every conductor packet.

Let `u_m=c_m/sqrt(phi(m))`, `G_m,l(N)=sum_(n≤N)u_m(n)u_l(n)/n`,
and `B_m,l=gamma·1_(m=l)−I(m,l)/sqrt(phi(m)phi(l))`.
For positive conductors and `N≥1`, the proposed entry estimate is

`|G_m,l(N)−1_(m=l) log N−B_m,l| ≤ 4ml/(N+1)+1_(m=l)/N`.

For `Q≥2`, every vector on conductors `1≤m≤Q` satisfies

`|sum_(n≤N)(sum_(m≤Q)a_m u_m(n))²/n−log N sum a_m²|`
`≤ [|gamma|+4 log Q+log 4+4+Q(Q−1)/(N+1)+1/N] sum a_m²`.

## Proof mechanism

The centered product `u_m u_l−1_(m=l)` has period `ml`, mean zero,
and period absolute mass at most `2ml`, by complete-period Plancherel
and `2|ab|≤a²+b²`. Every interval sum is therefore at most `4ml`.
Abel summation bounds its harmonic tail by `4ml/(N+1)`. The exact
harmonic-to-torsion limit identifies that tail's endpoint. The classical
harmonic remainder contributes only the diagonal term `1/N`.

For the whole packet, the sharp two-sided large sieve gives
`|sum_(A<n≤A+K) F(n)²−K sum a_m²|≤Q(Q−1)sum a_m²`.
Abel summation of this signed discrepancy gives the stronger quadratic
remainder `Q(Q−1)sum a_m²/(N+1)` directly.
The torsion counterterm controls the finite part by
`(|gamma|+4 log Q+log 4+4) sum a_m²`.

The exact finite-part and torsion identities passed Lean; their final
direct source audits remain. The common remainder is under Lean verification.
The complete Weil agreement-shell identity remains open.

# The regional logarithmic energy pays the signed first fold

- **ID:** F1-LS
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** [Joint first-fold payment](../1-in-progress/f1-joint-cubic-prime-payment.md)
- **Statement:** The logarithmic principal energy restricted to the prime-two strip,
  together with its signed reflection, has a positive mass floor `1/16`.

Put `b=log2`, `η=1−b`, `l=2b−1`, `w=b/√2`, `u(x)=b+ηx`.
For every real C¹ function `H:ℝ→ℝ`, define

`T(H)=η/2 ∫∫ K(u(x),u(y))(H(x)−H(y))² dx dy`,
`K(s,t)=1/(2|s−t|)−1/(2(s+t))`,
`R(H)=∫H(x)H(−x)dx`, `E=∫H²`, `m=∫H`.
All integrals here use `[-1,1]`.

Then `[PROVED HERE]`

`T(H)+wR(H)≥E/16`.

The stronger retained-mean estimate is
`T+wR≥(139/250−w)E+(w−139/500)m²`.
The mean term preserves the full prime gain on constant strip profiles;
reducing the estimate to its uniform mass floor discards that gain.

Under `H(x)=G(b+ηx)`, multiplication by `η` gives the corresponding floor on
`[l,1]` for half the principal double integral plus `w∫G(u)G(2b−u)du`.
The exterior potential, off-strip pairs, and pole charge remain to be paid.

## Proof

The regional energy is `J(H)=∫∫(H(x)−H(y))²/(2|x−y|)`.
Since `b|x−y|≤u(x)+u(y)` and `η/b≤111/250`,

`T(H)=J(H)/2−η/4∫∫(H(x)−H(y))²/(u(x)+u(y)) ≥(139/500)J(H)`.

The first Legendre gap applied to `H−m/2` gives `J(H)≥2E−m²`.
Integration of `(H(x)+H(−x)−m)²≥0` gives `R(H)≥m²−E`.
Consequently

`T+wR≥(139/250−w)E+(w−139/500)m²≥E/16`,

using `49/100≤w≤4902/10000`. No energy outside the strip is spent.

## Lean status

Formalization in progress. Required inputs already audited: the regional first
Legendre gap and elementary prime-two weight bounds. The normalized theorem and
its physical-strip identification must both be checked before this bridge is complete.

# Arbitrary multiplicity near unit annihilator mass

- **Candidate:** For every real `β`, positive integer `r`, and `ε>0`, there is a positive one-prime Dirichlet polynomial with constant coefficient one, a zero of order `r` at `β+iπ/log 2`, and nonconstant mass in `[1,1+ε)` on `Re s=β`. For `r≥2`, the mass is strictly greater than one.

For odd `K`, set

`S=Σ_(j=0)^(r−1) (−1)^j binom(r−1,j)/(1+jK)`,

`Q(X)=1+S^(−1) Σ_(j=0)^(r−1) binom(r−1,j) X^(1+jK)/(1+jK)`.

Then `Q(−1)=0` and `Q′(X)=S^(−1)(1+X^K)^(r−1)`. Thus `−1` has exact multiplicity `r`. Also
`S=∫_0^1(1−t^K)^(r−1)dt>0`, so every coefficient is nonnegative. As odd `K→∞`, `S→1` and the sum of the nonconstant coefficients tends to one. The finite bound
`Σ_(j=1)^(r−1) binom(r−1,j)/(1+jK)≤(2^(r−1)−1)/(K+1)`
gives a direct quantitative existence proof without dominated convergence.

Substitute `X=2^(β−s)`; its derivative at the marked zero is `log 2≠0`, preserving multiplicity. The case `r=2` is the explicit trinomial in `TheUnitMassBoundaryOfPositiveAnnihilators`.

- **Corpus:** Positive finite annihilators with prescribed orders already exist; their power construction does not control mass at the zero near one. `HTGeometry/PolynomialAntiderivative.lean` supplies the primitive mechanism.
- **Lean status:** unformalized. Exact order transfer, finite binomial estimates, and the literal positive-polynomial construction require certificates.
- **Limit:** The marked root is not asserted to be a zeta zero. Extension to arbitrary fixed nonreal points is a separate question.

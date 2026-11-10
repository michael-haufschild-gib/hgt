# Stepanov bounds for Heilbronn sums and Fermat quotients

- **Stage:** 1-in-progress
- **Source:** review-0911 §11.4.

## Targets

For prime `p` and `p∤a`, prove a uniform power saving for
`H_p(a)=Σ_{n=1}^p exp(2πian^p/p²)`, together with a power-saving bound
for the fibres of `L_p(X)=Σ_{1≤j<p}X^j/j` over `𝔽_p`.

[Heath-Brown–Konyagin](https://doi.org/10.1093/qjmath/51.2.221)
prove `Σ_{r mod p}|H_p(a+rp)|⁴≪p^(7/2)` and hence `|H_p(a)|≪p^(7/8)`.
Their fibre estimate is
`#{x∈𝔽_p : L_p(x)∈U}≪(p·#U)^(2/3)`.
Orthogonality reduces the fourth moment to the collision count of `L_p`.
The first Witt carry identifies these collisions with the mixed-characteristic
congruence; a bound for an unrelated finite-field curve would not suffice.

## Nonvanishing input

The auxiliary substitution `Φ(X,L_p(X),X^p)` must be nonzero when
`deg_X Φ<A`, `deg_Y Φ<B`, `AB≤p`.
It suffices to show `X^p∤F(X,L_p(X))` for each nonzero bivariate `F`
of those degrees, by selecting the least power of the third variable.

A direct jet proof uses `D=(1−X)d/dX` and
`D L_p=1−X^(p−1)`. For every `n<p`, the value at zero of
`D^n((1−X)^a L_p^b)` equals the `b`th derivative of `t^n` at `t=−a`.
The error from `X^(p−1)` still vanishes at zero after fewer than `p−1`
further derivatives. The resulting confluent Vandermonde determinant is
nonzero for `0≤a<A`, `0≤b<B`, `AB≤p`: its factorials and node differences
are units modulo `p`.

Existing anchor: `det_confluentPolynomialJetMatrix` works over every
commutative ring. The finite-characteristic logarithm jets, auxiliary
vanishing constraints, parameter bounds and fourth-moment transfer remain
to be formalized. No analytic estimate is assumed as a premise.

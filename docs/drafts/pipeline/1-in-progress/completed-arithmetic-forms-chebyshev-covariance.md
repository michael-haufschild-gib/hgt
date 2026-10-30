# Arithmetic completion of the actual normalized Chebyshev energy

**ID:** completed-arithmetic-forms-chebyshev-covariance  
**Stage:** In progress  
**Type:** Exact actual-source covariance bridge

The literal source is
$$F(N)=\sum_{2\le d<N}\frac{\psi(d)-d}{\sqrt d},\qquad
E(N)=\sum_{2\le n\le N}\frac{F(n)^2}{n^2}.$$
Lean definitions: `GaloisForLFunctions.RHTower.chebyshevNormalizedCesaroSum`
in `RHTower/NormalizedChebyshevCesaroAndSqrtRieszBridge.lean`, and
`RHTower.chebyshevNormalizedCesaroMeanSquareEnergy` in
`RHTower/QuasiRHNormalizedChebyshevCesaroAndMertensActionAbscissaLaw.lean`.
The latter module proves that the exponent families $5/3+\varepsilon$ and
$3/2+\varepsilon$ for $E(N)$ are equivalent to the five-sixths and three-quarters
zero strips, respectively. It does not supply either actual upper bound.

Set $c_j=F(j)-F(j-1)$ and
$$C(N)=\sum_{1\le n\le N}\frac{F(n)^2}{n(n+1)}.$$
Telescoping identifies $C(N)$ with `cumulativeEnergy c N`; the proved conductor
identity then gives
$$C(N)=\frac{\mathcal E_{N+1}(j\mapsto c_j/j)}{N+1}.$$
Since $F(0)=F(1)=F(2)=0$, termwise denominator comparison has the target
$$C(N)\le E(N)\le\frac43 C(N).$$
The correction is exactly
$$E(N)-C(N)=\sum_{3\le n\le N}\frac{F(n)^2}{n^2(n+1)}.$$
Thus this source map preserves every power exponent with a fixed constant.
The completed Gram also exposes the weighted increment mass, weighted square
mass, and its nonnegative cyclotomic remainder. These identities and the
factor-$4/3$ comparison require formalization for the literal source.

For $j\ge3$, the increment is exactly
$$c_j=\frac{\psi(j-1)-(j-1)}{\sqrt{j-1}}.$$
The corpus bound $|\psi(d)-d|\le6d$ and the reciprocal-square-root sum bound
would pay the explicit coefficient channels by
$$\left|\sum_{j\le N}\frac{c_j}{j}\right|\le12\sqrt N,
\qquad \sum_{j\le N}\left(\frac{c_j}{j}\right)^2\le36N.$$
Writing $R_N$ for the nonnegative cyclotomic remainder of this literal packet,
the resulting sharper target is
$$\frac{R_N}{N+1}\le4E(N),\qquad
E(N)\le60N+\frac{R_N}{3(N+1)}.$$
Thus every exponent above one would be carried entirely by the normalized
cyclotomic remainder; the two explicit coefficient channels have a proved-source
linear payment once these estimates are formalized. No upper estimate for
the remainder is asserted.

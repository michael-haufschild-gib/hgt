# Arithmetic completion of the actual normalized Chebyshev energy

**ID:** completed-arithmetic-forms-chebyshev-covariance  
**Stage:** Formalized  
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
Since $F(0)=F(1)=F(2)=0$, termwise denominator comparison gives
$$C(N)\le E(N)\le\frac43 C(N).$$
The correction is exactly
$$E(N)-C(N)=\sum_{3\le n\le N}\frac{F(n)^2}{n^2(n+1)}.$$
Thus this source map preserves every power exponent with a fixed constant.
The completed Gram also exposes the weighted increment mass, weighted square
mass, and its nonnegative cyclotomic remainder.

For $j\ge3$, the increment is exactly
$$c_j=\frac{\psi(j-1)-(j-1)}{\sqrt{j-1}}.$$
The corpus bound $|\psi(d)-d|\le6d$ and the reciprocal-square-root sum bound
pays the explicit coefficient channels by
$$\left|\sum_{j\le N}\frac{c_j}{j}\right|\le12\sqrt N,
\qquad \sum_{j\le N}\left(\frac{c_j}{j}\right)^2\le36N.$$
Writing $R_N$ for the nonnegative cyclotomic remainder of this literal packet,
the exact estimates are
$$\frac{R_N}{N+1}\le4E(N),\qquad
E(N)\le60N+\frac{R_N}{3(N+1)}.$$
For every $r\ge1$, a uniform $N^r$ bound for $E$ is equivalent to one for
$R_N/(N+1)$. In particular, the two strip exponent families are exactly
equivalent to the corresponding bounds for this literal normalized remainder.
No upper estimate for the remainder is asserted.

**Lean:** `CompletedArithmeticForms/ChebyshevCyclotomicCompletion.lean`.
`chebyshevEnergy_covariance_defect`, `chebyshevCompletedEnergy_comparison`,
`chebyshevConductor_channels_le`, `chebyshevEnergy_cyclotomic_bounds`,
`chebyshevEnergy_power_bound_iff_cyclotomic`,
`five_sixths_strip_iff_chebyshevCyclotomicRemainder_subpower`, and
`three_quarters_strip_iff_chebyshevCyclotomicRemainder_subpower`.
The capstones use only `propext`, `Classical.choice`, and `Quot.sound`.

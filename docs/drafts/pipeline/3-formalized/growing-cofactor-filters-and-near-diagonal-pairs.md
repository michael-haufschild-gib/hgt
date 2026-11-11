# Growing filters and near-diagonal Gaussian cofactors

- **ID:** A86
- **Stage:** 3-formalized
- **Type:** THEOREM

## Near-diagonal law

The exact normalized overlap is

`[1+(1+(Im ε/Re ε)²)((m²−k²)/(2mk))²]^(−r)`.

On a dyadic cofactor interval of size `M`, rotation `|Im ε|≥t Re ε` confines
the main correlation to width `M/(t sqrt(r))`. Bernoulli's inequality gives
an inverse-quadratic majorant with that width. Its lattice rows are bounded by
`O(1+M/(t sqrt(r)))`; the continuum scale is proportional to `1/sqrt(mk)`.
The complete lattice has the already proved Bernoulli remainder.

For the full integer range `1≤m,k≤W`, the precise row bound is
`Σ_k overlap(m,k)≤1+4W/(t sqrt(r))`. Indeed
`|(m²−k²)/(2mk)|≥|m−k|/W`, and Bernoulli gives the majorant
`1/(1+α²(m−k)²)` with `α=t sqrt(r)/W`.
Use `1/(1+y²)≤2/(1+y)²`; the positive affine-square lattice telescopes to
at most `1/α`. The two sides of the diagonal contribute at most `4/α`.

## Growing-filter obstruction and replacement

`HolomorphicDampingFilters.dampingFilterCost` contains the factors
`2·2^j+dampingRootCost(ω)`. Repeated strip halving therefore costs approximately
`2^(d²/2)`, which cannot be absorbed by an exponential error when
`d` grows like `t/log t`.

Spend `δ=R/(d+1)` of strip radius at each root. Cauchy's estimate gives
`|f'|≤M/δ`; translation and
`|exp(hω)−1|≤2hB(1+exp(hB))` give

`|∏(T_h−exp(hω))f(0)| ≤ M[h((d+1)/R+2B(1+exp(hB)))]^d`.

At `R=1/(16t)`, `B≤t²`, `hB≤1`, `d≤t`, and `t≥34+2e`, the bracket
after removing `h` is at most `t³`. Thus `d log t≤κt` bounds the
spacing-normalized filter cost by `exp(3κt)`.

An unbounded half-strip loses the direct Gaussian horizon, but polynomial
tail moments offer a replacement. At `UW≥Xt²`, moment `k` costs
`X³·O(4^k(k+2)!/t^(4k))`. Taking `k` proportional to `t` can absorb the
growing filter. First-moment bounds alone do not allow `UV` near `X`;
the higher-moment half-strip estimate below supplies this range.

## Higher-moment strip bound

Write `s=Re z`, `r₀=1/(16t)` and `ε_z=ε exp(−2z)`. The rotated physical
scale satisfies `Xe^s/2≤Y≤2Xe^s`. For `s>−1`, `β≥1/2`, `p≥1/2`, and
`Y≥1`, put `L=1+log X+log 2` and `λ=β+p−1/2`. Then

`exp((1/2−β)s−t Im z) Y^(−p)(1+log Y)`
`≤4 exp(β+1) exp(p(1+log 2)) X^(−p)(1+log X)`.

Indeed `log Y≥log X+s−log 2`, `1+log Y≤L+s`, and
`exp(−λs)(L+s)≤(L+2)exp λ`. For `s≤0` use `s>−1`; for `s≥0` use
`s exp(−λs)≤s exp(−s/2)≤2`. Also `L+2≤4(1+log X)`.

Apply this to the proved higher-error estimate with `p=2r−1/2` and `p=1/2`.
For `t≥max(8192,4e²)`, `r≤t`, and `2e UV≤X`, the twisted actual error has
the uniform half-strip bound

`8 exp(β+2) C [(t^(8r)(UV)^(2r) X^(1/2−2r))`
`              + V t^(4r+1) X^(−1/2)](1+log X)`,

where `C=gaussianGrowingMomentConstant`. The first factor uses
`exp((2r−1/2)(1+log 2))≤(4e²)^r≤t^r`.
Take `r=floor((a/64)t/log t)`, `U=floor(exp(at)/t^69)`, and `V=floor t`.
The product budget is `UV t^68≤exp(at)`. The first strip-bound term is at most
`exp(−at/2)`; the second is at most `t² exp(−3at/8)`.
A filter with `d log t≤at/24` costs at most `exp(at/8)`, leaving a polynomial
times `exp(−at/4)`. Thus its spacing-normalized error is eventually at most
`exp(−at/8)`.

## Complementary cofactor tail

Take `W=ceil(2t^71)`, so `UW≥exp(at)t²` and eventually `W≤3t^71`.
For tail moment `k=floor t`, the twisted half-strip bound is

`M=784·32^r(r+1)! k! 2^(3+2k)e² X^(3+2k)/(UW)^(2k)`.

Eventually `3r≤k≤t`. The bounds `32^r(r+1)!≤t^(3r+2)`, `k!≤t^k`,
and `2^(3+2k)≤8t^k` give `M≤6272e² X³t²/t^k`.
Translate each filter root by `c=gaussianCofactorTwist(1/2,β,k)`.
Under `B+|c|≤t²` and `h(B+|c|)≤1`, the scalar twist costs at most `exp t`;
the filter costs `exp(at/8)`. Since `k≥t/2`, `t^k` absorbs both costs,
leaving at most `h^d exp(−at/8)` eventually.
Adding the arithmetic reduction error gives the actual prime-to-cofactor
error `≤2h^d exp(−at/8)`, retaining both signed continuum corrections.

## Lean status

`HolomorphicDampingFilters.norm_dampingFilterPolynomial_sum_le_growing_order`
is proved: equal-radius Cauchy estimates cost `exp(3κt)` while retaining
every spacing factor `h^d`, for `d log t≤κt`, `B≤t²` and `hB≤1`,
at sufficiently large height.

Exact overlaps, lattice remainder and growing unfiltered cofactor reduction
already exist in `ExceptionalLayerTheory`.
`TheNearDiagonalCofactorsHaveASummableRow.lean` contains the quadratic overlap
majorant and row bound `1+4W/(t sqrt(r))`; direct Lean check passed.
`TheGrowingGaussianErrorIsHolomorphic.lean` proves holomorphy of the actual
higher-moment arithmetic error and complementary cofactor tail, including
the factorial polynomial-moment tail bound. Its required dependency compile passed.
`TheGrowingGaussianErrorSurvivesTheFilter.lean` proves the actual half-strip
estimate and the concrete growing-order transfer above; required dependency
compile passed. The normalized filtered arithmetic error is eventually
at most `exp(−at/8)` for degree `d log t≤at/24`.
`TheGrowingCofactorTailSurvivesTheFilter.lean` proves the complementary-tail
bound with cutoff `ceil(2t^71)` and shifted-root budget; required dependency
compile passed. `TheGrowingFilterReachesPolynomiallyManyCofactors.lean`
combines both actual errors; direct Lean check passed.
The near-diagonal row bound concerns complete lattice correlations; it does
not prove cancellation after inserting prime coefficients.

All five new modules are wired into `ExceptionalLayerTheory.lean`.

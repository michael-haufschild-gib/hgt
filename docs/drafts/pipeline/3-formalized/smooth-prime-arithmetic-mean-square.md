# Smooth–prime mean square with arithmetic off-diagonal cost

- **ID:** TAPO-smooth-prime-arithmetic-mean-square
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Scope:** Broader RH research; uses the proved Fourier triangular majorant.

For `y`-smooth rows `A` and prime columns `P>y`, all in `(X,2X]`, and
coefficients `|c(m,p)|≤1`, every centered interval satisfies:

`∫_{−T}^T |Σ_(m∈A,p∈P) c(m,p)(mp)^(−i(U+t))|² dt`
`≤(5π/2)(T #A #P+8X² #A²)`.

The off-diagonal cost scales with the square of the number of
smooth rows. Generic product-frequency separation instead charges the
number of product terms. This is useful when the smooth support is sparse.

## Mechanism and inputs

`RHTower.Sieve.integral_Icc_normSq_finiteFrequencyPoly_le_collisionWeight`
is proved for arbitrary indexed real frequencies and complex coefficients.
At frequency `−log(mp)/(2π)` and width `1/(2πT)`, it bounds the mean square
by `(5π/2)T` times the actual logarithmic collision count. A center shift
is absorbed into coefficients of unchanged modulus.

The dependency is the cumulative arithmetic count
`E(1/T)≤#A #P+2 floor(4X²/T)#A²`, formalized on
`logarithm-cumulative-collision-gcd-cancellation.md`.
The floor estimate removes any harmonic logarithmic loss from this transfer.

## Boundary

This is an averaged bound for the actual smooth–prime polynomial. It does not
bound exceptional Bohr sets, growing infinite tails, or individual heights.
It uses a nonnegative Fourier kernel and is therefore kept outside the
sum-product programme's restricted methodology.

## Dependency-closed paper proof

Allow arbitrary sub-supports `A` and `B` of the balanced smooth rows and
rough prime columns. For fixed rows `m,m'`, partition closed logarithmic
column collisions into equal products and the two strict product orderings.
Smooth/prime coprimality makes the first part have `#B` members when `m=m'`
and zero otherwise. Each strict ordering is contained in the corresponding
full prime-column fibre, bounded by `H=floor(4X²δ)`. Thus the fixed-row
count is at most `1_(m=m') #B+2H`. Summing rows gives
`E_(A,B)(δ)≤#A #B+2H #A²`.

Put frequency `x_(m,p)=−log(mp)/(2π)` and kernel width `δ=1/(2πT)`.
The proved finite-frequency triangular-majorant theorem gives
`∫_[−T,T]|S(t)|²≤(5π/2)T E_(A,B)(1/T)`, since coefficient products have
modulus at most one and strict frequency collisions lie in the closed
logarithmic window. The arithmetic bound and
`T floor(4X²/T)≤4X²` give the displayed estimate.

For any center `U`, replace `c(m,p)` by `c(m,p)(mp)^(−iU)`. The new
coefficients have the same modulus and their polynomial at `t` is exactly
`S(U+t)`. This proves uniformity in the center without an exceptional set.
The literal unit-coefficient full-support sum is a direct specialization.

The existing corpus `indexed_meanValue` has error
`8N(1+log N) Σ|c|²`. The new bound retains a larger absolute diagonal
constant but replaces the product-support cost by `X² #A²`. No sharp
asymptotic or exceptional-height conclusion is asserted.

For factorized coefficients `c(m,p)=r(m)b(p)`, positivity of the integer
arguments gives `log(mp)=log m+log p`. The polynomial is therefore exactly
the smooth head times the prime tail, and the same estimate bounds
`∫|R(U+t)|²|B(U+t)|²`. The off-diagonal term is absorbed by the diagonal
scale when `T #P≥8X² #A`. This is a finite-data threshold, not an asserted
prime-density asymptotic.

The same bound divided by `V²` controls the smooth-head mass restricted to
`|B(U+t)|≥V`, for every `V>0`: on this set,
`|R|²≤|R|²|B|²/V²`. Integrate this pointwise inequality and enlarge the
integration set. Continuity gives all needed measurability and integrability.

## Lean status

`TailArithmeticOfThePrimeOrbit/TheSmoothPrimeMeanSquareHasAnArithmeticCost.lean`
proves `balancedSmoothPrimeEnergy_le`, `integral_balancedSmoothPrimePoly_le`,
`integral_balancedSmoothPrimePoly_shift_le`, `integral_fullSmoothPrimePoly_shift_le`,
`integral_balancedHead_primeTail_sq_le`, and
`setIntegral_balancedHead_on_large_primeTail_le`.

Direct source check passed. All six capstones and the imported Fourier kernel
were audited with `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.

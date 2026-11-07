# Rectangular arithmetic costs for smooth-head tail moments

- **ID:** TAPO-rectangular-arithmetic-moments
- **Stage:** 3-formalized
- **Type:** THEOREM

## Target

For smooth rows
`A⊂(X,2X]` and rough columns `B⊂[1,Z]`, retaining coefficient norms:

`∫_[−T,T] |R(U+t)|² |B(U+t)|²`
`≤(5π/2)(T ‖r‖₂²‖b‖₂²+4Z(X+Z)‖r‖₁²‖b‖∞²)`.

The same arithmetic estimate applies to every power of an actual prime-tail
polynomial. Its sparse-head error can improve the generic product-length
threshold. No exceptional-height cancellation is claimed.

## Dependency-closed paper proof

For fixed rows `m,m'>X`, gcd `g`, and columns at most `Z`, the quotient label
`p/(m'/g)` has fewer than `g(Z/X+1)` values. Equal labels and the collision
congruence force equal column pairs. Only differences divisible by `g` occur.
Summing differences to `H` therefore costs at most `(Z/X+1)H`.

Products are at most `2XZ`, so a logarithmic window has
`H=floor(2XZδ)`. Smooth/rough uniqueness identifies the weighted diagonal;
the off-diagonal row weights sum to `‖r‖₁²`. The existing triangular Fourier
majorant transfers the collision bound without a harmonic logarithmic loss.

## Corpus inputs

Corpus comparison found the balanced gcd-fibre estimate, but no exact
rectangular cumulative statement. The rectangular integer census, weighted smooth/rough transfer, and actual
prime-power coefficient bound are formalized; every analytic input is discharged.

For fixed rows, split the weighted logarithmic collision sum into equal
products and the two strict orderings. Smooth/rough uniqueness identifies
equal products with equal rows and columns. Its total weight is exactly
`‖r‖₂²‖b‖₂²`. Each strict ordering has at most
`(Z/X+1) floor(2XZδ)` column pairs, each of column weight at most `K²`
when `|b|≤K`. Summing row weights gives `‖r‖₁²`.

At kernel width `1/(2πT)`, the proved triangular Fourier majorant gives
`(5π/2)T` times this logarithmic energy. Since
`T floor(2XZ/T)≤2XZ` and `X(Z/X+1)≤Z+X`, the displayed bound follows
with `K²` in place of `‖b‖∞²`. Arbitrary centers are unit coefficient twists.

For a prime tail supported below `Y`, its `k`th power is supported on rough
integers at most `Y^k`. The corpus proves its coefficient square sum at most
`k!(Σ|b|²)^k`. If `|b|≤1`, every power coefficient is at most `k!`: induction
on `k`, triangle inequality, and the proved bound of `k+1` for each
convolution fibre give `(k+1)k!`. Thus, writing `Z=Y^k`,

`∫_[−T,T]|R(U+t)|²|B(U+t)|^(2k)`
`≤(5π/2)(T‖r‖₂² k!(Σ|b|²)^k+4Z(X+Z)‖r‖₁²(k!)²)`.

Restriction to `|B|≥V`, `V>0`, divides this bound by `V^(2k)`.
This is a finite arithmetic moment inequality; it does not assert prime-density
savings or control an infinite tail at an exceptional return.

## Lean status

`SumProductArithmeticOfTheLogarithm/RectangularProductCollisions.lean` proves
`rectangularProductCollisionFiber_le_gcd`,
`cumulative_rectangular_collision_fiber_le`,
`rectangularUpperLogFiber_le_floor`, and
`rectangularOffDiagonalLogFiber_le_floor`. Direct source check passed; all
four capstones use only `propext`, `Classical.choice`, `Quot.sound`.
`TailArithmeticOfThePrimeOrbit/TheRectangularMomentsHaveAnArithmeticCost.lean`
proves `rectangularLogWeight_le`, `integral_rectangular_head_tail_le`,
`norm_powCoeff_le_factorial`, `integral_rectangular_head_prime_tail_pow_le`,
`setIntegral_rectangular_head_on_large_prime_tail_le`, and
`integral_rectangular_full_prime_tail_pow_le`.
Direct source check passed; all six capstones use only
`propext`, `Classical.choice`, `Quot.sound`.

Taking literal supports `A={X<m≤2X : m is y-smooth}` and
`B={y≤p≤Y : p prime}`, with all coefficients one, gives the same moment
bound with `‖r‖₂²=#A`, `‖r‖₁²=(#A)²`, and `Σ|b|²=#B`.
This specialization has no supplied smooth/rough or coefficient interface.

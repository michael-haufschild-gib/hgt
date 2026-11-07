# Arithmetic moments without a dyadic restriction on the smooth head

- **ID:** TAPO-unrestricted-head-arithmetic-moments
- **Stage:** 3-formalized
- **Type:** THEOREM

For arbitrary finite `y`-smooth head `A`, `y`-rough tail `B⊂[1,Z]`, and
`|b|≤K`, put `R_j=Σ|r_m|^j`, `M₁=Σm|r_m|`, `B₂=Σ|b_n|²`, and

`C(A,r,Z)=Σ_{m,n∈A}|r_m r_n| Z(2Z+m/gcd(m,n)+n/gcd(m,n))`.

Every center `U` and `T>0` satisfy

`∫_[−T,T]|R(U+t)|²|B(U+t)|²≤(5π/2)(T R₂ B₂+C(A,r,Z)K²)`.

The intrinsic cost satisfies `C≤2Z²R₁²+2ZR₁M₁`. For a prime tail below
`Y` with `|b|≤1`, its `k`th power has coefficient supremum `≤k!` and
squared coefficient sum `≤k!B₂^k`. Thus the head-weighted `2k`th moment is
at most `(5π/2)(T R₂ k!B₂^k+C(A,r,Y^k)(k!)²)`. Head mass on `|tail|≥V`
is bounded by this expression divided by `V^(2k)`. The literal full smooth
head below `M` and prime tail in `[y,Y]` satisfy the first-moment version.

## Proof

For positive rows `m,n`, put `g=gcd(m,n)` and `d=n/g`. A fixed product
difference has at most `floor(Z/d)+1` column labels; only differences
multiple of `g` occur. Through `H`, cumulative cost is at most
`(floor(Z/d)+1)floor(H/g)`. The larger ordered product is at most `nZ`,
so a positive logarithmic collision has difference at most `floor(nZ/T)`.
Using `T floor(H/g)≤dZ` and `d(floor(Z/d)+1)≤Z+d` gives oriented cost
`Z(Z+n/g)`. Reversing rows gives the displayed kernel.

Smooth–rough uniqueness identifies equal products with identical row and
column pairs, retaining the exact diagonal `R₂B₂`. Unequal products pay
the primitive collision count times `K²`; sum the nonnegative row weights.
Dropping the gcd saving gives the first-moment bound.

The triangular Fourier majorant at frequency `log(mp)/(2π)` and width
`1/(2πT)` bounds the physical mean square by `(5π/2)T` times actual weighted
logarithmic energy. Center shifts are unit coefficient twists. Actual
prime-tail powers are rough and supported below `Y^k`; substitution of
their proved coefficient bounds gives higher moments. On a large-tail
event, divide by `V^(2k)` and integrate.

## Lean

`SumProductArithmeticOfTheLogarithm/PrimitiveProductCollisionCosts.lean`
proves the primitive fibre, cumulative, logarithmic and height-scaled
collision bounds, with `primitiveProductCost` as the two-sided kernel.

`TailArithmeticOfThePrimeOrbit/TheSmoothHeadNeedsNoDyadicRestriction.lean`
proves:

- `integral_head_tail_le_logWeight`, `integral_head_tail_shift_le_logWeight`;
- `primitiveHeadCost_le_first_moment`, `scaled_rectangularLogWeight_le_primitive`;
- `integral_smooth_head_rough_tail_le_primitive`,
  `integral_smooth_head_rough_tail_le_first_moment`;
- `integral_smooth_head_prime_tail_pow_le_primitive`,
  `integral_smooth_head_prime_tail_pow_le_first_moment`;
- `integral_full_smooth_head_prime_tail_pow_le`;
- `setIntegral_smooth_head_on_large_prime_tail_le`.

Both production files passed direct Lean checks. All sixteen audited
capstones depend only on `propext`, `Classical.choice`, `Quot.sound`.
Both umbrellas include the modules.

The Fourier transfer belongs to broader RH work and uses positivity.
Prime-density savings, growing Euler-tail limits and control of infinite
signed tails at exceptional returns remain open.

# Arithmetic moments without a dyadic restriction on the smooth head

- **ID:** TAPO-unrestricted-head-arithmetic-moments
- **Stage:** 2-fully-proven; Lean verification in progress
- **Type:** THEOREM

For arbitrary finite smooth head `A`, rough tail `B⊂[1,Z]`, coefficients
`|b|≤K`, set `R₁=Σ|r_m|`, `R₂=Σ|r_m|²`, `M₁=Σm|r_m|`, `B₂=Σ|b_n|²`.
For every center `U` and `T>0`:

`∫_[−T,T]|R(U+t)|²|B(U+t)|²`
`≤(5π/2)(T R₂ B₂+2Z²R₁²K²+2Z R₁M₁K²)`.

For fixed ordered rows `m,n>0`, quotient labels need only
`(floor(Z/n)+1)g` values, where `g=gcd(m,n)`. Summing compatible differences
removes `g`. The positive product ordering has maximum product `nZ`, so its
logarithmic cutoff is `floor(nZδ)`. At `δ=1/T`, its scaled cost is at most
`Z(Z+n)`. The reverse ordering costs at most `Z(Z+m)`.
Summing weighted rows gives the displayed first-moment expression.

This removes the dyadic-head restriction and improve the rectangular
constant. Actual prime-tail powers then use `Z=Y^k`, supremum `k!`, and the
proved factorial coefficient-square bound. Every arithmetic and Fourier input
must be proved or discharged before publication; no estimate at an exceptional
infinite tail follows from this finite mean value.

The primitive-step version is stronger. Put `g=gcd(m,n)`
and `d=n/g`. The label `p/d` has only `floor(Z/d)+1` values, so cumulative
fibres cost at most `(floor(Z/d)+1)floor(H/g)`. With `H=floor(nZ/T)`,
`T floor(H/g)≤dZ` and `d(floor(Z/d)+1)≤Z+d`. The oriented cost is therefore
`Z(Z+n/g)`. Both orientations retain the kernel
`Z(2Z+(m+n)/g)`, stronger than the first-moment envelope above.

Formalization should expose a reusable analytic transfer from arbitrary
positive-support head/tail polynomials to their actual weighted log-energy;
subsequent arithmetic refinements can then reuse the Fourier argument.

## Dependency-closed transfer

Smooth/rough uniqueness identifies equal product frequencies with equal row
and column pairs, retaining `R₂B₂`. For unequal products, the two oriented
counts above bound the weighted column sum by `K²` times their cardinality.
Summing `|r_m r_n| Z(2Z+m/g+n/g)` gives the intrinsic arithmetic cost.
Since `g≥1`, this is at most `2Z²R₁²+2ZR₁M₁`.

The proved triangular Fourier majorant, at frequency `log(mp)/(2π)` and
width `1/(2πT)`, bounds the physical mean square by `(5π/2)T` times actual
weighted log-energy. Center shifts are unit coefficient twists. Applying the
primitive-step census proves both the intrinsic and first-moment bounds.

Every actual prime-tail power is rough, supported below `Y^k`, with the
proved supremum `k!` and squared coefficient sum `k!B₂^k`; substitution gives
all higher moments. On `|B|≥V`, divide by `V^(2k)` and integrate, giving the
corresponding large-tail head-mass bound. No additional analytic input remains.

## Lean status

`SumProductArithmeticOfTheLogarithm/PrimitiveProductCollisionCosts.lean` proves
`rectangularProductCollisionFiber_le_primitive`,
`cumulative_rectangular_collision_le_primitive`,
`rectangularUpperLogFiber_le_primitive`,
`mul_card_rectangularUpperLogFiber_le_primitive`,
`mul_card_rectangularOffDiagonalLogFiber_le_primitive`, and
`primitiveProductCost_le`. Direct source check passed; all six capstones use
only `propext`, `Classical.choice`, `Quot.sound`.
The weighted analytic transfer and unrestricted prime-tail moments remain
under Lean verification.

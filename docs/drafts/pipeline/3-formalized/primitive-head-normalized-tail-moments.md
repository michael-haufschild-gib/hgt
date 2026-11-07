# Normalize arithmetic tail moments by the actual head mass

- **ID:** TAPO-primitive-head-normalized-moments
- **Stage:** 3-formalized
- **Type:** THEOREM

For a finite positive head support `A`, define
`H(A)=max(1,max_{m,n∈A} m/gcd(m,n))`.
The all-center lower bound is
`∫_[−T,T]|R(U+t)|²≥(2T−52H(A))Σ|r_m|²`, followed by normalized
prime-tail moments with the unrestricted primitive collision error.

Dividing both integers by their gcd preserves their logarithmic difference.
The integer gap then gives separation `1/H(A)`. The proved
`HTGeometry.interval_integral_normSq_expSum_ge` supplies the lower bound.
This uses the broader RH corpus's Hilbert inequality; it belongs in TAPO,
not the restricted sum-product programme.

For the tail conclusions, take `A` to be `y`-smooth and `B` a finite set of
primes in `[y,Y]`, with `|b|≤1`. Write `R_j=Σ|r_m|^j`, `B₂=Σ|b_p|²`, and
`C(A,r,Z)=Σ_{m,n∈A}|r_m r_n|Z(2Z+m/gcd(m,n)+n/gcd(m,n))`.
Normalization means division by the actual integral of `|R|²`.

At `T≥52H(A)` and nonzero head coefficient energy, the normalized
`2k`th moment is at most
`(5π/2)(k!B₂^k+C(A,r,Y^k)(k!)²/(T R₂))`, where `C` is the primitive head
cost. A matching normalized large-tail bound divides by `V^(2k)`.
The same primitive support scale controls both normalization and arithmetic
cost: `C(A,r,Z)≤2Z(Z+H(A))R₁²`. Thus the normalized error is
`≤2Y^k(Y^k+H(A))R₁²(k!)²/(T R₂)`.

These are finite upper bounds. Gaussian limit laws, growing Euler-tail
limits and exceptional-return exclusion remain open.

## Dependency-closed proof

For positive distinct `m,n`, put `g=gcd(m,n)`. The positive integers `m/g`
and `n/g` are distinct and at most `H(A)`. Cancelling `log g` and applying
the proved integer logarithmic gap gives `|log m−log n|≥1/H(A)`.
The actual frequencies `log m/(2π)` therefore have spacing
`D=1/(2πH(A))`. The corpus's Montgomery–Vaughan lower bound has error
`26/(πD)=52H(A)` on an interval of length `2T`. A center shift changes
only coefficient phases. At `T≥52H(A)`, actual head mass is at least
`T R₂>0`.

Every row kernel is
`Z(2Z+m/g+n/g)≤2Z(Z+H(A))`. Summing the nonnegative coefficient weights
bounds `C(A,r,Z)` by `2Z(Z+H(A))R₁²`. The already proved unrestricted
prime-tail moment and large-event bounds can now be divided by actual
positive head mass. Their numerators are nonnegative. Replacing the
denominator by `T R₂` proves the displayed estimates.

Multiplying every head index by the same positive integer preserves every
reduced ratio: `gcd(am,an)=a gcd(m,n)`. Hence `H(aA)=H(A)`. This scale
has no artificial common-factor inflation.

For literal `A={1≤m≤M:m is y-smooth}`, `M≥1`, unit coefficients give
`R₂=R₁=#A>0` and `H(A)≤M`. For literal prime tail `B={y≤p≤Y:p prime}`,
the normalized `2k`th moment, for every center and `T≥52M`, is at most
`(5π/2)(k!#B^k+2Y^k(Y^k+M)#A(k!)²/T)`.
This specialization discharges smoothness, primality, support and coefficient
inputs. It requires no estimate for the number of primes.

## Lean

`SumProductArithmeticOfTheLogarithm/PrimitiveLogarithmicSeparation.lean`
proves `primitiveSupportHeight_le`, `log_sub_log_eq_primitive`,
`inv_primitiveSupportHeight_le_abs_log_sub_log`,
`primitiveProductCost_le_supportHeight`, and `primitiveSupportHeight_image_mul`.

`TailArithmeticOfThePrimeOrbit/TheNormalizedMomentsRetainTheArithmeticCost.lean`
proves:

- `primitiveHeadCost_le_supportHeight`;
- `integral_head_sq_ge_primitiveSupportHeight`, `integral_head_sq_ge_height_energy`;
- `normalized_prime_tail_moment_le_primitive`,
  `normalized_prime_tail_moment_le_supportHeight`;
- `normalized_large_prime_tail_mass_le`;
- `normalized_full_smooth_prime_tail_moment_le`.

Both production files passed direct Lean checks. All twelve audited
capstones depend only on `propext`, `Classical.choice`, `Quot.sound`.
Both modules are wired into their programme umbrellas.

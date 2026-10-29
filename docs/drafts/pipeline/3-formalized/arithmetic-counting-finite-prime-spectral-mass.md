# Finite prime flips have unit arithmetic conductor mass

- **ID:** ACP-FINITE-PRIME-SPECTRAL-MASS
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean audited)
- **Parent:** arithmetic-counting-finite-prime-secular-gap.md
- **Statement:** The normalized Möbius coefficients of a finite-prime flip have squared sum one, supported exactly on the positive integers whose prime factors belong to the flipped set.

## Arithmetic data

Let F be a finite set of primes, omega_F its completely multiplicative sign,
and c_F=prod_(p in F)(p-1)/(p+1). Extend omega_F to an arithmetic function
f_F by setting its value at zero to zero. Put b_F=f_F*mu and

`a_F(m)=c_F b_F(m)/sqrt(phi(m))`,

with the zero term interpreted as zero. These are the coefficients required
by the finite-set harmonic Ramanujan count. Their identification with actual
eigenline coordinates is a separate bridge, not a premise of this result.

## Closed proof

Both f_F and mu are multiplicative, hence so is b_F. The divisor formula is
`b_F(m)=sum_(d|m) mu(m/d) omega_F(d)`; the sum at m=0 is empty.
At a prime power p^(k+1), convolution with mu is the difference
`f_F(p^(k+1))-f_F(p^k)`. It equals `2(-1)^(k+1)` if p is in F and zero
otherwise. At one its value is one.

The square b_F(m)^2 is multiplicative. Its values at every positive prime
power are four on F and zero outside F. Unique prime factorization therefore
gives

`b_F(m)^2=prod_(p|m) (if p in F then 4 else 0)` for m>0.

Consequently its support consists exactly of the F-supported positive
integers. On that support it is `4^omega(m)`, where omega counts distinct
prime factors. In particular this is a finite product, not an assertion of
independence of the finite-horizon arithmetic coordinates.

Write w_F(m)=b_F(m)^2/phi(m). Totient multiplicativity makes w_F multiplicative.
Its local positive-power series, for p in F, is

`sum_(k>=0) w_F(p^(k+1))
 = (4/(p-1)) sum_(k>=0) p^(-k)
 = 4p/(p-1)^2`.

For p outside F the same tail is zero. All terms are nonnegative and each
prime-power series converges. The finite Euler-product theorem therefore
gives, including its summability assertion,

`sum_(m F-supported) w_F(m)
 = prod_(p in F)(1+4p/(p-1)^2)
 = prod_(p in F)((p+1)/(p-1))^2
 = 1/c_F^2`.

The Euler-product input asks only for the local summability just proved;
global summability is a conclusion. The coefficient identity
`a_F(m)^2=c_F^2 w_F(m)` follows from the square-root identity for the
nonnegative totient. Multiplying the Euler sum by c_F^2 gives unit mass.
The zero coefficients outside the supported set extend the sum to all
natural conductors. This includes F empty: only conductor one survives.

## Scope and reuse

The finite Euler factorization and generalized Liouville signs are classical;
the parent card records the source audit. This leaf supplies the explicit
unit-mass input for transferring a finite-set constraint to the entire actual
prime spectrum. It does not assert the joint optimal gap or any infinite-set
limit. No numerical approximation or unproved analytic input enters the proof.

Reuse the corpus prime-power Möbius convolution lemma and Mathlib's
`EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum`.
Do not reprove the general Euler-product machinery.

## Formalization

Source: `formal/GaloisForLFunctions/ArithmeticCountingPositivity/FinitePrimeFlipsHaveUnitConductorMass.lean`.

Eight public endpoints:

- `finiteFlipMobius_isMultiplicative`
- `finiteFlipMobius_eq_divisor_sum`
- `finiteFlipMobius_prime_pow`
- `finiteFlipMobius_sq_eq_prod`
- `finiteFlipSpectralWeight_eq`
- `hasSum_finiteFlipSpectralWeight_supported`
- `finiteFlipConductorCoefficient_sq`
- `hasSum_finiteFlipConductorCoefficient_sq`

Scratch check 67333 and canonical source check 67876 exited zero without
diagnostics. Every transitive axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`. The adjacent audit preserves commands,
source hash and actual output. Umbrella and foundational README are wired;
no umbrella was compiled. Owned scratch/check logs are cleaned.

- [x] Dependency-complete paper proof.
- [x] Concrete Lean coefficients, support and unit-mass identity.
- [x] Transitive axiom audit, canonical source check, wiring and cleanup.

# Polynomial orbit preservers force affine prime clocks

- **ID:** alst-orbit-preserving-endomorphisms-are-adams
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** Let `P` contain at least two distinct primes. Every complex polynomial self-map sending the prime orbit into itself has coordinates `X_p↦p^(−ib) X_p^n` for unique `n∈ℕ`, `b∈ℝ`. Its induced clock is `t↦nt+b`, without any assumed regularity. Over `ℤ`, necessarily `b=0`, so the maps are exactly Adams operations.

## Research consequence
This would classify every exact polynomial Frobenius candidate preserving
the prime orbit, rather than assuming a dilation clock. Every nonidentity
such map has at most one fixed orbit point; nontrivial translations have none.
Thus a Frobenius accounting for many prime-orbit fixed points would have
to change the auxiliary algebra or use correspondences instead of maps.
The positive result is the full semigroup classification, not a bound.

## Proposed proof
Each generator image has modulus one along the prime orbit. For a finite
exponential sum of constant modulus, the largest frequency in its squared
modulus is the difference of the largest and smallest support frequencies.
That coefficient has a unique contributing pair and is nonzero. Fourier
uniqueness therefore forces singleton support. Each generator image is a
monomial times a unit complex scalar.

The image of time zero supplies `b`, and subtracting this time translation
normalizes all scalar factors to one. Monomial images then make the
normalized clock additive, using injectivity of the prime orbit. One
coordinate says that its difference from a linear clock takes values in
a discrete period lattice. An additive map from the divisible group `ℝ`
into that lattice is zero. Thus the clock is `t↦a t+b`, and every `p^a`
is a positive integer.

The exponent matrix stabilizes the nonzero finite integer span of the prime
logarithms under multiplication by `a`. The determinant trick therefore
makes `a` integral over `ℤ`. Baker independence of prime logarithms over
real algebraic coefficients forces that matrix to be `aI`, hence `a∈ℕ`. Over `ℤ`, the scalar factors are signs; absence of nonzero
common torsion returns forces `b=0`. Equality on generators identifies
all maps, and the stated maps explicitly preserve the orbit.

## Formalization status
`FiniteUnitSpectrum.finiteExpWave_unit_support` passes Lean with standard
axioms only. Polynomial restriction, additive-clock rigidity, the finite
prime-lattice multiplier theorem, and the final classification are under
formalization. Baker's `RHTower.primeLog_algIndep` supplies the required
algebraic-coefficient independence; its transitive axiom audit contains
only `propext`, `Classical.choice`, and `Quot.sound`.

The full classification and fixed-point consequences remain unverified
and uncounted. Initial corpus searches found no matching classification.

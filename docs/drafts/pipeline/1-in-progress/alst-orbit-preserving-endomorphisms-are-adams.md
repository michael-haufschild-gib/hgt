# Polynomial orbit preservers force affine prime clocks

- **ID:** alst-orbit-preserving-endomorphisms-are-adams
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** Let `P` contain at least three distinct primes. Every complex polynomial self-map sending the prime orbit into itself has coordinates `X_p↦p^(−ib) X_p^n` for unique `n∈ℕ`, `b∈ℝ`. Its induced clock is `t↦nt+b`, without any assumed regularity. Over `ℤ`, necessarily `b=0`, so the maps are exactly Adams operations.

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

Six exponentials, applied to three independent prime logarithms and
`(1,a)`, forces `a∈ℚ`. Clearing denominators and using prime factorization
forces `a∈ℕ`. Over `ℤ`, the scalar factors are signs; absence of nonzero
common torsion returns forces `b=0`. Equality on generators identifies
all maps, and the stated maps explicitly preserve the orbit.

## Corpus inputs and open obligations
`RHTower/SixExponentials/PrimePowers.lean` proves independence of three
prime logarithms and applies six exponentials to prime powers. ALST
supplies absence of common torsion returns, frequency injectivity, and
Adams operations. Initial searches found no matching orbit-preserver
classification. Constant-modulus rigidity, clock rigidity, rational-to-
integral descent, novelty, and transitive dependencies require audits.
Nothing is proved or counted here.

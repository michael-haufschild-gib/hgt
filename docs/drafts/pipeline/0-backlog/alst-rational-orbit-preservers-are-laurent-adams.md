# Rational orbit preservers are Laurent Adams operations

- **ID:** alst-rational-orbit-preservers-are-laurent-adams
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Statement:** For a finite prime set containing two distinct primes, every rational self-map defined on the entire prime orbit and carrying that orbit into itself has coordinates `p^(−ib)X_p^n`, with a common `n∈ℤ`, `b∈ℝ`. Over real or integer coefficients, `b=0`.

## Research consequence
Polynomial rigidity leaves arbitrary denominators as a possible escape.
This would classify that entire escape: denominators permit time reversal
but no nonlinear clock or nonidentity map fixing two orbit points.
A counterexample would instead supply a new exact orbit mechanism.

## Proposed mechanism
For the prime derivation `D=Σ log(p)X_p∂_p`, orbit preservation should force
`log(q) D(F_p)/F_p = log(p) D(F_q)/F_q`. A local argument lift in one
coordinate differs from the selected clock by an integer period. The other
coordinate turns this difference into a continuous function with countable
image, forcing local constancy. No clock regularity is assumed.

At a noninvariant irreducible divisor, logarithmic derivatives have integer
residues. The displayed identity and irrationality of `log(p)/log(q)` force
both orders to vanish. Every irreducible polynomial invariant under `D`
should be a coordinate: `D(H)=aH` follows from degree, and distinct prime
frequencies force singleton support. Thus all coordinates are Laurent
monomials. The finite prime-logarithm lattice then forces a common integer
exponent, and the already established clock argument supplies translation.

## Corpus leads and gaps
`HTGeometry/RationalDiagonalDerivation.lean` constructs the polynomial and
fraction-field derivations. `RationalPolarCalculus.logDerivRat_residue`
proves the one-variable integer-residue law.
`PolynomialPhaseCharacterRankAperture.support_diagonalPolynomialDerivation_subset`
provides support preservation. The multivariate divisor
argument, local clock lifting, and assembly require proofs and novelty
audits. No theorem from this conjecture is proved or counted.

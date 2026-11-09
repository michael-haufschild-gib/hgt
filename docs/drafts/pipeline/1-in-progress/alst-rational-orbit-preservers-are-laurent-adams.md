# Rational orbit preservers are Laurent Adams operations

- **ID:** alst-rational-orbit-preservers-are-laurent-adams
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** For a finite prime set containing two distinct primes, every rational self-map defined on the entire prime orbit and carrying that orbit into itself has coordinates `p^(−ib)X_p^n`, with a common `n∈ℤ`, `b∈ℝ`. Over real or integer coefficients, `b=0`.

## Research consequence
Polynomial rigidity leaves arbitrary denominators as a possible escape.
This would classify that entire escape: denominators permit time reversal
but no nonlinear clock or nonidentity map fixing two orbit points.
A counterexample would instead supply a new exact orbit mechanism.

## Proposed mechanism
Write each coordinate as `N_p/D_p`, with denominator nonzero on the orbit.
Locally normalized logarithms satisfy
`log(q) log(F_p(t)/F_p(t₀)) − log(p) log(F_q(t)/F_q(t₀)) ∈ S`,
where `S` is the countable image of `ℤ²` coming from logarithm periods.
Continuity on a small interval forces this difference to be constant.
Differentiation gives proportional logarithmic derivatives without assuming
regularity of the selected clock.

The entire exponential polynomials obtained by substituting `X_p=p^(−s)`
then satisfy the cleared differential identity everywhere. Integer residues
and irrational prime-log ratios force numerator and denominator to have
the same zero divisor. Their entire nonvanishing quotient is exponential
affine by order-one rigidity. Bohr coefficient extraction identifies its
frequency as a difference of two monomial frequencies. The signed
prime-logarithm lattice then forces the common clock slope to be an integer.
The conclusion is a polynomial cross-multiplication identity, so common
factors require no coprimality assumption.

## Corpus leads and gaps
The corpus supplies `logDeriv_residue_of_meromorphicOrder`,
`EntireQuotient.exists_entire_nonvanishing_quotient`, and
`OrderOneRigidity.exists_expAffine_of_entire_quotient`; their transitive
axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
Mathlib proves countable metric subsets totally disconnected.
Local logarithmic rigidity, analytic continuation, the divisor comparison,
growth verification, frequency extraction, and signed lattice assembly
remain to be formalized. No theorem from this conjecture is counted.

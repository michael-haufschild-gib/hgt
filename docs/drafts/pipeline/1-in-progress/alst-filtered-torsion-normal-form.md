# Filtered normal form for full torsion multiplicity

- **ID:** alst-filtered-torsion-normal-form
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** The integer polynomials of length at most `N` with full multiplicity `r` on the order-`q` torsion grid have the integral basis
  `u^(a mod q) ∏_p (u_p^q−1)^(a_p div q)`, indexed by `weight(a) ≤ N` and `Σ_p floor(a_p/q) ≥ r`.

## Mathematical purpose
Determine the complete space of admissible Stepanov auxiliaries at every length, beyond its first nonzero member. The basis would make the filtered rank an exact arithmetic count and distinguish full torsion multiplicity from mere fibre cancellation. This is S1/S3 on the whole torsion locus; no zeta-specific input.

## Proof route
A maximal arithmetic-weight monomial is also coordinatewise maximal. Fourier–Euler extraction at its residue and quotient kills all other terms: an exponent with the same residue and dominating quotient must dominate the original exponent, hence cannot have smaller arithmetic weight. Multiplicity therefore forces the top quotient order to be at least `r`. Subtract its coefficient times the displayed basis element. Its lower terms have strictly smaller arithmetic weight, and it belongs to every point-ideal power `r`. Strong induction on length gives spanning; triangular top coefficients give independence and integral uniqueness.

## Gates
- [ ] Corpus novelty audit.
- [ ] Complete paper proof and formal statement.
- [ ] Lean proof and axiom audit.

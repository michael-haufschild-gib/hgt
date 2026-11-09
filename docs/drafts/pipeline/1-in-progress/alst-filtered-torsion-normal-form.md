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
- [x] Corpus novelty audit: existing residue Newton detection gives the strict support threshold, not the filtered integral kernel or unique expansion.
- [x] Complete paper proof: leading-weight elimination spans over integers; triangular top coefficients prove independence. Zero polynomial, empty prime set, `r=0`, and arbitrary `N` are included; `q>0`.
- [ ] Lean proof and axiom audit.

## Exact parameterization
For every `q>0`, `r,N≥0` and integer polynomial `F`, the conjunction of
`length(F)≤N` and full torsion multiplicity `r` is equivalent to a unique
finitely supported integer array `c` such that `F=Σ_a c_a B_a`, with every
nonzero `c_a` satisfying both `weight(a)≤N` and `Σ_p floor(a_p/q)≥r`.
Each `B_a` has leading coefficient one at `a` and length exactly `weight(a)`.
Thus the representation is integral, unique, and preserves every arithmetic cutoff.

## Integral ideal consequence
Let `J = (u_p^q−1 : p∈P)` in `ℤ[u_p]`. Full complex torsion multiplicity
`r` is exactly membership in `J^r`: each admissible Newton polynomial lies
in `J^r`, while each generator maps into every complex torsion point ideal.
The expansion therefore proves integral descent of the full multiplicity
condition, without denominators or an additional saturation hypothesis.

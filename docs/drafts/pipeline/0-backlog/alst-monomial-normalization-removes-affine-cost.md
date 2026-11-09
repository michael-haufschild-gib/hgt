# Monomial normalization of the polynomial Stepanov image

- **ID:** alst-monomial-normalization-removes-affine-cost
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Statement:** For `q≥2`, `I=(X_p^q−X_p)` and `J=(X_p^(q−1)−1)` over `ℤ`, the coefficient-one monomials `M=X^a` normalizing the order-`r` images satisfy
  `M·J^r⊆I^r ↔ (∏_p X_p^r) divides M`.
  Moreover `M F∈I^r ↔ F∈J^r` for every such `M`.

## Purpose
Polynomial syzygies force zeros on coordinate hyperplanes as well as on
the fixed torus. Multiplying a Dirichlet polynomial by a monomial changes
absolute length but has unit modulus on the prime torus. Exact monomial
division may therefore recover every torsion auxiliary from polynomial
syzygies. This tests whether the affine cost is intrinsic to the method
or depends on its polynomial normalization.

## Proposed mechanism
Each affine generator is `X_p` times its torus generator. Multiplication
by `∏ X_p^r` converts every product of `r` torus generators into an affine
ideal-power element. Conversely, each `X_p` is invertible modulo `J^r`:
`X_p^(q−1)=1+H_p`, and the finite geometric series in `−H_p` inverts
`1+H_p` modulo `J^r`. Thus `J^r` is saturated under monomials.

For necessity, specialize all other coordinates to `1`. The image ideal
becomes `(X_p^q−X_p)^r`. Testing the torus generator `H_p^r`, whose constant
term is a unit, should force the exponent of `X_p` in `M` to be at least
`r`. This must be proved over the integers, including `r=0` and empty prime
support. Corpus searches found general saturation constructions but no such normalization theorem. All proof obligations remain open.

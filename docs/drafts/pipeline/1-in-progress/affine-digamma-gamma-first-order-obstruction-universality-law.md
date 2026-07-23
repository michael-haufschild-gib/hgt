# Affine digamma-after-Gamma first-order obstruction universality law

Status: paper proof complete; Lean source complete; exact audit deferred until terminal parent modules
receive final module builds.

## Lean sources

- `not_differentiallyAlgebraicOfOrder_one_digamma_comp_Gamma`
- `differentiallyAlgebraicOfOrder_comp_const_mul_iff_uncond`
- `differentiallyAlgebraicOfOrder_comp_add_const_iff`

## Survivor

For every `a ≠ 0` and every complex `b`, the function
`z ↦ digamma (Gamma (a z + b))` satisfies no algebraic differential equation of order at most one
with complex polynomial coefficients. Thus the vanishing-residue pole-cluster obstruction is a law
of the entire invertible affine orbit, not one distinguished coordinate.

## Proof skeleton

Assume an order-one equation after affine precomposition. Fixed-order nonzero scaling invariance
removes `a`, then translation invariance removes `b`, contradicting the reciprocal-Gamma cluster
obstruction for `digamma ∘ Gamma`.

## Novelty audit

Pending post-formalization literature search.

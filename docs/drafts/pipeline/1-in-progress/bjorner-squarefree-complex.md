# Björner's squarefree complex

- **Stage:** 1-in-progress
- **Target:** For `N ≥ 2`, the prime-support complex is homotopy equivalent to a wedge
  with one sphere of dimension `ω(m) − 1` for each odd squarefree `N/2 < m ≤ N`.
  Consequently its integral reduced homology is free, with those sphere counts as ranks.

## Existing arithmetic and chains

`RHTower.primeSets N` consists of prime sets with product at most `N`, including the
empty face. `sum_primeSets_neg_one_pow` identifies its alternating face count with
the Mertens sum. `PrimeProductCutoffContraction` supplies the literal exterior-chain
boundary, its square-zero law, and contraction by adjoining prime two at doubled cutoff.

## Decomposition at prime two

Let `A` consist of faces `S` for which `insert 2 S` remains a face. It is the star of
vertex two, hence a cone. Faces outside `A` are exactly odd prime sets with product
in `(N/2, N]`. Every proper subface lies in `A`: deleting a prime `p ≥ 3` divides
the product by at least three, so adjoining two keeps it below `N`.
Thus every complementary face is a facet attached to `A` along its entire boundary.

The required topological step is the homotopy equivalence obtained by collapsing the
contractible star, identifying the quotient with the wedge of those simplex-boundary
quotients. This step and the resulting integral homology calculation remain unformalized;
an alternating face count alone does not establish either claim.

An explicit extension of the star contraction avoids a general cofibration theorem.
On a complementary simplex with `k` vertices, write `x = r b + (1-r)y`, where `b` is
its barycenter, `r = k minᵢ xᵢ`, and `y` lies on its boundary. Put `rₜ = (1+t)r-t`.
For `rₜ ≥ 0`, use `rₜ b + (1-rₜ)y`; for `rₜ ≤ 0`, use
`(-rₜ)e₂ + (1+rₜ)y`. The formulas agree at `rₜ = 0` and restrict on the boundary
to `(1-t)y + t e₂`. The barycenter stays fixed; the formula involving `y` is only
needed away from it. At `t=1` the entire star is collapsed. Quotient descent of this
homotopy supplies the inverse up to homotopy of the collapse map.

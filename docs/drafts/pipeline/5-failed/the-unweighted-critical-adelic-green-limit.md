# The unweighted critical adelic Green limit vanishes

- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Obstacle:** B133.
- **Retired claim:** The critical single-point Green kernels for the
  unweighted sums of finite-place adjacency operators have a nonzero
  limit under exhaustion of the primes.

## Exact obstruction

For every finite nonempty place set `S`, every `p∈S`, and all vertices,
`0≤G_S(x,y)≤√p/(p−1)≤2/√p`. Thus `G_S` converges uniformly to zero
along the directed finite subsets of primes, including on the diagonal.
This excludes precisely the unrenormalized unweighted limit.

## Strongest positive survivor

The [finite-product construction](../3-formalized/the-critical-green-kernel-on-finite-adelic-products.md)
gives a convergent occupation series at `λ_S=Σ_{p∈S}2√p`, the exact
single-point equation `(λ_S−Σ_{p∈S}A_p)G_S=δ`, and minimality among
all nonnegative supersolutions without a growth assumption. Its diagonal
satisfies `1/λ_S≤G_S(x,x)`, and its full kernel has an explicit product
bound obtained from the coordinate-hyperplane sources of the local product.

## New insight and status

Local critical Green kernels do produce a genuine inverse of the summed
operator at every finite stage. The obstruction occurs in passing to
infinitely many places: nonzero diagonal mass requires additional
normalization or a different operator. Neither option supplies Weil's
diagonal or quotient descent by itself.

The construction and collapse have complete paper proofs and Lean
formalizations in `TheCriticalGreenKernelOnFiniteAdelicProducts.lean`
and `TheUnweightedAdelicGreenKernelCollapses.lean`. Plain checks passed;
the ten displayed axiom audits use only the three standard axioms.

# The critical Green kernel on finite adelic products

- **ID:** the-critical-green-kernel-on-finite-adelic-products
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** B133; actual finite-place adjacency and minimal local Green kernels.
- **Target:** Construct the least nonnegative single-point Green kernel for the
  sum of adjacency operators on every nonempty finite product of prime trees,
  at the sum of their local tempered parameters.

## Construction

Let `I` be finite and nonempty, with a prime `p_i` at each coordinate.
On `V=Π_i LocalVertex(p_i)`, let `A=Σ_i A_i` and `λ=Σ_i 2√p_i`.
For vertices `x,y`, define

`G(x,y)=Σ_{n≥0} λ^(−n−1)(A^n δ_x)(y)`.

This series converges, solves `(λ−A)G(x,·)=δ_x`, and is the
least nonnegative supersolution. Its quantitative bound is

`G(x,y)≤Π_i g_i(x_i,y_i) / Σ_i Π_{j≠i}g_j(x_j,x_j)`,

where `g_i` is the already constructed critical local Green kernel.

## Proof

The product `K=Π_i g_i` satisfies the exact source identity

`(λ−A)K(x,y)=Σ_i 1_{x_i=y_i}Π_{j≠i}g_j(x_j,y_j)`.

Its source is nonnegative and at `y=x` equals the positive denominator
of the proposed bound. Scaling therefore supplies a global supersolution.
Write `T=A/λ`, `b=δ_x/λ`. For every nonnegative supersolution `u`,
`b≤u−Tu`, hence `Σ_{n<N}T^n b≤u−T^N u≤u`. Apply this first to the
scaled product to prove summability, then to arbitrary `u` to prove
minimality. Finite adjacency commutes with the convergent nonnegative
series, so `TG=Σ_{n≥1}T^n b=G−b`, giving the exact single-point source.
At the source, positivity of adjacency gives `λG(x,x)≥1`, hence
`1/λ≤G(x,x)`. Every finite-stage kernel therefore has a strictly positive
diagonal despite the infinite-place collapse below.

## Uniform collapse with infinitely many places

Every local critical kernel is at most its own diagonal. The denominator
in the product bound includes `Π_{j≠i}g_j(x_j,x_j)` for each `i`; therefore

`0≤G(x,y)≤g_i(x_i,x_i)=√p_i/(p_i−1)≤2/√p_i`.

For every `ε>0`, choose a prime `q` with `2/√q<ε`. Every finite place set
containing `q` then has `G(x,y)<ε` for all vertices, uniformly. Thus the
unweighted critical Green kernels converge uniformly to zero along the
directed finite subsets of all primes. The sum of local operators has a
minimal inverse at every finite stage, but its unrenormalized infinite-place
limit supplies no nonzero diagonal.

## Boundary

This is a single-point inverse of the sum of local operators, rather than
the sum of prime-fibre inverses. A nonzero infinite-place normalization,
separate arithmetic quotient descent and comparison with Weil's diagonal
remain additional questions. The positive survivor is the finite-place
single-source kernel, its minimality and its quantitative product bound.
No revival of the refuted torus-invariant gluing is claimed.

## Lean verification

Namespace `GaloisForLFunctions.HyperbolicArakelovTheory.FiniteProductGreen`:

- `TheCriticalGreenKernelOnFiniteAdelicProducts.lean`:
  `productKernel_source`, `summable_occupation`, `green_source`,
  `green_isLeast`, `green_le_product`.
- `TheUnweightedAdelicGreenKernelCollapses.lean`:
  `one_div_edge_le_green_self`, `green_le_local_diagonal`,
  `green_le_two_div_sqrt`, `cutoffKernel_uniform_zero`,
  `tendsto_cutoffKernel_zero`.

Both modules passed plain `lake --old env lean` checks without warnings.
All ten displayed axiom audits contain only
`[propext, Classical.choice, Quot.sound]`. Both modules are imported by
the Hyperbolic Arakelov Theory umbrella.

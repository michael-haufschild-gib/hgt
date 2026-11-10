# A weighted single-point Green kernel on the full adelic product

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** B133; finite-product Green construction and its unweighted collapse.
- **Statement:** On the actual restricted product of all prime vertices,
  `A=Σ_p p⁻² A_p` has a nonzero least nonnegative single-point Green kernel
  at `λ=Σ_p 2p⁻²√p`, constructed without an assumed analytic input.

## Proof [PROVED HERE]

Use the existing normalized critical product
`H(x,y)=Π_p p^(-d_p(x_p,y_p)/2)`, whose factors differ from one at
only finitely many places. With `c_p=(p−1)/√p`, its local source identity
gives `A_pH=(2√p−c_p 1_{x_p=y_p})H`: factor the restricted product
at `p`, apply the local unit-source equation, and note that the local
factor equals one when `x_p=y_p`. Every factor is positive, so `H>0`;
also `H(x,x)=1`.

The series `Σ_p 2p⁻²√p` converges by comparison with the natural-number
series of exponent `−3/2`. Since `0<c_p≤2√p`, the constant
`c=Σ_p p⁻²c_p` is finite and positive. The local identity yields

`(λ−A)H(x,y)=H(x,y) Σ_p p⁻²c_p 1_{x_p=y_p}`.

All series here converge absolutely: each weighted local adjacency
term lies between zero and `2p⁻²√p H(x,y)`. The source is nonnegative
and at `y=x` equals `c`. Hence `B_x=H(x,·)/c` is a supersolution for
the full-product unit point source. The same summable bound proves
that adjacency is defined on every nonnegative function below `B_x`.

Iterate `u₀=0`, `u_{n+1}=(δ_x+Au_n)/λ`. Positivity gives
`0≤u_n≤u_{n+1}≤B_x` by induction. Let `G(x,y)=sup_n u_n(y)`.
For each fixed `y,p`, the finite neighbour sum converges. Its weighted
value is bounded by `p⁻²A_pB_x(y)`, a summable majorant independent
of `n`. Dominated convergence over the primes therefore gives
`Au_n(y)→AG(x,·)(y)`. Passing to the limit in the recurrence proves
`(λ−A)G(x,·)=δ_x`, and also proves absolute convergence of the
adjacency sum for `G`.

For any nonnegative supersolution `v` in the domain of weighted
adjacency, induction gives `u_n≤v`; thus `G≤v`. The domain means
absolute convergence of the defining place sum at every vertex,
and is proved for `G`, not assumed as an analytic input. At the source,
`λG(x,x)=1+AG(x,·)(x)≥1`. Consequently

`1/λ≤G(x,x)≤1/c`, and `0≤G(x,y)≤H(x,y)/c`.

This constructs a nonzero single-point inverse on all restricted
adelic vertices, including pairs differing at arbitrarily many finite places.
Local adjacency is equivariant under the finite adelic group. The point
source, every iterate and hence the limiting kernel are invariant under
simultaneous translation of both vertices by that group.

The constant function has divergent adjacency at every vertex:
`Σ_p p⁻² A_p1 = Σ_p (p+1)/p² ≥ Σ_p 1/p = ∞`.
The last divergence is the prime reciprocal theorem. Thus the constructed
kernel's operator-domain membership comes from its spatial decay, even
though bounded constant functions do not belong to that domain.

## Boundary

This is a specified weighted operator, not the unweighted limit and not
an identification with Weil's diagonal. The arithmetic meaning of this
choice of weights and separate quotient descent remain open.

## Lean verification

Namespace `GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen`:

- `TheRestrictedGreenProductHasSummableSources.lean` proves
  `summable_edgeTerm`, `product_source`, `barrier_inDomain`, and `barrier_source`.
- `TheWeightedGreenKernelOnTheFullAdelicProduct.lean` proves
  `green_inDomain`, `tendsto_adjacency_partial`, `green_source`,
  `green_isLeast`, `green_self_bounds`, `green_self_pos`, `green_smul`,
  and `constant_row_not_summable`.

Both plain `lake --old env lean` checks passed without warnings.
All twelve displayed axiom audits contain only
`[propext, Classical.choice, Quot.sound]`. Both modules are imported by
the Hyperbolic Arakelov Theory umbrella.

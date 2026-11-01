# Renormalized Gauss–Mayer nuclear expansion

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [three approaches, A](../1-in-progress/argon-three-orthogonal-rh-approaches.md).
- **Input:** [actual cutoff regularization](gauss-mayer-renormalized-cutoff-operator.md).

Let `D={z:|z−1|≤3/2}`, let `A(D)` carry its supremum norm, and write
`L(w)` for the actual regularized Gauss–Mayer operator with exponent `w=2s`.
For `Re w>0`, `w≠1`, and `1<r<R<3/2`, put `q=r/R` and

`C(w,r)=|ζ(w)|+[2M(w)/(r−1)+(5/2)|w|M(w+1)] Σₙ≥1 n^(−Re w−1)`,

where `M(w)=2^(Re w) exp(π|Im w|)`. Let `αₖ,R` be the Cauchy coefficient
functional about `1` on radius `R`, and `eₖ(z)=(z−1)^k`. Then

`L(w)=Σₖ αₖ,R ⊗ L(w)eₖ`

in operator norm, with

`‖αₖ,R‖·‖L(w)eₖ‖ ≤ C(w,r)q^k`.

The first `N` terms have range in a subspace of dimension at most `N`, and

`‖Σₖ<N αₖ,R ⊗ L(w)eₖ − L(w)‖ ≤ C(w,r)q^N/(1−q)`.

For every real `p>0`, the same decomposition satisfies
`Σₖ(‖αₖ,R‖·‖L(w)eₖ‖)^p<∞`. Thus the concrete operator is nuclear of order
zero and compact throughout this half-plane, away from the scalar pole.

## Proof

Suppose `|f|≤A` on `|z−1|≤r`. The circle of radius `r−1` about any point
of `|z−1|≤1` stays in the radius-`r` disc. Cauchy's estimate gives
`|f′|≤A/(r−1)` there. Integrating along the segment from `0` to an inverse
branch point gives

`|f(1/(n+z))−f(0)| ≤ 2A/[(r−1)n]`.

The previously proved branch geometry and principal-power estimates give
`|(n+z)^(−w)|≤M(w)n^(−Re w)` and
`|(n+z)^(−w)−n^(−w)|≤(5/2)|w|M(w+1)n^(−Re w−1)`.
Splitting each branch remainder before estimating it therefore bounds it by

`A[2M(w)/(r−1)+(5/2)|w|M(w+1)]n^(−Re w−1)`.

Summing this convergent series and the scalar term `ζ(w)f(0)` proves the
local estimate `‖L(w)f‖≤C(w,r)A`.

The actual Cauchy integral is linear in `f` and has norm at most `R^(−k)`.
Since `|eₖ|≤r^k` on the smaller disc, the local estimate proves the geometric
rank-one bound. Taylor expansion and its geometric tail yield

`|Σₖ<N αₖ,R(f)eₖ(z)−f(z)|≤‖f‖q^N/(1−q)` for `|z−1|≤r`.

Applying the local operator estimate gives the stated operator-norm error.
The approximation's range lies in `span{L(w)eₖ:k<N}`, whose dimension is at
most `N`. Absolute convergence of the rank-one series and uniqueness of
operator-norm limits identify its sum with `L(w)`. Taylor convergence on the
outer boundary is not needed.

For `p>0`, raising the nonnegative product bound to `p` gives the summable
majorant `C(w,r)^p(q^p)^k`, since `0<q^p<1`. One fixed pair of radii,
`r=9/8`, `R=5/4`, supplies a single decomposition for all positive orders.
The existing Banach nuclear-operator compactness theorem then applies.

## Lean certificate

Module: `RenormalizedIntersectionTheory/GaussMayerNuclearExpansion.lean`.
Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNuclear`.

- `regularized_local_bound`: concrete operator controlled by a smaller-disc supremum.
- `nuclear_term_bound`, `hasSum_rankTerm`: geometric decomposition and actual operator identity.
- `approximation_finiteRank`, `approximation_error`: dimension and explicit error certificates.
- `nuclear_products_summable_rpow`, `nuclear_order_zero`: all positive real orders in one decomposition.
- `nuclear_regularized`, `compact_regularized`: existing Banach nuclearity interface and compactness.

Final direct `lake --old env lean` check passed. All eight public theorem
audits report only `propext`, `Classical.choice`, and `Quot.sound`.
Umbrella import is wired; no umbrella build was run.

## Scope

The corpus supplied Cauchy coefficients, Taylor expansion, Banach nuclearity
and the actual cutoff regularization. The new bridge proves the local
seminorm estimate and identifies an order-zero nuclear expansion of that
specific operator. No literature-novelty claim is made.

Lean's totalized definition also has a nuclear value at `w=1`; this is not a
claim that the meromorphic family is regular there. The [actual global
Fredholm determinant and its spectral criterion](gauss-mayer-source-fredholm-determinant.md)
are also certified. Selberg/scattering comparison and source-specific exclusion
of off-critical resonances remain separate obligations. Compactness alone does
not exclude eigenvalues.

# Critical boundary graphs in every exterior degree

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md)

## Exact arithmetic statement

Let `H_k=ℓ²({prime faces of cardinality k};ℂ)`. Embed the original finite-support
exterior chains using squared face norm `∏_(p∈S)p^δ`, and retain their original
Dirichlet boundary `d_s(e_p)=p^(−s)`. Write `G_k(δ,s)` for the graph of that
boundary in `H_(k+1)×H_k`. For every degree, including the augmented degree,

`2 Re(s)+δ≤1  ⇒  closure G_k(δ,s)=H_(k+1)×H_k`.

The graph uses the union of all conductor cutoffs. A fixed finite cutoff
has a finite-dimensional closed graph and is not covered by this conclusion.
The theorem preserves the actual chain embedding, orientation and boundary.

## Proof

Conductor normalization identifies the graph with the unweighted graph at
`z=s+δ/2`. Put `b_p=p^(−z)`. Suppose continuous linear functionals `φ,ψ`
annihilate this graph: `φ(a)+ψ(d_z a)=0` on embedded finite chains.

Fix an increasing `k`-face `S=(s₀,…,s_(k−1))` and append a prime `p`
larger than every vertex. Its exact oriented boundary gives

`b_p ψ(e_S)=(-1)^(k+1)[φ(e_(S∪{p})) + Σ_(j<k)(-1)^j b_(s_j) ψ(e_((S\{s_j})∪{p}))]`.

For each fixed old face, the appended faces are distinct canonical basis
vectors. Every continuous Hilbert functional therefore has square-summable
values on that tail. The right side is a finite sum of such sequences.
The prime sequence `b_p` is not square summable when `Re(z)≤1/2`, even
after deleting finitely many primes. Hence `ψ(e_S)=0`. This also treats
`k=0`, with an empty old-vertex sum. Every target basis coefficient vanishes,
so `ψ=0`; density of embedded finite chains then gives `φ=0`.
Hahn–Banach separation excludes a proper closed graph relation.

## Consequence and scope

The positive classification is the entire closed arithmetic relation,
stronger than a single nonzero vertical vector. Every source–target pair
is approximable by actual boundary pairs. On the normalized carrier the
closed relation has no remaining parameter distinction throughout this
critical region. A completed invariant retaining arithmetic information
must use additional domain, relative or equivariant structure.

This does not bound `Σ_p index_p(N)=1−M(N)`. The independent gluing-height
upper bound and the bounded-region exterior contraction remain open.

## Lean

- [PrimeExteriorTailCoordinates.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/PrimeExteriorTailCoordinates.lean):
  canonical tail faces, injectivity, square-summable observations, exact
  appended-face boundary and finite-deletion prime divergence.
- [PrimeExteriorGraphClosure.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/PrimeExteriorGraphClosure.lean):
  `primeExteriorBoundary_annihilator_eq_zero`,
  `primeExteriorBoundaryGraph_normalized`,
  `primeExteriorBoundaryRelation0_closure`,
  `primeExteriorBoundaryGraph_closure_eq_univ`.

Both modules pass direct `lake --old env lean` checks. Their twelve transitive
axiom audits use only `propext`, `Classical.choice` and `Quot.sound`.

# Curvature, fusion capacity, and the zeta divisor

**Status:** fully formalized in Lean 4 and audited. The capacity/finite-face/Euler-heat/continuous-reference/Mellin-divisor construction is at [the exact result](chronological-fusion-zeta-response.md); the join powers' sphere reading and the eta comparison are now Lean theorems too (see the Lean section below). No new-field or priority claim is established.

## Geometry supplies the energy spacing

For the cubic seed P=27ace+S(b+c+d)c, both displayed diagram terms individually have capacity one. Their sum has exact capacity K=`sixCapacity`>1, attained on the curved response arc. The coefficient normalization is fixed by these unit-capacity diagram terms.

For n independent copies under one variation budget, use the already proved normalization `P_n=n^(3n) ∏P(block_i)`. Finite AM–GM and the repeated maximizing probe give the exact capacity `C_n=K^n`; this is `fused_sharp_bound` plus `fused_attained`. The n=0 empty product has capacity one. Thus the logarithmic capacity increments give

`E_n = log C_n = n a`, where `a=log K>0`.

This spacing is derived from the fusion capacity law, rather than assigned as an arithmetic spectrum. Logarithm converts multiplicative capacity into an additive quantity. Here “energy” is a mathematical grading by logarithmic norm; no physical Hamiltonian is claimed. A merely renamed arbitrary sequence would not establish this construction.

## The cubic ring supplies the sign

The cubic physical sparse unit complex is K_3=Ind(P_5), a triangle with three further edges, with the explicit ring retraction in the coalescence paper. Independent block supports, with separating gaps held at zero, form joins. The n-fold join of K_3 is homotopy equivalent to S^(2n−1), so its reduced Euler characteristic is −1 for every n≥1.

The Euler-weighted heat trace of this repeated-seed tower is therefore

`H_a(t)=−Σ_(n≥1) exp(−E_n t)=−1/(exp(a t)−1)`, t>0.

The zero-energy empty product is omitted. On Re s>1, the spectral trace is `−Σ E_n^(−s)=−a^(−s)ζ(s)`. Both the geometric progression and the zeta identity are classical; the geometric obligations are the capacity-derived spacing and the actual join/Euler classification.

## A convergent response at the nontrivial zeros

The continuous interpolation of the linear fusion spectrum has density 1/a and heat trace `−∫₀∞ exp(−a t u)du=−1/(a t)`. Subtract this continuous reference from H_a:

`B_a(t)=1/(a t)−1/(exp(a t)−1)`.

Its Mellin transform converges as an ordinary integral throughout 0<Re s<1. Indeed 0≤B_1(t)≤min(1,1/t). Nonnegativity follows from exp(t)≥1+t. The bound B_1≤1 is equivalent, after multiplying positive denominators, to `(1−t)exp(t)≤1`, which follows from exp(−t)≥1−t. The 1/t bound is immediate. Scaling gives the corresponding bounds for B_a.

The exact identity is

`∫₀∞ t^(s−1) B_a(t) dt = −a^(−s) Γ(s) ζ(s)`.

For a direct proof on this strip, let F(t)=1/(exp(t)+1). Elementary algebra gives `2B_1(2t)−B_1(t)=F(t)`. Taking the convergent Mellin transforms gives `(2^(1−s)−1) M(B_1)(s)=M(F)(s)`. The classical Fermi identity is `M(F)(s)=Γ(s)(1−2^(1−s))ζ(s)`, recorded in [NIST DLMF 25.5.3](https://dlmf.nist.gov/25.5.E3). The prefactor is nonzero in the open strip because |2^(1−s)|>1. Cancellation and scaling prove the displayed formula. The unregularized Bose identity on Re s>1 is [DLMF 25.5.1](https://dlmf.nist.gov/25.5.E1).

Since a^(−s) and Γ(s) are nonzero on this strip, this **actual convergent geometric response vanishes exactly at the zeta zeros there**, with the same multiplicities. The interpretation is cancellation of the Mellin response of the discrete fusion tower against its continuous interpolation. No assertion about the real parts of the zeros is used or implied.

## Observation loss under the ring retraction

The cubic retraction sets the middle gap to zero, so both seed diagram responses ace and S(b+c+d)c vanish on its image. Hence the entire amplification seed vanishes there. Its original positive capacity K>1 cannot be recovered from the homotopy-equivalent ring by restricting this observation. The proposed spectral construction therefore needs the pair consisting of probe geometry and observation, not its bare homotopy type. The ring supplies a topological sign; the uncollapsed observation supplies the nonzero logarithmic scale. CubicObservation now proves this seed annihilation, preservation of B,C,D throughout the homotopy, and the exact restriction kernel B=C=D=0.

## Relation to the other topological trace

This construction repeats one cubic seed and weights by its logarithmic capacity. It differs from the all-pairing-degree tower, which weights by homological occupation and yields eta. Joining two copies of that entire tower yields `η(s−1)−η(s)` and has no common strip zero with eta. Those are different indexing operations; do not claim that arbitrary fusion either preserves or removes zeta zeros.

For a general spherical seed with positive logarithmic capacity, join parity selects a Bose-type or Fermi-type geometric series. For a seed with several homology generators, multiplicities change the trace and need not give zeta. These extensions are useful classification questions, not formalized results here.

## Novelty boundary and next steps

The logarithm law, join homology, Bose/Fermi series, spectral zeta, and Mellin sum-minus-integral identity are classical mechanisms. The proposed contribution is their concrete coupling to the proved chronological capacity amplification and sparse observation geometry. This coupling has not yet passed a sufficient novelty audit; absence of an exact search hit would not establish priority.

Next: audit the novelty of this coupling and classify more general graded seeds. The actual geometric Euler trace and its continuous-reference subtraction are now connected in Lean to the analytic zero-locus and multiplicity theorems. The full five-generator cubic norm remains separate paper work.

## Lean formalization of the join reading (complete, unconditional)

The sphere-homotopy interpretation of the join powers is now a Lean theorem at the level of the
reduced cohomology it is used for, and the eta comparison of the last section is a Lean theorem as
well. Four new modules, 151 declarations, all wired into `GaloisForLFunctions/HTGeometry.lean`,
every declaration depending only on `propext`, `Classical.choice`, `Quot.sound`.

| Module | Declarations | Content |
|---|---:|---|
| `HTGeometry/VertexIndependenceCochain.lean` | 89 | the leaf reduction for the independence complex of an arbitrary induced path subgraph |
| `HTGeometry/VertexIndependenceSphere.lean` | 55 | the block vertex sets and the concentrated cohomology of the join powers |
| `HTGeometry/CubicJoinSphere.lean` | 9 | the identification of `fusedCubicFaces` with the block model |
| `ChronologicalTensor/FusionEtaJoin.lean` | 7 | the alternating zeta series, the self-join trace `η(s-1) − η(s)`, and the no-common-zero statement |

### Joins are disjoint unions, and disjoint unions are induced path subgraphs

An independent block support with the separating gaps held at zero is a disjoint union of paths,
and the independence complex of a disjoint union of graphs is the join of the independence
complexes. So the `n`-fold join of `K_3 = Ind(P_5)` is the independence complex of the induced
subgraph of the path on `joinVertsFrom 0 n = {6i + q : i < n, q < 5}`.

`VertexIndependenceCochain.lean` generalises the three-vertex reduction of
`../3-formalized/chronological-path-cochain-reduction.md` from `Finset.range n` to an arbitrary
finite vertex set `V ⊆ ℕ`. If `a` is the least element of `V` and `a + 1 ∈ V` as well
(`IsLeaf V a`), the maps

  `(K f)(σ) = 0` if `a ∈ σ` or `a+1 ∈ σ`, and `f({a} ∪ σ)` otherwise,
  `(q f)(τ) = f({a+1} ∪ τ) − f({a} ∪ τ)`,
  `(J g)(σ) = g(σ \ {a+1})` if `a+1 ∈ σ`, and `0` otherwise,

satisfy the same four identities, with the tail complex now the independence complex on
`tailVerts V a = {v ∈ V | a + 3 ≤ v}`, that is on `V` with the closed neighbourhood of `a+1`
deleted. The conclusion is

```
cohomologyEquiv F V a j (hL : IsLeaf V a) :
    cohomology F V (j+1) ≃ₗ[F] cohomology F (tailVerts V a) j
```

and because the tail is already a vertex set no relabeling step is needed at all.

### Two leaf reductions strip one join factor

`tailVerts (joinVertsFrom a (n+1)) a = midVertsFrom a n` and
`tailVerts (midVertsFrom a n) (a+3) = joinVertsFrom (a+6) n`, so

```
joinCohomologyEquiv F a n j :
    cohomology F (joinVertsFrom a (n+1)) (j+2) ≃ₗ[F] cohomology F (joinVertsFrom (a+6) n) j
```

deletes one block of five vertices — one join factor `Ind(P_5)` — and lowers the occupation degree
by two. The base case is the empty vertex set, whose independence complex is the single empty face
(`cohomologyEmptyEquiv : cohomology F ∅ 0 ≃ₗ[F] F`, the reduced cohomology of `S^(-1)`).
Induction gives

```
joinCohomology_nonempty_equiv : Nonempty (cohomology F (joinVertsFrom a n) (2*n) ≃ₗ[F] F)
joinCohomology_subsingleton   : j ≠ 2*n → Subsingleton (cohomology F (joinVertsFrom a n) j)
joinCohomology_finrank (F : Field) :
    Module.finrank F (cohomology F (joinVertsFrom a n) j) = if j = 2*n then 1 else 0
```

Occupation `2n` is topological degree `2n − 1`: **exactly the reduced cohomology of `S^(2n−1)`,**
for every `n ≥ 1`, and the alternating sum of these ranks is the already proved reduced Euler
characteristic `−1` of `fusedCubicReducedEuler_eq`. What is formalized is the graded reduced
cohomology, which is everything the Euler-weighted heat trace uses; the homotopy equivalence
itself would additionally need a geometric realization and a join homotopy theory that mathlib
does not have, and no claim on this card depends on it.

### The identification with the corpus join

`CubicJoinSphere.lean` closes the loop with the corpus's own model of the join.
`mem_cubicFaces_iff_isPathFace_image` proves `σ ∈ cubicFaces ↔ IsPathFace 5 (σ.image Fin.val)`, so
the cubic facets `{0,2,4}`, `{0,3}`, `{1,3}`, `{1,4}` are exactly the maximal nonadjacent subsets
of `P_5`. Relabelling the block-labelled vertex `(i, q)` by `6i + q` (`cubicJoinLabel`, injective
and cardinality preserving) then gives

```
mem_fusedCubicFaces_iff_isFace :
    σ ∈ fusedCubicFaces n ↔ IsFace (joinVertsFrom 0 n) (σ.image cubicJoinLabel)
```

so the graded cohomology above is the graded cohomology of the corpus's `fusedCubicFaces n`.

### The eta comparison

`FusionEtaJoin.lean` makes the last section's warning a theorem. `etaJoinEuler` computes the join
coefficients of two copies of the occupation tower,
`−∑_{m+n=k} ε_m ε_n = (k−1)(−1)^(k−1)` with `ε_n = (−1)^(n−1)`. `dirichletEta_eq_tsum` proves the
alternating zeta series `η(s) = ∑ (−1)^n (n+1)^(−s)` for `1 < Re s` (new corpus infrastructure: the
corpus had `dirichletEta` only as `(1 − 2^(1−s)) ζ(s)`), and `etaJoin_tsum` assembles

```
∑' n, n (−1)^n (n+1)^(−s) = dirichletEta (s−1) − dirichletEta s     for 2 < Re s.
```

Finally `dirichletEta_sub_one_ne_zero` proves `η(s−1) ≠ 0` throughout `0 < Re s < 1` — the factor
`1 − 2^(2−s)` has modulus bounded away from `1` there, and `ζ(s−1) ≠ 0` because the zero locus of
`ζ` left of the strip is exactly the trivial ladder `−2, −4, …` — so
`etaJoin_ne_zero_of_dirichletEta_eq_zero` gives: **the self-join trace and eta have no common zero
in the strip.** Joining does not preserve the eta zeros, confirming the card's warning that fusion
is not a zero-preserving operation on spectral traces.

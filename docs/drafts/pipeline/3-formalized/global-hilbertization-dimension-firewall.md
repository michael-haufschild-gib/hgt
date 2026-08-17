# Global Hilbertization and dimension firewall

Stage: 3-formalized

Status: `[LITERATURE] [PAPER-PROVED] [BRIDGE] [LEAN PROVED]`

Lean status: unconditional and closed — no hypotheses, no added axioms, no dimension assumption

Source: Nowicki and Eve, *Locally Quantum, Globally Non-Hilbertizable* (Zenodo 21982163, 2026),
Theorem 4.1 and Corollary 4.2.  The Gram-factorization parent theorem is already formalized locally
as `exists_gram_factorization`.

## Exact claim

For every finite complex matrix `K`, the following are equivalent:

1. `K` is positive semidefinite;
2. `K` is the Gram matrix of vectors in the canonical Euclidean space of dimension `card K`.

Moreover, a realization of `K` as a Gram matrix in any complex inner-product space, with no
finite-dimensional assumption on that space, implies that `K` is positive semidefinite.  Hence an
indefinite finite kernel cannot be repaired by increasing ambient Hilbert-space dimension.

For an occurrence-indexed block kernel whose diagonal blocks are identities, every Gram realization
consists of an orthonormal frame at each context.  Equivalently, positivity of the normalized block
kernel is exactly existence of one common Hilbert carrier containing all those frames.

As a closed corollary, every member of the balanced context-order family has no global Hilbert-space
realization in any complex inner-product space.

## Paper proof

Every Gram matrix is positive semidefinite because for every finitely supported coefficient family
`c`,

```text
Σᵢⱼ conj(cᵢ) ⟨vᵢ,vⱼ⟩ cⱼ = ‖Σᵢ cᵢvᵢ‖² ≥ 0.
```

This argument uses only the finite index family, so the ambient Hilbert space may have arbitrary
dimension.

Conversely, the positive square root of a finite PSD matrix gives `K=VV†`.  Taking the conjugated
rows of `V` as vectors in the canonical Euclidean coordinate space gives `Kᵢⱼ=⟨vᵢ,vⱼ⟩`.

If the diagonal context block is the identity, substituting two occurrence labels in the same
context into the Gram equality gives `⟨vᵢₐ,vᵢ_b⟩=δₐb`, exactly orthonormality.  Finally, the balanced
context kernel is indefinite by the separately proved constant-line witness, whereas every Hilbert
Gram is PSD; contradiction proves the dimension firewall.

## Hostile audit

- Infinite ambient dimension is explicitly covered; no finite-dimensional escape remains.
- The finite kernel itself is essential and unconditional.
- Normalization is stored as data of the normalized block-kernel structure, not assumed ad hoc by a
  theorem intended to cover unnormalized kernels.
- This is established Gram theory and is a bridge, not a novelty claim.

## Lean target

Use `Matrix.gram`, `Matrix.posSemidef_gram`, `exists_gram_factorization`, and the balanced hierarchy.
No new axiom, spectral theorem, or dimension assumption.

## Lean status -- the whole card is formal

`formal/GaloisForLFunctions/HTGeometry/GramRealizationFirewall.lean` (new, umbrella-wired,
axiom-clean), on top of the already formal `exists_gram_factorization`.

| Card item | Declaration |
|---|---|
| the Gram kernel of a finite family of vectors, and its Hermitian symmetry | `innerGramMatrix`, `isHermitian_innerGramMatrix` |
| **`2 => 1` with no finite-dimensional assumption on the ambient space** | `posSemidef_innerGramMatrix` |
| **`1 => 2`**: a positive semidefinite kernel is the Gram kernel of the conjugated rows of a square factorization | `exists_innerGramMatrix_of_posSemidef` |
| **the equivalence, hence the dimension firewall** | `posSemidef_iff_exists_innerGramMatrix` |
| an identity diagonal block of a Gram kernel is an orthonormal frame | `orthonormal_of_innerGramMatrix` |
| **the corollary**: no member of the balanced context-order family is a Gram kernel in any complex inner product space | `balancedContext_ne_innerGramMatrix` |

`posSemidef_innerGramMatrix` is stated for an arbitrary `NormedAddCommGroup`/`InnerProductSpace ℂ`,
with no `FiniteDimensional` instance anywhere, which is exactly the card's "infinite ambient
dimension is explicitly covered" clause: the quadratic form of the kernel against a finitely
supported coefficient family is literally the inner product of one finite linear combination with
itself, and `CStarModule.inner_self_nonneg` closes it.  The converse uses the corpus's continuous
functional calculus square root through `exists_gram_factorization`; no spectral theorem is invoked
here.

The corollary is stated as a non-equality quantified over every complex inner product space and
every family, which is the universe-clean form of "has no global Hilbert-space realization".

# Arbitrary finite interaction hypergraphs have maximal generic component spectra

- **ID:** `hypergraph-local-projective-spectral-factorization`
- **Stage:** 3-formalized
- **Type:** DEPENDENCY-CLOSED PAPER PROOF / ALL FINITE INTERACTION ORDERS /
  GENERIC PROJECTIVE SPECTRUM
- **Date:** 2026-07-30
- **Status:** `[PAPER-PROVED] [LEAN PROOF CLOSED]`
  `[SPECIALIST AUDIT OPEN] [PRIORITY OPEN]`
- **Parents:**
  `arbitrary-graph-quantum-temporal-curvature-law.md`,
  `disconnected-local-spectral-factorization-genericity.md`

## Theorem

Let \(V\) be a finite set. Give every \(v\in V\) a complex Hilbert space
\(\mathcal H_v\) of dimension \(q_v\ge2\), and put
\[
 \mathcal H=\bigotimes_{v\in V}\mathcal H_v.
\]
Let \(\mathfrak H\) be any finite hypergraph on \(V\). Define
\(\mathcal L_{\mathfrak H}\) to be the real linear subspace of Hermitian
operators on \(\mathcal H\) spanned by:

1. arbitrary one-site Hermitian operators;
2. arbitrary Hermitian operators acting nontrivially only inside one
   hyperedge \(X\in\mathfrak H\).

For every hypergraph connected component \(C\), put
\[
 D_C=\prod_{v\in C}q_v.
\]
Then a dense full-Lebesgue-measure \(G_\delta\) subset of
\(\mathcal L_{\mathfrak H}\) has simple spectrum and projective rational
spectral rank
\[
 \boxed{
 \tau(H)=\sum_{C\in\pi_0(\mathfrak H)}(D_C-1).
 }                                                       \tag{1}
\]
The result already holds on the real-symmetric slice in a fixed product
basis.

Thus the generic completed spectral rank depends on interaction
factorization only, not interaction order, range, hyperedge sizes, vertex
degrees or geometry.

## Proof

### 1. Two-section spanning forests

Let \(G_2(\mathfrak H)\) be the two-section graph: distinct vertices
\(u,v\) are adjacent when some hyperedge \(X\in\mathfrak H\) contains both.
Hypergraph connectivity is exactly graph connectivity in
\(G_2(\mathfrak H)\).

Choose a spanning tree \(T_C\) in the two-section graph of each nontrivial
component \(C\), and let \(T\) be their disjoint union. For every tree edge
\(\{u,v\}\), choose one containing hyperedge \(X_{uv}\).

Every arbitrary two-site Hermitian operator \(A_{uv}\) embeds as
\[
 A_{uv}\otimes I_{X_{uv}\setminus\{u,v\}}
\]
on \(X_{uv}\), tensored with identities outside \(X_{uv}\). It is therefore
an allowed hyperedge-local term. Consequently
\[
 \mathcal L_T\subseteq\mathcal L_{\mathfrak H},        \tag{2}
\]
where \(\mathcal L_T\) is the ordinary arbitrary one-site plus arbitrary
two-site spanning-forest Hamiltonian space.

### 2. Connected components

For each connected component \(C\) with at least two vertices, the
arbitrary-graph local maximality theorem applied to \(T_C\) supplies a
real-symmetric Hamiltonian with simple spectrum and projective rank
\(D_C-1\). For a one-vertex component, an arbitrary real-symmetric one-site
matrix with a rationally independent gap list supplies the same witness.

Every balanced rational relation polynomial and the discriminant that are
nonzero on the spanning-tree subspace remain nonzero on the containing
hypergraph-local space by `(2)`. Hence, within each connected component,
simple maximal projective rank is dense, full measure and \(G_\delta\).

### 3. Disconnected components

No allowed term crosses distinct hypergraph components, so every
Hamiltonian decomposes as a tensor-sum of its component Hamiltonians. The
universal upper bound is therefore
\[
 \tau(H)\le\sum_C(D_C-1).                              \tag{3}
\]

The disconnected factorization theorem applies to the component parameter
spaces just established. It constructs mutually rationally transverse
scaled component witnesses and separately symmetric relation polynomials
for every excess relation. Outside their countable null/meagre union and
the total discriminant, the component gap modules are maximally projective
and mutually transverse. Equality holds in `(3)`, proving `(1)`.
\(\square\)

## Scope boundary

“Arbitrary term on a hyperedge” means support contained in that hyperedge;
lower-body operators inside it are allowed. The theorem does not cover a
family restricted to exactly \(k\)-body correlation tensors with every
lower-order marginal forced to vanish. Such a restricted family requires
its own witness theorem.

Likewise, the full inhomogeneous coefficient space is used. A
translation-invariant, symmetry-constrained, gauge-constrained or
few-parameter subfamily may lie inside an exceptional relation variety.

## Hostile audit

1. **Does a hyperedge necessarily contain arbitrary pair terms?** Yes under
   the stated support-contained convention; this is why that convention is
   explicit.
2. **Does the tree witness prove genericity in the larger space?** Yes.
   Every obstruction is the zero set of a polynomial on the larger space;
   its restriction is nonzero on the tree subspace, so the full polynomial
   is nonzero.
3. **Can extra hyperedges create a universal relation?** No. The larger
   parameter space still contains the relation-destroying tree witness.
4. **Are isolated vertices covered?** Yes, separately by arbitrary one-site
   spectra.
5. **Does disconnectedness introduce forced relations overlooked by global
   symmetrization?** No. The cited disconnected theorem uses componentwise
   symmetrization and tests only excess relations beyond tensor-sum
   factorization.

No paper-proof dependency remains. Exact-object priority and formalization
remain open.

## Lean formalization

Unconditional; every theorem below has axioms `[propext, Classical.choice,
Quot.sound]` only.  Four modules, all wired into `GaloisForLFunctions.HTGeometry`.

`HTGeometry.HypergraphLocalHamiltonian`

- `twoSection 𝔥` — two-section graph; `twoSection_adj_iff`,
  `twoSection_reachable_of_mem_hyperedge`.
- `hypergraphLocalSubmodule A 𝔥` — the exact real space \(\mathcal L_{\mathfrak H}\):
  the real span of Hermitian operators `IsSiteSupported {v}` or `IsSiteSupported X`
  for `X ∈ 𝔥`.  This is the stated support convention, so lower-body operators
  inside a hyperedge are admissible.
- `siteFactorLocalSubmodule_twoSection_le_hypergraphLocalSubmodule` — equation `(2)`.
- `exists_maximallyProjective_mem_hypergraphLocalSubmodule` — connected witness.
- `hypergraphLocalMaximalSet_dense_residual_fullMeasure`,
  `anchoredTemporalRank_hypergraphLocalMatrix_eq`,
  `injective_eigenvalues_hypergraphLocalMatrix` — the connected case:
  `τ(H) = ∏_v q_v − 1` and simple spectrum, dense, residual, full measure in the
  canonical coordinates of \(\mathcal L_{\mathfrak H}\).
- `injective_of_maximallyProjectiveEnergy` — maximal projective rank ⟹ simplicity.

`HTGeometry.HypergraphComponentFactorization`

- `hypergraphComponents 𝔥` — component packets; disjointness, covering
  (`biUnion_hypergraphComponents`, `prod_hypergraphComponents_prod`),
  `hyperedge_subset_hypergraphComponentOf` (no admissible term crosses components).
- `exists_hermitian_componentBlocks` — exact block decomposition of every
  hyperedge-local Hamiltonian over the components.
- `anchoredTemporalRank_eq_sum_hypergraphComponents` — equation `(1)`.
- `injective_eigenvalues_of_componentProjectivelyIndependent` — simple total
  spectrum from transverse component gap modules.

`HTGeometry.ConcatenatedSpectrumScaleShiftWitness`

- `exists_scale_shift_concatenated_linearIndependent`,
  `exists_scale_shift_concatenated_maximallyProjective` — independently scaling
  and shifting maximally projective component spectra makes the concatenation
  carry no nonzero integer relation.  This is the transverse witness of §3 and
  the input the block-diagonal genericity theorem had never been given.

`HTGeometry.HypergraphComponentWitness`

- `blockLocalSubmodule A 𝔥 P` — block space of one component; contains the
  identity (`one_mem_blockLocalSubmodule`), so component spectra shift freely.
- `siteFactorLocalSubmodule_le_blockLocalSubmodule`,
  `exists_maximallyProjective_mem_blockLocalSubmodule` — component witness.

`HTGeometry.HypergraphProjectiveSpectralFactorization`

- `hypergraphHamiltonian A 𝔥 p`, `hypergraphBlock A 𝔥 c p` — the exact affine
  parameterization of \(\mathcal L_{\mathfrak H}\) split by component;
  `hypergraphHamiltonian_eq_sum_lift`, `exists_hypergraphHamiltonian_eq`
  (the coordinates exhaust the space).
- `exists_witness_hypergraphBlock` — the transverse witness parameter.
- `hypergraphComponentGenericSet_dense_residual_fullMeasure` — dense, residual,
  full Lebesgue measure.
- `anchoredTemporalRank_hypergraphHamiltonian_eq_sum` — equation `(1)`:
  `τ(H) = ∑_{C ∈ π₀(𝔥)} (∏_{v ∈ C} q_v − 1)`.
- `injective_eigenvalues_hypergraphHamiltonian` — simple spectrum.

The only hypotheses are the ones in the statement: `V` finite, `q_v ≥ 2`, and
`𝔥` a finite family of site packets.  Hyperedge sizes, interaction order, vertex
degrees and geometry are unconstrained.

## Gates

- [x] exact support convention
- [x] two-section spanning-forest inclusion
- [x] connected component witness
- [x] larger-space genericity
- [x] disconnected factorization
- [x] exact Lean formalization
- [ ] exact-object priority audit
- [ ] independent specialist review


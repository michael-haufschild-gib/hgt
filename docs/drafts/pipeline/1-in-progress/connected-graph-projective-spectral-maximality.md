# Connected interaction graphs have generically maximal projective spectral rank

- **ID:** `connected-graph-projective-spectral-maximality`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / ACTIVE FORMALIZATION
- **Parent:** `../3-formalized/nearest-neighbor-qudit-projective-spectral-maximality.md`
- **Scientific status:** `[NEW TARGET] [EXTERNAL PRIORITY PROVISIONAL]`

## Target theorem

Let \(G=(V,E)\) be every finite connected simple graph with at least two
vertices.  Give vertex \(v\) a finite local Hilbert space
\(\mathbb C^{q_v}\), \(q_v\geq2\), and let \(\mathcal L_G\) be the full real
space of Hermitian one-site terms and Hermitian two-site terms on edges of
\(G\).  Put
\[
 D=\prod_{v\in V}q_v .
\]
Then for Lebesgue-almost every \(H\in\mathcal L_G\),
\[
 \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
 \{E_j(H)-E_1(H):2\leq j\leq D\}=D-1.
\]
The maximal set is dense, residual, and full measure.

Consequently every finite connected interaction geometry generically has the
full \(D-1\) projective recurrence dimension.  For every fixed
\(0<\varepsilon<2\), its exact completed-time projective return density is
\[
 \left(\frac{2\arcsin(\varepsilon/2)}{\pi}\right)^{D-1}.
\]

## Why this moves the frontier

The existing path theorem reaches only graphs containing a spanning path and
explicitly leaves connected graphs without one open.  Stars with four or more
leaves are the simplest excluded family.  The new theorem removes graph
shape, degree, branching, and uniform-local-dimension restrictions.

The mechanism is not genericity by assertion:

1. every connected finite graph contains a spanning tree;
2. every finite tree is obtained from one edge by successive attachment of a
   leaf to an arbitrary existing parent;
3. the exact-unitary Hermitian leaf theorem preserves maximal projective rank
   and a connected nonbipartite local-observer family at every existing site;
4. a two-site Bell seed supplies the physical qubit base; arbitrary local
   dimensions use the same two-site full-edge base;
5. the constructed tree-local witness is a point in the full polynomial
   graph-local Hamiltonian family;
6. one witness activates the existing polynomial Hermitian genericity theorem;
7. setting all non-tree edge coefficients to zero embeds the tree witness in
   every connected supergraph.

## Exact formal gap

Spectral iteration alone erases physical provenance.  Before this card can
advance, Lean must retain:

- every attachment as a real combination of probes at the chosen parent;
- every inherited probe as an original probe at the same physical site;
- the accumulated unitary from physical tensor coordinates to spectral
  coordinates;
- the decomposition of the Hamiltonian into one-site and graph-edge terms;
- the graph leaf schedule and the spanning-tree embedding.

The first two provenance statements are now compiled in the Hermitian
leaf-extension chain.  Tensor-coordinate accumulation, physical Bell seed,
tree induction, and the universal graph-local polynomial family remain.

## Collision audit

Searches through current arXiv/journal results found generic simple-gap and
controllability criteria, and explicit rationally independent free-fermion
chains, but no theorem asserting full many-body projective rational rank for
almost every fixed finite connected interaction graph with arbitrary local
dimensions.  This is provisional until exact-object citation chasing is
complete.

## Hostile boundary

1. This closes spectral recurrence geometry, not Brown--Susskind linear
   circuit-complexity growth.
2. It is finite-volume and time-independent; thermodynamic limits require a
   separate statement.
3. Translation-invariant coefficient subspaces need not inherit genericity.
4. Exact rational rank alone gives no uniform finite-resolution first-return
   constant.
5. No manuscript claim is authorized before physical locality, genericity,
   and recurrence corollaries compile without forbidden axioms.

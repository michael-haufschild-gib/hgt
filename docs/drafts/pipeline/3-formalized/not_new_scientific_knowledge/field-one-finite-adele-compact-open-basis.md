# Compact-open basis of rational finite adeles

- **ID:** `field-one-finite-adele-compact-open-basis`
- **Stage:** 3-formalized
- **Type:** TOPOLOGICAL THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-finite-adele-sigma-compact`
- **Statement:** compact-open subsets form a basis of the rational
  finite-adele topology, and every compact subset of an open set admits a
  compact-open interpolant.

## Theorem

Every local rational adic completion is homeomorphic to a \(p\)-adic field,
so it is Hausdorff and totally disconnected.  The restricted product embeds
continuously and injectively in the product of these completions; therefore
\(\mathbb A_f\) inherits both properties.  Local compactness and zero
dimensionality give a clopen neighborhood basis.  Shrinking inside a compact
neighborhood makes the basis compact-open.

If \(K\subseteq U\), with \(K\) compact and \(U\) open, choose a compact-open
neighborhood \(V_x\subseteq U\) for every \(x\in K\).  Compactness extracts a
finite subcover, and its union is a compact-open set \(C\) satisfying
\[
  K\subseteq C\subseteq U.
\]

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FieldOneFiniteAdeleCompactOpenBasis`
- **Instances:** `fieldOneFiniteAdeleT2Space`,
  `fieldOneFiniteAdeleTotallyDisconnectedSpace`
- **Core theorems:** `fieldOneFiniteAdele_compactOpen_basis`,
  `fieldOneFiniteAdele_exists_compactOpen_between`
- **Audit:** direct cached `lake env lean` passed. Scratch `#print axioms`
  reports only `propext`, `Classical.choice`, and `Quot.sound`. Final
  targeted `lake build` remains reserved for final audit.

## Gates

- [x] 0 → 1: local separation and restricted-product inheritance
- [x] 1 → 2: compact-open basis and finite-union interpolation proof
- [x] 2 → 3: unconditional direct Lean check and axiom audit
- [ ] 3 → 4: publication-ready integration

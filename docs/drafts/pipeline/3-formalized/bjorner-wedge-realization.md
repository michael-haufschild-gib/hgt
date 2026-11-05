# Björner's wedge decomposition of the prime complex

- **ID:** bjorner-wedge-realization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0411 §2.1, A22.

## Statement

For `N≥2`, the realization of the squarefree prime complex is homotopy
equivalent to the finite wedge of spheres `S^(ω(m)−1)`, indexed by odd
squarefree integers `N/2<m≤N`. For `N<2`, the realization is empty.

## Arithmetic input

`HTGeometry/SquarefreePrimeComplex.lean` already proves:

- `primeTwoStar` is closed under adjoining the apex `2`.
- Every face outside this star is a facet; every proper subface lies in the star.
- `primeTwoComplementEquiv` identifies these facets with the stated odd squarefree integers.

## Proof

For each complementary facet `S`, the entire boundary of the simplex on
`{2}∪S` lies in the prime complex: its face `S` is present, and every other
face lies in the star. This boundary is a sphere of dimension `|S|−1`.
Map their wedge into the complex by these inclusions, with common basepoint `2`.

Contract the star linearly to `2`. On each complementary facet, extend the
boundary contraction through its surrounding simplex boundary. The extensions
agree on intersections, since those lie in the star. At time one, the resulting
map factors through the wedge. These same local homotopies prove both inverse
identities; all fix vertex `2`. Singleton facets use the identity homotopy on
their two-point sphere. Finite closed-face gluing gives continuity.

Located inputs:

- Mathlib `Geometry.SimplicialComplex.onFinsupp`.
- `DifferentialGeometry.Simplex.exists_continuous_homotopy_extension`.
- `DifferentialGeometry.Simplex.exists_boundary_homotopy_contracting_faces_through_zero`:
  its restriction to every inactive face is the same linear vertex contraction.
- `DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph`.

## Lean

Namespace `GaloisForLFunctions.HodgeTheoryWithoutVarieties`:

- `CompatibleSimplexContractions.lean`: compatible boundary contractions,
  finite closed-cover gluing, pointed wedges and descent of homotopies.
- `FiniteConeComplexesHaveSphereBouquets.lean`: `finiteConeComplexHomotopyEquiv`
  constructs both maps and both homotopies; `bouquetFamilyHomeomorph` transports
  the summands and their index set.
- `SquarefreePrimeComplexIsASphereBouquet.lean`:
  `primeComplexSphereBouquetHomotopyEquiv` is the arithmetic theorem.
  `boundedPrimeFaces_nonempty_iff` identifies its faces with the existing abstract
  prime complex; `primeSphereIndex_card` gives the sphere dimensions;
  `primeSphereIndex_window` gives the exact upper half-window;
  `primeComplexRealization_empty` covers `N<2`.

The target spheres are literal unit spheres in Euclidean spaces, with basepoints
given by vertex two. The empty wedge is a point. All three modules are wired into
the owning umbrella. Direct source checks and seven transitive axiom audits contain
only `propext`, `Classical.choice`, and `Quot.sound`.

# Isolated primes obstruct fixed-point localization

- **ID:** hhac-isolated-prime-fixed-points
- **Stage:** 5-failed
- **Route:** Literal square-root-sized fixed set for a self-map homotopic to the identity
- **Positive survivor:** Component classification, connected-core bouquet and exact Euler correction; formalized

## Negative theorem

Every prime `N/2<p≤N` is an isolated vertex of the actual prime complex.
Every self-map homotopic to the identity fixes each such vertex. The
prime-window theorem supplies at least `N/(4 log N)` such vertices eventually;
their number divided by `√N` tends to infinity. Consequently no family of
these maps admits an eventual `C√N` bound on its fixed-point cardinality,
for any constant `C`.

This refutes the literal small-fixed-set question in the programme specification.
It does not refute signed Lefschetz cancellation or a relative localization.

## Strong positive survivor

For `N≥4`, the path components are exactly one connected core containing
prime two and the isolated upper-half primes. The core consists of the faces
whose vertices satisfy `2p≤N`; every identity-homotopic self-map preserves it.

Its complementary facets are exactly the original complementary facets with
at least two vertices. The actual cone-bouquet equivalence therefore retains
all positive-dimensional arithmetic sphere summands and removes precisely
the prime-labelled zero-spheres. This is a homotopy classification, not a
contraction of the core.

With the empty face included in the signed count,

`coreEuler(N) = M(N) + #{p prime : N/2<p≤N}`.

Thus `χ̃(core)=−M(N)−#{N/2<p≤N}`. A replacement localization must account for
that component mass; deleting isolated points does not erase their arithmetic
contribution.

## Proof mechanism

A face containing an upper-half prime cannot contain a second prime. Its
barycentric coordinate is consequently zero or one, and continuity along a
homotopy fixes the isolated vertex. Every remaining point joins a support
vertex inside its simplex, then joins prime two along an allowed edge.
The core star of two contains every proper subface of each complementary
facet. The finite cone-bouquet theorem gives the stated homotopy equivalence.
Finally, the face sum splits into core faces and removed singletons, each of
which contributes `−1` to the signed augmented count.

## Formalization

All paper statements above are formalized. Direct `lake --old env lean <module>`
audits pass; the printed capstones use only `propext`, `Classical.choice`, and
`Quot.sound`.

| Module | Main declarations |
|---|---|
| [PrimeComponentRigidity](../../../../formal/GaloisForLFunctions/HeightHomotopyArithmeticCounts/PrimeComponentRigidity.lean) | `upperPrimeFixedEmbedding`, `primeHeight_joined_iff` |
| [PrimeFixedPointObstruction](../../../../formal/GaloisForLFunctions/HeightHomotopyArithmeticCounts/PrimeFixedPointObstruction.lean) | `tendsto_upperPrime_count_div_sqrt`, `not_squareRoot_fixedPoint_localization` |
| [PrimeCoreEuler](../../../../formal/GaloisForLFunctions/HeightHomotopyArithmeticCounts/PrimeCoreEuler.lean) | `primeCore_isPathConnected`, `homotopy_preserves_primeCore`, `primeCoreEulerChar_eq` |
| [PrimeCoreBouquet](../../../../formal/GaloisForLFunctions/HeightHomotopyArithmeticCounts/PrimeCoreBouquet.lean) | `primeCore_complement_iff`, `primeCoreBouquetEquiv`, `primeCore_complement_arithmetic` |

The input topology and prime asymptotics are classical; no priority claim is
made for them. The contribution is the explicit obstruction to the proposed
arithmetic localization and its dependency-closed positive replacement.

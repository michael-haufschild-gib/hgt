# Dense-null continuation seam topology

- **ID:** `dense-null-continuation-seam-topology`
- **Stage:** 3-formalized
- **Type:** THEOREM / TOPOLOGICAL BRIDGE
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [BRIDGE] [NOT NEW IN ISOLATION]`
- **Parent route:**
  `../../2-fully-proven/new_scientific_knowledge/helson-universal-ht-arbitrary-divisor-orthogonality.md`

## Statement

The following general facts isolate the topology used by the Helson continuation seam.

1. In an arbitrary product `product_i A_i`, the functions that differ from a fixed base point at
   only finitely many coordinates form a dense subset.
2. If a subset `S` of a measured topological space has measure zero and every nonempty open set has
   positive measure, then `S` has dense complement.
3. If both `S` and its complement are dense, then every open neighborhood meets both sides and
   `frontier(S)` is the whole ambient space.
4. The Boolean side indicator of a dense/codense seam is continuous at no point and cannot factor
   through continuous maps to and from any intermediate topological readout space.
5. If `S` lies in a compact space and admits a surjective readout onto a noncompact topological
   space, then `S` cannot be both closed and a domain on which that readout is continuous.

Applied after the classical analytic inputs, these statements say that the globally meromorphic
Helson stratum is dense, codense, and boundary-everywhere in the prime-phase product torus, while
its continuation indicator is nowhere continuous and its divisor readout cannot be a continuous
readout from a closed compact seam.

## Proof

For the product-density theorem, let a nonempty basic open set be given.  It restricts only a
finite coordinate set.  Match an arbitrary point of the open set on those coordinates and use the
fixed base point elsewhere.  This finite modification remains in the open set.

For the null-complement theorem, if a nonempty open set failed to meet `S^c`, it would be contained
in `S` and hence have measure zero, contradicting positivity of nonempty open sets.  The frontier
identity

```text
frontier(S) = closure(S) intersect closure(S^c)
```

then gives the whole space.  Finally, a closed subset of a compact space is compact, and the
continuous image of a compact space is compact.  A continuous surjection onto a noncompact target
is therefore impossible.  For the classifier theorem, continuity at any point would give a
neighborhood on which the discrete Boolean output is constant; density of the opposite side gives
an immediate contradiction.  A continuous factorization would make the indicator continuous and
is therefore impossible.

## Scientific role

These are standard topology and measure arguments and are not new in isolation.  Their role is to
make the new candidate geometry exact: the finite-prime inverse-limit topology cannot locally
decide analytic continuation, and a divisor-universal continuation seam needs either a nonclosed
domain or a stronger, noncompact topology.

## Formal theorem surface

The implementation is
`formal/GaloisForLFunctions/HTGeometry/DenseNullContinuationSeam.lean` and contains:

- `finiteModification`;
- `dense_finiteModification`;
- `dense_compl_of_measure_zero_of_open_pos`;
- `frontier_eq_univ_of_dense_and_dense_compl`;
- `every_open_neighborhood_meets_both_sides`;
- `seamIndicator`;
- `nowhereContinuous_seamIndicator`;
- `no_continuous_factorization_seamIndicator`;
- `not_isClosed_or_not_continuous_of_surjective_to_noncompact`.

## Gates

- [x] finite-modification density proved
- [x] null plus full-support measure implies codensity
- [x] boundary-everywhere and neighborhood two-sidedness proved
- [x] nowhere-continuous side indicator proved
- [x] no-continuous-factorization theorem proved
- [x] compact-readout dichotomy proved
- [x] narrow module check passed
- [x] narrow module build passed
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] project lint and generated indexes refreshed

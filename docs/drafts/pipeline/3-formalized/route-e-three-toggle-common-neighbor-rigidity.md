# Route E: three-toggle common-neighbor rigidity

- **ID:** E-THREE-TOGGLE-COMMON-NEIGHBOR-RIGIDITY-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Distance-three prime-support edges reverse Möbius sign; two sources sharing such a
  neighbor have symmetric-difference distance only zero, two, four, or six, and the distance-six
  common-neighbor fibre has exact cardinality `Nat.choose 6 3`.

## Goal

Open the first direct odd-toggle graph surviving the one-toggle Hall obstruction and the
two-by-two switch parity no-go. Classify its collision geometry before attempting any Hall or
column-load estimate. This attacks the unsigned source-incidence gate: a coefficient-one expansion
proof must control how many source rows can share the same opposite-sign receiver.

## Exact theorem

Write `S △ T` for symmetric difference and declare `S,T` adjacent when

```text
card(S △ T) = 3.
```

For finite prime supports, every such edge reverses Möbius sign. If `T` is adjacent to both `S`
and `U`, put `A = S △ T` and `D = S △ U`. Symmetric-difference cancellation gives
`A △ D = T △ U`; hence `card A = card(A △ D) = 3`. The exact cardinal identity

```text
card(A) + card(D) = card(A △ D) + 2 * card(A ∩ D)
```

therefore gives

```text
card(D) = 2 * card(A ∩ D).
```

Since `A` has three elements, `card(D)` is one of `0,2,4,6`.

At distance six, the overlap has cardinality three, so `A ⊆ D`. Conversely every three-subset
`A ⊆ D` gives a common neighbor `T = S △ A`: its distance from `S` is three, and its distance
from `U` is the other three coordinates of `D`. Toggling from fixed `S` is injective. Thus the
complete common-neighbor fibre is in bijection with the three-subsets of `D` and has cardinality

```text
Nat.choose 6 3.
```

No enumeration or computational decision procedure is used.

## Consequence for proof chain

The direct distance-three relation is now certified sign-reversing, and its pairwise collision
support is completely local: source pairs farther than six have no common receiver. The most
separated collision regime, distance six, has an absolute finite codegree independent of ambient
prime aperture.

This does not prove Hall. At source distances two and four, common-neighbor counts can still grow
with ambient support coordinates; multiplicative cutoff can also remove upward moves and collapse
row degree near the top shell. Therefore generic degree/co-degree double counting still reaches at
most the already known near-Hall scale. The live theorem remains an arbitrary-family,
multiplicative-threshold expansion with coefficient one and only square-root additive defect,
compatible with the same physical interval and seam.

If that expansion is proved, finite matching bounds unmatched Möbius mass, the existing Mertens
cancellation implication applies, and the chain reaches RH. None of those later steps is claimed
here.

## Lean formalization

`RouteEThreeToggleCommonNeighborRigidity.lean` contains:

- `routeEThreeToggleAdjacent`;
- `routeE_threeToggle_reverses_moebius`;
- `routeE_threeToggle_common_neighbor_exact_overlap`;
- `routeE_threeToggle_common_neighbor_even_separation`;
- `routeE_threeToggle_common_neighbor_separation_le_six`;
- `routeE_threeToggle_common_neighbor_separation_cases`;
- `mem_routeEThreeToggleDistanceSixCommonNeighbors_iff`;
- `card_routeEThreeToggleDistanceSixCommonNeighbors`.

All results are dependency-closed finite theorems. Prime assumptions occur only in the Möbius-sign
corollary; collision classification is unconditional finite-set algebra. No Hall premise,
column-load bound, asymptotic estimate, hypothesis about RH, computation, or added axiom occurs.

## Research and conjecture loops

Corpus deep search found no existing exact common-neighbor theorem for symmetric-difference
distance three. It recovered Hamming-distance definitions, generic simple-graph common-neighbor
bounds, Kruskal--Katona/local-shadow infrastructure, and the already formalized Route E
row-degree/co-degree near-Hall theorem. That last result proves only an `X^{-o(1)}` neighborhood
ratio, explicitly insufficient for coefficient-one Hall.

1. **Conjecture:** full-cube distance-three codegree depends only on source distance.
   **Proved locally:** exact overlap forces distances `0,2,4,6`; at distance six the entire fibre
   is the three-subset image and has size `Nat.choose 6 3`.
2. **Conjecture:** row degree and pairwise codegree alone upgrade near-Hall to unit Hall.
   **Failed by corpus audit:** existing full-mass reservoir construction has matching half-density
   row/co-degree exponents yet retains an `X^{o(1)}` load loss and potentially macroscopic deficit.
3. **Conjecture:** a sharp recent shadow theorem supplies the coefficient automatically.
   **Failed as direct transfer:** the tight-tree shadow theorem needs a forbidden tight-tree
   certificate absent from the thresholded distance-three relation; its permutation deletion also
   overlaps the already audited chronological-deletion mechanism.
4. **Pivot:** isolate the dimension-sensitive distance-two and distance-four collision clusters
   and exploit multiplicative-threshold closure there. Any useful next theorem must couple those
   clusters to top-shell row survival, not merely repackage common-neighbor counts.

Broad September 2026 arXiv searches on `association`, `shadow`, `switching`, and `threshold`
identified three relevant analogies: support-induced rigidity for nonnegative positive exchanges,
sharp permutation-injection shadow bounds for tight trees, and parity obstructions under signed
switching. None states the required multiplicative-threshold Hall theorem. Sources:
[positive scattering](https://arxiv.org/abs/2609.11606),
[tight-tree shadows](https://arxiv.org/abs/2609.08012), and
[signed switching obstructions](https://arxiv.org/abs/2609.10975).

## Gates

- [x] 0 → 1 in-progress: exact distance-three graph and collision question identified.
- [x] 1 → 2 fully-proven: finite paper proof dependency-closed.
- [x] 2 → 3 formalized: closed Lean theorems, targeted check/build, axiom audit.
- [ ] 3 → 4 publication-ready: not a standalone RH advance; use in coefficient-one expansion
  attack.

## Final audit

`lake env lean GaloisForLFunctions/RHTower/RouteEThreeToggleCommonNeighborRigidity.lean` and its
targeted module build pass. Module is wired into `RHTower.lean`; no umbrella build is run. Axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound`. No forbidden declaration token
occurs.

## Log

- 2026-09-12 — distance-three sign reversal, exact common-neighbor separation, and exact
  distance-six fibre cardinality proved and formalized; distance-two/four threshold clusters become
  next source-expansion target.

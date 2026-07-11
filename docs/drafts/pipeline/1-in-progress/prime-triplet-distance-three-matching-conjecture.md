# Prime-triplet distance-three matching conjecture

- **ID:** `prime-triplet-distance-three-matching-conjecture`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`; full three-toggle matching / static reheating route
- **Scientific status:** `[NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Source:** residue after the one-to-two graph and full-cubulation routes failed, 2026-07-11

## Statement

Let `Q_x` be the finite prime-product downset

```text
Q_x = {S : S finite prime set, product(S)<=x}.
```

Define `H_x` on `Q_x` by joining `S` and `S'` exactly when

```text
#(S symmetric_difference S') = 3.                      (D3)
```

There should exist a source-canonical matching in `H_x` leaving at most
`O_epsilon(x^(1/2+epsilon))` vertices unmatched.

Every edge toggles three prime occupations and reverses Möbius parity. It includes both reactions

```text
vacuum <-> three-particle cluster,
one-particle <-> complementary two-particle cluster,
```

relative to the common support outside the toggled triple.

## Conditional RH theorem `[PROVED; BRIDGE]`

Matched endpoints have opposite signs. If `U_x` is the unmatched set, then

```text
|M(x)| <= #U_x = O_epsilon(x^(1/2+epsilon)),
```

so RH follows from the Mertens criterion.

## Exact Hall target

Let `O_x,E_x` be the odd and even sides and `N_3` the `H_x` neighborhood. Put

```text
d_O^3(x) = max_(A subset O_x) (#A-#N_3(A)),
d_E^3(x) = max_(B subset E_x) (#B-#N_3(B)).
```

By Hall deficiency,

```text
minimum unmatched vertices in H_x = d_O^3(x)+d_E^3(x).  (H3)
```

The exact nonconstructive target is

```text
d_O^3(x)+d_E^3(x) = O_epsilon(x^(1/2+epsilon)).          (HI3)
```

As before, `(HI3)` alone is an RH-strength target. A live route needs a source theorem for its
distance-three neighborhoods.

## Full Boolean bulk `[PROVED; MODEL]`

On an unconstrained Boolean prime sector, fix any triple `T`. Then

```text
S |-> S symmetric_difference T
```

is a perfect matching by distance-three edges. This is stronger than the one-to-two graph: it also
pairs the empty and full patterns on `T`.

The multiplicative quota is therefore the only obstruction to this bulk matching.

## Why the failed facet argument no longer applies

A full rank-three Boolean interval consumes eight faces per maximal top and consequently leaves a
linear facet defect. A distance-three matched edge consumes only two faces. A top-shell facet can
be paired directly with any lower support obtained by deleting three of its occupied primes, or
with a same-scale support obtained by a one-to-two exchange. Since top-shell facets are
asymptotically half of `Q_x`, pairwise capacity is exactly the correct scale; cubical capacity was
not.

## Absolute no-go checks

### Fixed triple

`[REFUTED]` Toggling one cutoff-independent triple leaves a proportional crossing shell and hence
`Omega(x)` unmatched states.

### Full Boolean intervals

`[REFUTED]` Requiring all eight vertices of every active triple to form a disjoint cell is the
retired cubulation conjecture and has the linear facet obstruction `(FD)`.

### One-to-two-only edges

`[RETIRED]` Restricting `(D3)` to cardinality difference one loses the exact Boolean involution. The
one-to-two card exhausted inward/outward shifting and reciprocal allocation, leaving only its Hall
target.

### Arbitrary maximum matching

`[INVALID AS MECHANISM]` Existence of a maximum matching is formal. The square-root deficiency must
come from a theorem about the prime-product downset, not from running a matching algorithm or
counting parity first.

## Candidate moves

### Candidate A: largest-three forest

`[ATTACKED]` Direct every support of rank at least three to the support obtained by deleting its
three largest primes. This is a canonical edge, but many children have the same parent. A rooted
forest matching can use only one child per parent, leaving uncontrolled sibling mass. The rule
supplies reactions, not coverage.

### Candidate B: disjoint block first-fit

`[ATTACKED]` Partition prime labels into triples `T_1,T_2,...` and toggle the first block whose
partner stays below `x`.

The rule is generally not involutive. Toggling `T_j` changes the total product, and can make an
earlier disjoint block admissible at the partner even though it was inadmissible at the original
vertex.

### Candidate C: mutual admissibility graph

`[CONJECTURE; SELECTED]` Keep disjoint ordered blocks `T_j`, but accept an edge only when `j` is the
least admissible block from both endpoints. This defines an honest matching. Vary the block system
by multiplicative scale and prove that a vertex rejected by every mutual block must be saturated in
small primes or lie in a thin quota shell.

The first task is to state a block hierarchy for which mutual rejection has a usable arithmetic
normal form. A fixed block hierarchy is expected to leave linear mass.

### Candidate D: distance-three neighborhood expansion

`[CONJECTURE]` Bypass a constructive rule and prove a source isoperimetric dichotomy: every family
`A` larger than RH scale either has `#N_3(A)>=#A` or contains a common prime-saturation pattern whose
primorial cost forces `#A=O_epsilon(x^(1/2+epsilon))`.

This is admissible only if the saturation pattern is derived from distance-three collision
geometry, rather than chosen to make the conclusion true.

## Boundary cases

- The vacuum is no longer isolated; it is adjacent to every prime triple of product at most `x`.
- A prime in `(x/2,x]` is adjacent to every squarefree semiprime at most `x` avoiding that prime.
- A rank-two facet is adjacent downward/upward through one-to-two exchanges and upward through
  adding three absent primes only when the quota permits.
- Every facet of rank at least three has a product-decreasing edge obtained by deleting any three
  occupied primes.

No rank layer has yet produced a super-square-root Hall obstruction.

## Literature boundary

Boolean interval partitions, Stanley decompositions, and cube tilings are established and killed
the novelty of the full-cubulation object. Focused searches have not yet located the exact graph
`H_x`, a distance-three matching theorem for multiplicatively weighted downsets, or its Mertens/RH
criterion. This is preliminary and does not establish scientific novelty.

## Exact open cores

`[OPEN CORE 1: BLOCK HIERARCHY]` Define a cutoff-adaptive hierarchy of prime triples whose mutual
first-fit edges form a source-canonical matching.

`[OPEN CORE 2: REJECTION NORMAL FORM]` Characterize vertices unmatched by every block in terms of
prime occupation and multiplicative slack.

`[OPEN CORE 3: SQUARE-ROOT BOUND]` Prove the rejection class is
`O_epsilon(x^(1/2+epsilon))` without a Mertens estimate.

`[OPEN CORE 4: FAKE SOURCE]` Test the same hierarchy on a multiplicative weight system with a
different ordered atom sequence; identify exactly which integer-prime property prevents a false RH
analogue.

## Current verdict

`[LIVE OUTLANDISH CONJECTURE; NOT AN RH PROOF]`

This is the minimal combinatorial residue that survives both previous failures: it retains the
three-support locality needed to escape the one-toggle obstruction, restores the full Boolean bulk
involution, and avoids the eight-face cost that killed cubulation. The next decisive object is the
mutual-rejection normal form for a scale-adaptive block hierarchy.

## Gates

- [x] 0 -> 1 in-progress: exact graph, Hall target, conditional RH theorem, full Boolean model,
  predecessor no-gos, and first candidate rules recorded.
- [ ] 1 -> 2 fully-proven: no matching or square-root deficiency theorem exists.
- [ ] 2 -> 3 formalized: deferred until a paper mechanism survives.
- [ ] 3 -> 4 publication-ready: ineligible before proof and broad graph-isoperimetry audit.

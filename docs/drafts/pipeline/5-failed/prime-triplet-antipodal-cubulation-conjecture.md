# Prime-triplet antipodal cubulation conjecture

- **ID:** `prime-triplet-antipodal-cubulation-conjecture`
- **Stage:** 5-failed
- **Type:** FAILED ROUTE; rank-three Boolean-interval cubulation
- **Scientific status:** `[REFUTED]`; top-shell facet density forces a linear exceptional set
- **Source:** pivot from the retired one-prime-to-two-prime fission graph, 2026-07-11

## Statement

Let

```text
Q_x = {S : S is a finite prime set and product_(p in S) p <= x}.
```

There should exist a source-canonical partition of all but
`O_epsilon(x^(1/2+epsilon))` members of `Q_x` into Boolean intervals

```text
[C,C union T] = {C union U : U subset T},               (B3)
```

where `C` and `T` are disjoint prime sets, `#T=3`, and the full interval lies in `Q_x`.

On each interval, define the antipodal involution

```text
C union U  |->  C union (T\U).                          (A3)
```

It changes exactly three prime occupations, reverses parity, and has no fixed points. The
cosmological reading is a static triplet-reheating cell: vacuum and triplet states are paired, as
are every one-particle state and its complementary two-particle state. There is no evolution
parameter.

## Conditional RH theorem `[PROVED; BRIDGE]`

Every cube `(B3)` contains four antipodal pairs, and the two endpoints of each pair have opposite
Möbius sign. Hence the cube's signed contribution is zero. If `E_x` is the exceptional set left by
the conjectural cubulation, then

```text
|M(x)|
  = |sum_(S in Q_x) (-1)^#S|
  <= #E_x
  = O_epsilon(x^(1/2+epsilon)).
```

The Mertens criterion implies RH. The load is entirely in the cubulation and its exceptional-set
bound.

## Why this is not the retired fission graph

The retired route allowed only

```text
C union {p} <-> C union {q,r}.
```

It omitted the other antipodal pair type

```text
C <-> C union {p,q,r}.
```

That omission destroys the Boolean bulk symmetry and forces every cancellation through a
spectator-core allocation. Here all eight patterns on a triple are treated simultaneously.

## Full-cube theorem `[PROVED; MODEL CASE]`

On the unconstrained Boolean algebra of a prime label set containing a fixed triple `T`, the map

```text
S |-> S symmetric_difference T
```

is a perfect parity-reversing involution. Equivalently, the Boolean algebra is partitioned by the
three-cubes obtained after freezing every coordinate outside `T`, and `(A3)` pairs every cube.

Thus the obstruction is not bulk parity, topology, or a shortage of reactions. It is entirely the
multiplicative quota cutting through Boolean cubes.

## Exact cube-admissibility law `[PROVED]`

Fix disjoint `C,T` with `#T=3`, and put

```text
y = x/product(C).
```

The full cube `[C,C union T]` lies in `Q_x` if and only if

```text
product(T) <= y,
```

because the terminal vertex has the largest product and every other vertex is a divisor of it.
Therefore the conjecture is an interval-partition problem for the multiplicative downset `Q_x`:
tile almost every face by a rank-three Boolean interval whose top remains under the quota.

## Fixed-triplet failure `[PROVED; NO-GO]`

No cutoff-independent triple can work. Fix `T={p,q,r}` with product `P_T`. Every squarefree core
`C` disjoint from `T` with

```text
x/P_T < product(C) <= x
```

lies in `Q_x`, but the opposite endpoint `C union T` does not. Such cores have positive density in
that proportional interval, so a fixed-triple antipodal pairing leaves `Omega(x)` states.

The cubulation must therefore be adaptive: the selected triple must depend on the multiplicative
scale and on the occupied support, while the interval selection must remain identical from all
eight vertices of the chosen cube.

## Anti-vacuity rules

1. Arbitrarily pair even and odd squarefree integers. This reads the Mertens imbalance.
2. Solve a maximum matching and call its edges cubes. A valid object is an interval partition by
   full rank-three Boolean cells, with a source-side construction and coverage proof.
3. Select a triple separately at each vertex. The eight vertices must select the same interval;
   otherwise `(A3)` is not an involution.
4. Use a fixed triple or a finite cutoff-independent list. Each produces proportional crossing
   shells unless a cross-cell absorption theorem is proved.
5. Use the simplicial boundary or a discrete Morse vector field. The natural prime-product complex
   has linear total Betti number; antipodal cube pairing is deliberately not an acyclic face
   matching.
6. Invoke a generic Boolean interval decomposition without proving that the interval tops obey the
   product quota and that the uncovered set is RH-scale.

## Candidate moves

### Candidate A: least admissible absent triple

`[ATTACKED]` Given a support, take the three least absent primes whose product fits the available
slack and toggle them.

This is not automatically involutive. After toggling, those primes become occupied, so the partner
usually selects a different triple. The rule must be attached to the frozen core `C`, not chosen
independently from a vertex.

### Candidate B: recursive Boolean interval partition

`[CONJECTURE; SELECTED]` Order potential cube tops by multiplicative weight and recursively remove a
full interval `[C,C union T]` when its eight vertices are still unassigned. Prove that a canonical
priority rule leaves only faces whose every admissible rank-three interval collides with an earlier
cell. Then convert collision saturation into a primorial lower bound on those residual faces.

The nontrivial assertion is not that greedy removal terminates. It is that a residual face blocked
in all three-coordinate directions must carry enough small prime mass to make the total residual
population square-root sized.

### Candidate C: quota-stratified cubical shells

`[CONJECTURE]` Partition by dyadic multiplicative slack

```text
2^j <= x/product(C) < 2^(j+1)
```

and assign each shell a disjoint reservoir of prime triples of product at most `2^j`. This avoids a
single fixed triple and may make interval collisions triangular across shells. The unresolved issue
is that a prime can occur in both the core of one cell and the active triple of another.

## Boundary attacks

### Vacuum and low-rank states

Unlike the one-to-two graph, the vacuum has many neighbors: every prime triple of product at most
`x`. Primes and semiprimes also lie in complete three-cubes whenever two or one additional prime
labels, respectively, fit the top quota. No fixed low-rank Hall obstruction is visible.

### Facets near the quota

A maximal face `S` cannot be the bottom of a nontrivial cube, but it can be any other vertex of a
cube whose bottom removes the occupied part of `T`. Thus the linear family of top-shell facets that
obstructed discrete Morse theory is not automatically exceptional here. A proof must explicitly
assign each facet to a cube reaching downward.

### Shifted-family methods

The previous card proves that ordinary inward and outward prime shifts can both enlarge a
replacement neighborhood. The cubulation cannot inherit a monotone compression theorem for free.
Its prospective invariant is interval collision saturation, not ordinary shadow size.

### Generic interval-partition risk

Boolean interval partitions, Stanley decompositions, and cubical matchings are established parent
subjects. The route is scientifically distinct only if the multiplicative quota forces a new
square-root residual theorem. Merely renaming an interval partition as reheating fails the novelty
gate.

## Exact open cores

`[OPEN CORE 1: CANONICAL CUBULATION]` Give a deterministic, vertex-independent rule producing
pairwise disjoint full intervals `(B3)`.

`[OPEN CORE 2: COLLISION SATURATION]` Characterize residual faces for which every admissible
three-cube intersects a previously chosen cell.

`[OPEN CORE 3: PRIMORIAL COST]` Prove collision saturation forces sufficient small-prime occupation
or multiplicative boundary thickness to bound the residual population by
`O_epsilon(x^(1/2+epsilon))`.

`[OPEN CORE 4: NONCIRCULARITY]` The residual bound must be proved from cube geometry and prime
distribution, not from `M(x)` or a parity count.

## Preliminary verdict

`[ROUTE REFUTED: FIXED-RANK BOOLEAN CUBULATION HAS LINEAR FACET DEFECT]`

Let `N_x=#Q_x`. The squarefree counting theorem gives

```text
N_x = (6/pi^2)*x+o(x).
```

Every squarefree integer `n` in `(x/2,x]` is a maximal face of `Q_x`, because multiplication by any
absent prime takes it above `x`. Hence the number `F_x` of facets satisfies

```text
F_x >= (3/pi^2)*x+o(x).
```

A rank-three Boolean interval has eight faces and contains at most one ambient facet: every
non-top vertex has the interval top as a strict coface in `Q_x`. Any disjoint family of such cubes
therefore covers at most `N_x/8` facets. The exceptional set contains at least

```text
F_x-N_x/8
  >= (9/(4*pi^2))*x+o(x).                               (FD)
```

This is linear, so the conjectured RH-scale cubulation is false.

The same counting argument refutes every fixed-rank `d>=2` Boolean-interval cubulation: a rank-`d`
interval consumes `2^d` faces per possible facet, while the top shell already contains asymptotically
half of all faces. This obstruction is independent of homology and stronger than the earlier
discrete-Morse no-go for the proposed interval partition.

The antipodal **edge** survives: a matching may pair a facet with one lower face without consuming
the other six vertices of a full cube. The next route must therefore use the full distance-three
matching graph directly, allowing both `0<->3` and `1<->2` moves, and must not promote matched edges
to disjoint Boolean intervals.

## Gates

- [x] 0 -> 1 in-progress: exact cube object, conditional RH implication, full-cube model, fixed-cell
  no-go, anti-vacuity rules, and open cores recorded.
- [x] terminal attack: facet density proves the exceptional set is `Omega(x)` by `(FD)`.
- [ ] 1 -> 2 fully-proven: ineligible; conjecture refuted.
- [ ] 2 -> 3 formalized: deferred until a paper mechanism survives.
- [ ] 3 -> 4 publication-ready: ineligible before proof and broad Boolean-partition literature audit.

# Prime-triplet distance-three matching — terminal route record

- **ID:** `prime-triplet-distance-three-matching-conjecture`
- **Stage:** 5-failed
- **Type:** TERMINAL RH ROUTE RECORD; full three-toggle matching / static reheating route
- **Scientific status:** `[CLOSED AS AN RH ROUTE] [NOT AN RH PROOF]`
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

`[REFUTED]` No hierarchy of pairwise disjoint prime triples can have sublinear rejection, regardless
of its ordering, greedy rule, or mutual-admissibility convention. The positive-density obstruction
is proved below.

### Candidate D: distance-three neighborhood expansion

`[CONJECTURE]` Bypass a constructive rule and prove a source isoperimetric dichotomy: every family
`A` larger than RH scale either has `#N_3(A)>=#A` or contains a common prime-saturation pattern whose
primorial cost forces `#A=O_epsilon(x^(1/2+epsilon))`.

This is admissible only if the saturation pattern is derived from distance-three collision
geometry, rather than chosen to make the conclusion true.

## Disjoint-block positive-density obstruction `[PROVED; NOVELTY UNVERIFIED]`

Let `T_j={a_j,b_j,c_j}` be any pairwise disjoint prime triples, ordered so
`a_j<b_j<c_j`. The four antipodal pair classes in one block have larger-to-smaller product ratios

```text
a_j*b_j*c_j,
(b_j*c_j)/a_j,
(a_j*c_j)/b_j,
max(c_j/(a_j*b_j),(a_j*b_j)/c_j).                       (R4)
```

The first three ratios are strictly greater than `2`. Only the fourth can be near `1`.

For each block, call a local pattern **safe lower** if it is the smaller endpoint of its antipodal
pair and its ratio in `(R4)` is at least `2`. Exclude all four upper patterns and, when the fourth
ratio is below `2`, exclude its lower pattern as well.

The density cost of the excluded patterns in block `j` is bounded by a universal constant times

```text
1/(a_j*b_j) + 1/(a_j*c_j) + 1/(b_j*c_j).                (EC)
```

For the potentially near fourth pair, if `c_j>=a_j*b_j` its upper pattern has cost at most
`1/(a_j*b_j)` and its lower near-pattern has cost `1/(a_j*b_j)`; if
`c_j<a_j*b_j`, the corresponding costs are at most `1/(a_j*b_j)` and
`2/(a_j*b_j)`. The other three classes give the remaining terms in `(EC)`.

Because the triples are disjoint,

```text
sum_j 1/(u_j*v_j) < infinity
```

for each selected pair of coordinates: use
`1/(u*v) <= (1/2)*(1/u^2+1/v^2)` and the convergence of the prime reciprocal-square sum. Hence the
sum of the excluded local densities converges. Independence of divisibility conditions on disjoint
prime blocks, expressed by the convergent Euler product, shows that the squarefree integers whose
pattern is safe lower in every block have a positive natural density.

Let `n` be such an integer in `(x/2,x]`. Toggling any prescribed block moves from its lower pattern
to its upper pattern and multiplies `n` by at least `2`, so the partner exceeds `x`. Thus `n` is
unmatched by every block-toggle rule. There are `Omega(x)` such `n`.

Therefore every disjoint-block construction—fixed, scale-stratified, greedy, mutual-first-fit, or
superincreasing—fails by a linear margin. A surviving use of `H_x` must employ an overlapping
triple hypergraph. In particular, near-resonant triples must overlap enough that their exceptional
cylinder costs no longer form a summable family.

## Cofinal persistence obstruction `[PROVED; NOVELTY UNVERIFIED]`

The logarithmic-boundary gate suggests a stronger implementation: construct one matching `M` on
all squarefree positive integers and recover the cutoff matching by restriction.  Put

```text
C_M(x) = #{ {a,b} in M : min(a,b)<=x<max(a,b) }.
```

If `M` were perfect, its restriction to `Q_x` would leave exactly `C_M(x)` vertices unmatched.
This would be a genuinely persistent, zero-preserving matching architecture.  No such architecture
can have RH-scale boundary defect.

Fix `0<alpha<1/4`, and let `Y=X^alpha`.  The standard fixed-parameter smooth-number asymptotic,
together with squarefree sieving, gives `Omega_alpha(X)` squarefree `Y`-smooth integers in
`[X/2,X]`.  Let `n` be one of them and let `m` be any distance-three neighbor.  If the toggled
triple removes `d` occupied primes, there are four cases:

```text
d=0: |m-n| >= 29n,
d=3: |m-n| >= (29/30)n,
d=1: |m-n| = (n/p)|qr-p| >= n/Y,
d=2: |m-n| = (n/(pq))|r-pq| >= n/Y^2.
```

Here `p,q<=Y`, while a prime cannot equal a product of two distinct primes, so the displayed
integer differences are at least one.  Uniformly,

```text
|m-n| >> X^(1-2alpha).                                      (PG)
```

This already kills cutoff-local matching, without assuming persistence. Fix `theta<1` and choose
`alpha<(1-theta)/2`. For all sufficiently large `X`, every one of the above `Omega_alpha(X)`
vertices is isolated in the subgraph of `H_X` containing only edges with

```text
|m-n| <= X^theta.
```

Thus every fixed sublinear-transport implementation leaves `Omega_theta(X)` vertices unmatched.
In particular, overlapping **near-resonant** triples cannot be the missing mechanism: positive
density smooth states force genuinely macroscopic numerical jumps.

Each matched edge contains at most two of these smooth vertices.  Integrating the crossing count
and truncating at `2X` therefore gives

```text
integral_1^(2X) C_M(t) dt >>_alpha X^(2-2alpha).             (IC)
```

Indeed, an edge incident to `n in [X/2,X]` contributes at least a constant multiple of
`X^(1-2alpha)` inside `[1,2X]`; if its other endpoint lies beyond `2X`, its truncated contribution
is even larger.

If `C_M(t)=O_epsilon(t^(1/2+epsilon))`, the same integral is
`O_epsilon(X^(3/2+epsilon))`.  Taking

```text
0<epsilon<1/2-2alpha
```

contradicts `(IC)`.  Consequently no cutoff-independent global distance-three matching has
RH-scale restriction defect.

This does not refute a theorem constructing a different matching for every `x`: such a theorem
would control the exact sum `M(x)` and needs no analytic convergence to `Xi`.  It does prove that
the matchings must undergo macroscopic cutoff-dependent rewiring.  Hence this route cannot supply
a quantized pairing invariant stable through finite-prime boundary layers, and finite matching
successes cannot be assembled by persistence.

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
criterion. A second focused search found no parent for the global-matching boundary-crossing
obstruction. Its only external input is classical: the Ivić--Tenenbaum estimate

```text
Psi_(mu^2)(x,y) = Psi(x,y)/zeta(2) * (1+o(1))
```

in the range containing `y=x^alpha`, combined with the Dickman--de Bruijn fixed-parameter
asymptotic for `Psi`.  See the summary and equation (1.19) in
https://link.springer.com/article/10.1007/s00209-024-03601-w.  Absence from focused search is not a
novelty proof; the obstruction remains `[NOVELTY UNVERIFIED]`.

## Retired open cores

`[RETIRED CORE 1: LOCAL TRIPLE DESIGN]` Disjoint block hierarchies are refuted by the
positive-density cylinder obstruction. Overlapping near-resonant hierarchies are refuted by the
smooth-state sublinear-transport obstruction. Cutoff-independent global matchings are refuted by
the integrated persistence obstruction.

`[RETIRED CORE 2: REJECTION NORMAL FORM]` Every concrete block or local-transport family has been
refuted. There is no surviving source rule whose rejection class could be normalized.

`[RETIRED CORE 3: SQUARE-ROOT BOUND]` The remaining statement is the direct Hall inequality
`(HI3)`. Without an independent matching rule, it is the RH-strength target rather than an
intermediate theorem.

`[RETIRED CORE 4: FAKE SOURCE]` No hierarchy survived long enough to define a nontrivial fake-source
test.

## Current verdict

`[CLOSED AS AN RH ROUTE; NOT AN RH PROOF]`

This is the minimal combinatorial residue that survives both previous failures: it retains the
three-support locality needed to escape the one-toggle obstruction, restores the full Boolean bulk
involution, and avoids the eight-face cost that killed cubulation. The disjoint-block mechanism is
now terminally refuted. Near-resonant overlapping designs and persistent global pairings are also
terminally refuted. Any survivor must be cutoff-dependent, extensively rewired, and use
macroscopic numerical jumps on a positive-density smooth sector. No concrete source rule with
those properties remains; the residue is the direct Hall inequality `(HI3)`.

## Gates

- [x] 0 -> 1 in-progress: exact graph, Hall target, conditional RH theorem, full Boolean model,
  predecessor no-gos, and first candidate rules recorded.
- [x] 1 -> 5 failed: disjoint, near-resonant, and cutoff-persistent implementations refuted; only
  the naked RH-strength Hall inequality remains.
- [ ] 1 -> 2 fully-proven: closed; no matching or square-root deficiency theorem exists.
- [ ] 2 -> 3 formalized: deferred until a paper mechanism survives.
- [ ] 3 -> 4 publication-ready: ineligible before proof and broad graph-isoperimetry audit.

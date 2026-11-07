# Isolated primes obstruct fixed-point localization

- **ID:** hhac-isolated-prime-fixed-points
- **Stage:** 1-in-progress
- **Type:** OBSTRUCTION AND COMPONENT CLASSIFICATION

## Exact question

Can a self-map of the actual prime complex, homotopic to the identity,
have a fixed set of square-root size?

## Arithmetic obstruction

Every prime `N/2 < p ≤ N` is an isolated vertex: a face containing a
second prime has product at least `2p>N`. Any path starting at this vertex
is constant. Consequently every self-map homotopic to the identity fixes
all these vertices, regardless of how the map is constructed.

The unconditional finite statement is an injection from the upper-half primes
into the fixed-point set. A square-root localization would therefore require
a square-root bound on `π(N)−π(N/2)`, contrary to its prime-number asymptotic.
The existing prime-window theorem gives at least `N/(4 log N)` such primes
eventually. Dividing by `√N` tends to infinity. Thus no family of maps homotopic
to the identity can have an eventually `C√N`-sized fixed set, for any constant `C`.

## Positive survivor

For `N≥4`, remove the isolated upper-half prime vertices. The remaining
subcomplex is path connected: every remaining vertex is joined to prime two,
and every point of a face is joined inside that face to one of its vertices.
Thus the path components are exactly one connected core and one singleton
for each upper-half prime. This classifies the component obstruction and
identifies the necessary relative localization target.

The core retains the sphere summands indexed by composite odd squarefree
integers in `(N/2,N]`; the removed zero-spheres contribute the prime terms.
Any Euler cancellation mechanism must account for those positive component
contributions against the higher-dimensional core. Removing the isolated
points does not remove their arithmetic contribution.

The exact core bouquet remains a formalization obligation: its complementary
facets are precisely the original complementary facets with at least two
vertices. Every proper subface lies in the core star of two, so the existing
cone-bouquet theorem supplies a homotopy equivalence with these
positive-dimensional spheres. This is stronger than path connectedness.

Define the core nerve by retaining exactly the prime faces whose vertices
all satisfy `2p≤N`. Its signed augmented face count satisfies

`coreEuler(N) = M(N) + #{p prime : N/2<p≤N}`.

Equivalently its reduced Euler characteristic is `−M(N)` minus the number
of isolated primes. This is an exact arithmetic correction for any relative
or connected-core localization.

## Paper argument

In barycentric coordinates, the coordinate of an upper-half prime is
always zero or one. Its value is one exactly at that vertex. Continuity
on the connected homotopy interval makes that coordinate constant, proving
the fixed-point assertion. For the core, join a point to a vertex in its
support by a straight segment, then join that vertex to two along the
edge whose product is at most `N`. These paths also prove the component
classification; they do not give a contraction of the core. Splitting the
face sum into core faces and removed singleton faces gives the Euler identity,
since each removed singleton has sign `−1` in the augmented count.

## Scope and proof status

`PrimeComponentRigidity.lean` verifies the finite injection, fixed-point cover
bound, and exact path-component classification, with only the standard three
axioms. The asymptotic capstone and core Euler correction are under verification.

The argument is elementary topology applied to the existing prime complex;
no priority claim is made for homotopy invariance of components. Its consequence
is a constraint on the proposed arithmetic fixed-point mechanism. The route
cannot be closed before the quantitative obstruction and its positive core
replacement both pass direct Lean audits.

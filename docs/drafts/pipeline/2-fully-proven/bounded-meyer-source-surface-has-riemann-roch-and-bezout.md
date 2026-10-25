# The bounded Meyer source surface has Riemann–Roch and Bézout

- **ID:** bounded-meyer-source-surface-has-riemann-roch-and-bezout
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Q-II; bounded full-Hasse source orbit and actual source trace.
- **Statement:** Restricting the genuine Meyer surface to bounded centered source orbits gives unconditional RR, Bézout, and ampleness; principal and numerical equivalence agree there exactly when every critical Xi zero is simple.

## Exact scope

Retain both fibre classes and precisely the actual sources with bounded
Hilbert–Schmidt convolution orbit. The earlier paper identifies these with
critical highest jets. This is a restriction of the genuine source carrier;
it does not assert the original all-source Q-II endpoint.

## Dependency-closed paper proof [PROVED HERE]

The carrier is a complex linear subspace. Its ordinary sharp-square trace is
a sum of nonnegative critical value squares: off-line values vanish. Restrict
the existing polar surface, using `PolarSurface.restrict` from
`ArithmeticOrientationGeometry/SectionsOnTheOrbitOfACycle.lean`. Its defect
is therefore nonnegative, and the existing positive-cone RR, Bézout, and
ampleness theorems apply with their hypotheses proved on this carrier.

Its trace radical is precisely the value-zero part, already classified in
the bounded-orbit algebra paper. Numerical cycles additionally have both
pole degrees zero. If every critical point is simple, the highest-jet
condition and zero values kill every Xi jet, so the source is a genuine
boundary; balancing poles makes the whole cycle principal. A multiple
critical point supplies an actual nonprincipal highest-jet class with all
values zero, giving the reverse implication. The cone lineality is the same
numerical radical, by the semidefinite defect Cauchy inequality, so its
pointedness modulo principal cycles has the same exact criterion.

## Corpus audit

The restriction construction and orbit RR theorem already exist in
`SectionsOnTheOrbitOfACycle`. The new input is the exact actual-source
bounded-orbit carrier, including the surviving highest nilpotent jets.
The previous source trace radical theorem and finite causal synthesis are
required. The unconditional simple-critical producer was located and its
source proof read, as recorded below.

## Status

The paper proof is dependency-closed on the bounded-orbit classification,
its trace-radical theorem, and the existing polar-surface restriction and
positive-cone theorems. Complete unrun draft:
`/tmp/QIIBoundedMeyerSourceSurfaceDraft.lean`. Lean certification pending;
external novelty unverified.

The simple-critical witness search found the unconditional theorem
`RHTower.DeletionMixedRefinement.exists_high_simple_critical_xi` in
`ArithmeticJointJetExclusion.lean`, whose proof uses the existing superlinear
simple-critical census. Hence the restricted carrier has actual sources of
strictly positive ordinary trace, with isolated simple-critical support above
every prescribed height. Its raw source value one has trace exactly one.
This strengthens nontriviality beyond a possible nilpotent-only survivor.

## Exact restricted cone and proof details

Let W consist of triples (a,b,g) with g in the critical highest-jet carrier,
and let S_W be the original pairing restricted to W. Both fibres lie in W.
Define E_W by pulling back the genuine cohomological degree cone of
`MeyerSourceIntersectionSurface`; its defining reserve is the real linear
trace degree of the actual source sharp product. The existing identity
identifies E_W with the positive cone of S_W.

For g in this carrier the full trace expansion has zero summands off the
line, because g has zero values there. At a critical point the sharp value
is the conjugate of g's value, so each remaining summand is |M g(rho)|².
Convergence is the existing actual trace-class summability theorem. Thus
S_W has nonnegative defect and satisfies the Hodge index unconditionally.
The existing positive-cone theorems now give RR, Bézout, ampleness, and
additive closure, with their order inputs discharged on W.

A numerical-null x in W has both pole degrees zero, by testing the two
fibres. Its remaining mixed readings vanish precisely when all Mellin
values vanish, by the already proved trace-radical classification inside
the bounded carrier. Hence restricted numerical nullity is the restriction
of full numerical nullity. If critical points are simple, those zero values
and the carrier condition kill every lower jet; full source spectral
synthesis gives a cap preimage. Zero pole degrees give exactly its principal
cycle. Conversely a multiple critical point supplies a nonprincipal highest
jet source with all values zero. Balancing its pole degrees gives a numerical
null cycle in W, contradicting numerical/principal equality.

If x and -x are effective, their nonnegative ample degrees sum to zero.
Ampleness therefore makes x numerical-null. Conversely any numerical-null
cycle and its negative have square and ample degree zero, hence are both
effective. This proves the exact lineality statement and the identical
critical-simplicity criterion for pointedness modulo principals.

Finally W is the whole source cycle space exactly when every source has
bounded full-Hasse centered orbit, already classified as RH plus simplicity.
The one fixed Xi-avoiding compact source detects this coverage obstruction.
This is why the unconditional restricted theorem does not solve full Q-II.

At each simple critical point supplied above any height, the actual point
source has only its zeroth jet, belongs to W, and has self trace exactly one:
critical reflection fixes the point, its multiplicity is one, and its source
value is one. This gives cofinally many strictly positive source witnesses.

Actual candidate: `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/BoundedMeyerSourceSurface.lean`; unverified and unwired. Scratch draft retained until actual audit succeeds.

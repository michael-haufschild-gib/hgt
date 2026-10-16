# Complete CHMD Doob source graph and ground direction

Status: FORMALIZED; final audits complete.
Classification: PROGRESS on the actual signed-source domain. RH remains unproved.

## Exact object

Let Theta be the existing positive Riemann kernel. Put
mu(dx) = Theta(x) cosh(x/2) dx.
On edge coordinates (t,x), retain both:

- archimedean measure omega(t) Theta(x) Theta(x+t) dt dx, with t>0;
- for every natural n, the pushforward of
  (Lambda(n)/sqrt(n)) Theta(x) Theta(x+log n) dx to (log n,x),
  with the existing atom convention at n<2.

Their sum is kappa. The endpoints are x and x+t. The literal graph consists of
(v,g) in L2(mu) plus L2(kappa) with g(t,x)=v(x)-v(x+t) almost everywhere.
Its signed energy is Q(v,g)=||g||^2-||v||^2.

## Dependency-closed proof

The strictly positive density of mu makes Lebesgue measure absolutely continuous
with respect to mu. Both endpoint pushforwards of every edge measure are absolutely
continuous with respect to mu. For the archimedean part, use the product projection
and measure-preserving shear. For each prime line, use translation invariance.
These null-set statements survive the countable sum.

Suppose graph pairs converge in the source and edge L2 spaces. A subsequence of
source functions converges mu-almost everywhere; endpoint nonsingularity transports
this to both endpoints of kappa. A further subsequence of edge functions converges
kappa-almost everywhere. Uniqueness of scalar limits identifies the edge limit
with the difference of the source limit. The graph is therefore closed and is a
complete Hilbert subspace of the orthogonal L2 sum. Its source projection is
injective: completion introduces no edge vector invisible in the source carrier.

Every original compact C2 real profile belongs to this graph. Its mass norm squared
is exactly the original cosh mass. Weighted integral conversion, product Fubini and
the already-proved summability of the complete prime jump integrals give

Q(compactLift(v)) = archJump(v) + sum_n primeJump(v,n) - coshMass(v^2)
                 = markovEnergy(Theta v).

No prime, prime power, archimedean contribution or cosh term is discarded.
Moreover Q+2||v||^2 is exactly the graph norm squared, so the signed source is
realized on a complete Hilbert graph with its original mass subtraction.

The constant profile c has mass norm squared c^2/2 and energy -c^2/2. Conversely,
zero edge vector implies equality of profile values for almost every positive
archimedean shift, because that density is strictly positive. The inverse shear
turns this into equality at almost every ordered pair x<y. Swapping coordinates
and Fubini force a global almost-everywhere constant. Thus equality
Q=-||v||^2 occurs exactly in the constant-profile direction.

Finally, close the linear span of the actual compact-test lifts inside this graph.
This compact-test completion is complete and its source projection remains
injective. It is kept separate from the maximal graph.

## Exact limitations

This proves neither equality of the compact-test completion with the maximal
domain nor a selfadjoint-operator representation. It does not exclude energies
between the ground level and zero, establish primitive nonnegativity, eliminate
the original CHMD convolution defect, or prove RH. The simple ground direction
does not supply the missing primitive spectral gap.

## Formalization

- `formal/GaloisForLFunctions/RHTower/CHMDClosedJumpGraph.lean`:
  general closed difference graph, Hilbert completeness, source injectivity,
  shifted norm identity and actual-function energy representation.
- `formal/GaloisForLFunctions/RHTower/CHMDDoobSourceGraph.lean`:
  literal full source measures, endpoint nonsingularity, compact C2 admission,
  exact original energy identity, unique constant ground direction and faithful
  compact-test completion.

Both imports are wired once in `formal/GaloisForLFunctions/RHTower.lean`.
Validation: both --old leaf builds passed; both final plain `lake env lean` audits
passed with empty output. All 71 declarations passed a /tmp axiom audit, using
only propext, Classical.choice and Quot.sound. Mathlib-name probe passed. Index
refresh and global formal lint passed; existing large-file warnings remain.
Scoped and new-file whitespace checks passed. No heartbeat increase, full or
umbrella build, numerical experiment, web lookup, subagent, commit or push.

SHA-256 at final direct audit:
- CHMDClosedJumpGraph.lean: `9371c79bfdb7a126750efce316d981696daa5a6336efbe84b8df71604d5c6bc9`
- CHMDDoobSourceGraph.lean: `f2e0fdd3f3d63167706f81e4fc46b04e5d767fe7fc45f9cd6af1625ba57c542c`


## Next conjecture

Use the actual closed source domain and its arithmetic chain sectors to determine
whether the mass-orthogonal primitive sector has negative energy. The ground
direction has now been identified, but its complement's sign has not. A further
generic spectral-gap criterion would restate the obstacle rather than resolve it.

Cleanup complete: all 19 owned temporary files removed and absence verified; audited source hashes unchanged; all owned process handles terminal. Final whitespace checks passed.

# Prime-Ising collision-free spectral-depth universality law

Status: Stage 3 — formalized in Lean 4; final umbrella audit pending  
Lean target: `GaloisForLFunctions.RHTower.PrimeIsingCollisionFreeSpectralDepthUniversalityLaw`  
Novelty: `[NOVELTY UNVERIFIED]`

## Theorem-generated discovery

`PrimeIsingTreeFixedModalClosureNoGo` constructs an exact spectral packet for every balanced finite
prime Ising tree, proves packet cardinality `2 ^ |V|`, and proves the corresponding upper bound on
every derivative jet.

`DirectionalVandermondePhaseJet` proves the complementary lower statement: a nonzero exponential
packet with injective frequencies has a nonzero derivative among its first `r` jets at every base
point.  The prime-Ising module imports the shared finite exponential-derivative engine but never
connects its exact packet to this nonflatness theorem.

## Statement

Assume the frequencies in the exact balanced spectral packet of a finite prime Ising tree are
injective on the packet index type.  Then one simultaneous certificate holds:

1. packet cardinality is exactly `2 ^ |V|`;
2. packet evaluation is exactly the balanced partition;
3. all derivative jets have modal width at most `2 ^ |V|`;
4. at every complex base point, some derivative of order below packet cardinality is nonzero.

Thus collision-free finite-tree carriers have exact spectral depth: they possess both the existing
modal upper bound and a new base-point-uniform Vandermonde nonflatness bound.

## Dependency-closed proof

1. Index packet amplitudes and frequencies by `Fin packet.length`.
2. The exact finite-sum representation identifies packet evaluation with the HT phase polynomial.
3. If its amplitude vector were zero, packet evaluation would vanish at the origin.
4. Exact balanced-packet representation and unit central normalization instead give value `1` at
   the origin.  Hence the amplitude vector is nonzero without any coefficient-by-coefficient
   premise.
5. Apply directional Vandermonde phase-jet nonvanishing using frequency injectivity.
6. Transport the result through exact packet representation and adjoin the existing cardinality
   and modal-width laws.

No computation or new analytic hypothesis is introduced.  Frequency injectivity is the precise
collision-free boundary; repeated prime labels or additive frequency collisions are not hidden.

## Novelty audit

Corpus audit: exact prime-Ising packet width and generic directional nonflatness exist separately.
No theorem supplies the collision-free prime-Ising spectral-depth certificate or derives nonzero
amplitudes from unit central normalization.

Literature audit: deferred until exact Lean proof succeeds, per research protocol.

## Lean verification

- Exact source check passed:
  `lake env lean GaloisForLFunctions/RHTower/PrimeIsingCollisionFreeSpectralDepthUniversalityLaw.lean`.
- Wired into `GaloisForLFunctions.RHTower`.

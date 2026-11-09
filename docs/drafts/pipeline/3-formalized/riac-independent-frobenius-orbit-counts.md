# Independent Frobenius orbit counts

- **ID:** RIAC-independent-Frobenius-orbits
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); classical finite-field calibration
- **Source:** [discriminant-cover construction](riac-discriminant-cover-signed-counts.md)
- **Statement:** For any finite group acting on a finite label set, an explicitly constructed finite extension supplies exactly `q^n` Frobenius-stable tuple orbits. The proof uses actual bijections and no Möbius cancellation theorem.

## Construction

Let `F` have `q` elements, let a finite group `G` act on `n` labels `I`,
and let `E/F` be the finite extension of degree `|G|`.
The group acts on `E^I` by `(g·x)_i=x_(g⁻¹·i)`.
Coordinate Frobenius commutes with this action. The counted finite set is

`{O∈E^I/G : Frob(O)=O}`.

These are stable extension-field orbits, not merely orbits of `F^I`.
The construction retains tuples with repeated coordinates.

## Proof

For any equivariant map `φ` on a finite `G`-set, transporters from `x` to
`φ(x)` are empty unless their orbit is fixed. A nonempty transporter is a
stabilizer torsor. Orbit–stabilizer therefore gives

`Σ_g #{x:g·x=φ(x)} = |G| · #{φ-stable orbits}`.

For the arithmetic twists, Frobenius generates `Gal(E/F)`. Since every
element order divides `|G|`, sending Frobenius to any chosen `g∈G` defines
an actual homomorphism `Gal(E/F)→G` and hence an action on `I`.

Choose a normal basis `b_σ=σ(θ)`. The formulas

`a ↦ (x_i=Σ_σ a_(σ⁻¹·i) b_σ)`,

`x ↦ (coefficient of b_1 in x_i)`

are inverse bijections between `F^I` and the Galois-compatible tuples.
Compatibility with the generator is equivalent to compatibility with all
automorphisms. Each permutation-twisted Frobenius fibre consequently has
exactly `q^n` points. Substitution in the transporter identity gives the
asserted orbit count.

## Exact scope

No factorization statistic or scalar Möbius degree sum enters the count.
The comparison with discriminant-cover fibres, including collisions, is
separate. No identification with the integer prime cutoff or bound on
`Σ_p index_p(N)=1−M(N)` is supplied.

## Formalization

[FiniteFieldOrbitCounts.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/FiniteFieldOrbitCounts.lean):

- `transporterStabilizerEquiv`, `transporter_exists_on_orbit`.
- `orbitTransportersEquiv`, `sum_card_transporters`.
- `galoisCompatibleTuplesEquiv`, `galoisCompatibleTuples_card`.
- `frobeniusTwistedTuplesEquiv`, `frobeniusTwistedTuples_card`.
- `frobeniusTupleOrbits_card`, `arithmeticFrobeniusOrbits_card`.

Direct leaf check and ten transitive axiom audits; only `propext`,
`Classical.choice`, `Quot.sound`.

## Literature boundary

The arithmetic is classical. [Gadish, §§1.1 and 3.2](https://arxiv.org/html/1703.01710v2)
treats rational orbits and stabilizer-weighted Frobenius statistics for
ramified covers; its affine quotient specialization includes this point
count. Here the permutation case is proved directly by normal-basis and
transporter bijections. No new point-count theorem is claimed.

# Operator-only adelic gluing cannot give Weil's diagonal

- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Obstacle:** B133.
- **Retired claim:** A rational-torus-invariant finite part determined by
  the hyperbolic Laplacian and prime adjacency operators alone reproduces
  Weil's off-diagonal and the scattering-tower packet diagonal on the
  constructed adelic carrier.

## Exact obstruction

The user-supplied [structural refutation](../2-fully-proven/hat-weils-diagonal-is-not-one-glued-carrier-object.md)
is accepted as correct. Diagonal orbit functions at every degree are
isomorphic under commuting adelic isometries. Consequently every uniform
regularization of those functions gives a degree-independent diagonal.
The coupled packets retain a nonconstant discriminant defect against the
scattering tower. Leaf parity and Hecke support give independent
off-diagonal obstructions. Changing the scalar finite-part convention
does not repair the proposed gluing.

## Strongest positive survivors

- The [full projective carrier](../3-formalized/full-projective-adelic-carrier-retains-every-degree.md)
  retains all positive integer degrees under the actual discrete action
  of the finite Weyl conjugate of `SL₂(ℚ)`.
- [Prime Hecke operators](../3-formalized/prime-hecke-operators-on-the-projective-adelic-carrier.md)
  are actual commuting adjacency sums on that carrier, preserving
  prequotient neighbour multiplicities.
- The [critical product finite part](../3-formalized/a-height-finite-part-of-the-critical-adelic-green-product.md)
  has a sharp height threshold and an absolutely summable regularized
  height-row remainder; it is not the required additive Weil kernel.
- The [intrinsic scattering tower](../3-formalized/the-scattering-tower-and-the-weil-diagonal.md)
  independently realizes the complete Weil functional on compact C²
  autocorrelations with a fixed local scalar counterterm.

All four survivors have paper proofs and Lean formalizations with
standard-axiom audits. The supplied stronger refutation and its new
structural invariants have paper proofs; their Lean status is recorded
on the supplied card, which is maintained separately.

## New insight and surviving work

Carrier geometry and a correctly normalized scattering diagonal are
distinct constructions. An arithmetic comparison needs additional
structure carrying the contact and discriminant data; it cannot be
obtained from the stated local operators by a uniform torus finite part.

The [actual local Green kernel](../3-formalized/the-local-green-kernel-on-adelic-vertices.md)
is now formalized on all projective vertices, including the tempered edge
and its restriction to Weil prime-power coefficients. This closes the local
source-identity gap without reviving the rejected global assertion.
The [minimal-branch classification](../3-formalized/the-minimal-branch-of-the-adelic-green-kernel.md)
identifies the actual weighted walk Green kernel exactly for `s≥1/2`.
For `0<s<1/2`, the reflected branch removes an explicitly identified nonzero
positive harmonic remainder. The critical occupation sum converges pointwise.
The [marked-pair potential](../3-formalized/the-discriminant-as-a-marked-green-potential.md)
recovers the discriminant from actual local ratios and harmonic Green diagonals.
Its finite support, simultaneous adelic invariance, and exact specialization to
the original degree configuration are formalized with standard-axiom audits.
The extra degree-one mark retains the arithmetic separation that uniform
diagonal torus regularization loses.
The [finite prime-fibre sum](../3-formalized/the-prime-fibres-recover-arithmetic-contact.md)
recovers arithmetic contact from minimal Green sources on the finite vertex
product. Its exact cutoff subtraction does not supply a full global point source
or separate descent to the arithmetic quotient.
No replacement global Green construction is claimed.

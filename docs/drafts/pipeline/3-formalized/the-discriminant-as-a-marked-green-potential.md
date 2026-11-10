# The discriminant as a marked Green potential

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** B133: recover the discriminant defect without reviving operator-only gluing.
- **Statement:** The actual local Green kernels define a symmetric, simultaneously
  adelic-invariant potential of two finite vertices whose value between the base
  vertex and the degree-n vertex is the normalized cyclotomic different.

For distinct local vertices set
`D_p(v,w) = −log R_p(v,w) − log p ((p+1)G_{p,1}(v,v)−1)`;
set `D_p(v,v)=0`. Sum over the finitely many places where the vertices differ.
The definition uses the intrinsic radial coordinate and the unit-source Green
kernel, with a marked pair as additional data.

The degree identity follows from
`R_p(base,x_n)=p^(−v_p(n))`,
`(p+1)G_{p,1}(v,v)−1=1/(p−1)`, and local torsion adjunction.
The resulting sum is `selfIntersection n`.

This is a replacement invariant on marked pairs. It is not a scalar
on the original unmarked quotient, a global Green resolvent, or a proof of the
coupled-packet/scattering comparison. The accepted
[gluing refutation](../2-fully-proven/hat-weils-diagonal-is-not-one-glued-carrier-object.md)
remains in force.

## Lean status

`TheDifferentAsAMarkedGreenPotential.lean`, namespace `MarkedGreen`:

- `localTerm_finite_support`: the sum is genuinely finite on restricted-product vertices.
- `markedDifferent_symm`, `markedDifferent_smul`: symmetry and simultaneous adelic invariance.
- `markedDifferent_degree`, `markedDifferent_originalDegree`: exact equality to
  `selfIntersection n`, including the original degree-one/degree-n pair.

Plain `lake --old env lean` passes with no warnings. All five audited
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

The [walk Green identification](the-prime-walk-selects-the-green-kernel.md)
is formalized: the harmonic excess equals the sum of return probabilities
after time zero. Thus each local different is radial logarithmic cost minus
`log p` times this return mass.

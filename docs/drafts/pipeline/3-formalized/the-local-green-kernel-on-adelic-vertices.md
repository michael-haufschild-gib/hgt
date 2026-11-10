# The local Green kernel on adelic vertices

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** B133: actual local resolvents on the projective carrier.
- **Statement:** On `V_p=PGL₂(ℚ_p)/PGL₂(ℤ_p)`, the intrinsic radial
  coordinate `R(g)=|det g|_p/(maxᵢⱼ|gᵢⱼ|_p)²` defines the symmetric
  fundamental kernel
  `G_s(x,y)=p^s/(p^(2s)−1) R(g_x⁻¹g_y)^s`, `s>0`, satisfying
  `(p^s+p^(1−s)−A_p)G_s(x,·)=δ_x` for actual prime adjacency.

## Proof mechanism

Integral basis changes preserve the maximum entry norm; scalar changes
cancel in `R`. Normalize a matrix by a largest nonzero entry and apply
the corpus's DVR Smith normal form. Its divisibility chain gives a
projectively equivalent `k diag(1,d) l`, with `k,l∈GL₂(ℤ_p)` and
nonzero `d∈ℤ_p`.

For `|d|_p<1`, multiply by the established neighbour representatives
`diag(1,p)` and `[[p,−b],[0,1]]`, `b∈𝔽_p`. The label `b=0`
has radial value `p|d|_p`; every other label has `|d|_p/p`.
For `|d|_p=1`, all `p+1` values are `1/p`. Integral changes of basis
permute the neighbour set, so the law holds at every vertex.
The resulting radial recurrence fixes the coefficient
`(p^s−p^(−s))⁻¹` by its unit source at the base vertex.

This identifies an actual fundamental kernel, including the tempered edge
`s=1/2`. A bounded Hilbert-space resolvent and the global adelic
regularization require separate domain and convergence arguments.
The [operator-only gluing obstruction](../5-failed/the-operator-only-adelic-gluing-cannot-give-weils-diagonal.md)
is accepted: this local theorem cannot supply the rejected global
identification with Weil's diagonal.

The [minimal-branch theorem](the-minimal-branch-of-the-adelic-green-kernel.md)
identifies this source kernel with the actual weighted walk sum exactly for
`s≥1/2`; below it, a nonzero positive harmonic remainder survives.

## Lean status

- `HTGeometry.exists_smithNormalForm`: integral diagonal reduction.
- `AdelicAdjacency.neighborRep`, `neighbors_smul`, `card_neighbors`:
  actual local correspondence and multiplicities.
- `AdelicRadial.exists_integral_diagonal`, `localRatio_smul`,
  `localRatio_symm`, `localRatio_eq_one_iff`: formalized in
  `TheRadialCoordinateOnAdelicVertices.lean`, standard-three-axiom audits.
- `AdelicGreen.radialSum_eq`, `localGreen_resolvent`,
  `localGreen_tempered_resolvent`: actual neighbour recurrence and unit source.
- `localGreen_apartment`, `weilPrimeKernel_eq_localGreen`: the scalar tree
  profile and Weil prime-power coefficient are restrictions of this kernel.
- Both source files pass plain `lake --old env lean`; all audited declarations
  use only `propext`, `Classical.choice`, and `Quot.sound`.

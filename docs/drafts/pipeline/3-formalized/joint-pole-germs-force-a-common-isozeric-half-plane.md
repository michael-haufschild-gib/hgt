# Joint pole germs force a common isozeric half-plane

- **ID:** B130-uniform-local-residue-classification
- **Stage:** 3-formalized
- **Type:** THEOREM — formalized
- **Source:** Exact local residue classification and compact divisor rigidity.

## Theorem

Let `x(t)` be actual gauge fibres and let `U(t,s)` be jointly holomorphic
near `(0,1)`, with `U(0,1)≠0`, agreeing locally with `(s-1)F_{x(t)}(s)`
for real `t` and `Re s>1`. Then there exist `ε>0` and `1/2<σ<1` such
that every `|t|<ε` satisfies
`Σ_p |χ_{x(t)}(p)-1| p^(-σ)<∞`.

Thus all nearby real fibres preserve ζ's zero multiplicities on one
common half-plane extending left of one. No separate holomorphic prime
phases or summability premises are required.

## Dependency-closed proof

For a nonnegative Dirichlet series converging at every real exponent
above one, let `S` be its convergence set. Suppose convergence fails at
`σ>1-r`. Then `S` is nonempty, bounded below by `σ`, and its infimum
`σ_c` satisfies `σ≤σ_c≤1`. Thus `σ_c` lies inside `B(1,r)`.
The series is holomorphic on `Re s>σ_c`.

If `P D=N` holds on the Euler part of `B(1,r)`, with `P,N` holomorphic
there and `P` nonzero at every real point in the disk, analytic uniqueness
extends the identity over the connected intersection
`B(1,r)∩{Re s>σ_c}`. The quotient `N/P` then continues `D` through
`σ_c`, contradicting the existing local Landau theorem. Consequently the
series converges at every real exponent greater than `1-r`.

Apply this to the cleared paired prime-defect derivative of a gauge
regularization `U` analytic on `B(1,r)`, `0<r≤1/2`, and nonzero on its
real diameter. Its Schwarz conjugate regularizes the opposite gauge.
The existing paired identity gives `P D₁=N`, with
`P=2Z U conj(U(conj s))`. The numerator is analytic on the disk because
the paired remainder is analytic on `Re s>1/2`; the denominator is
nonzero on its real diameter. Removing the positive logarithmic weight
gives quadratic prime summability at every `τ>1-r`. Taking `τ=1-r/2`
and applying weighted Cauchy–Schwarz yields
`Σ_p |χ_x(p)-1|p^(-(1-r/8))<∞`.

Joint holomorphy and the nonzero central residue give one product
neighborhood on which all spectral slices are analytic and nonzero.
Shrink its radius below the local Euler agreement radius and `1/2`.
The preceding explicit exponent then works for every real parameter in
this smaller neighborhood. The Euler deformation theorem gives each
actual continuation and its ζ zero multiplicities on the common
half-plane. The individual local residue theorem identifies each given
spectral germ with this canonical continuation.

No summability, prime-phase holomorphy, or global continuation is assumed.

## Corpus boundary

`local_residue_isozeric_continuation` gives an exponent separately for
each fibre. `eventually_gauge_order_eq` assumes continuation and locally
uniform convergence on a whole half-plane. The target starts with a
joint pole germ and derives a common half-plane. Corpus searches found
these predecessors, `landau_local_summability_transfer` for ordinary
Dirichlet series on closed disks, and the positive Dirichlet power-series
estimates, not the joint-gauge implication. The radius transfer is an
adaptation of existing Landau machinery to local cleared identities. No external novelty claim. B130's arithmetic
Stepanov estimate remains unproved.

## Lean result

`GaugeDeformations/JointPoleRigidity.lean` proves:

- `summable_of_pole_disk_identity`: a local cleared identity gives
  convergence at every exponent above the disk's left edge.
- `quadratic_prime_summable_of_residue_disk`: quadratic prime energy
  converges at every `τ>1-r`.
- `absolute_prime_summable_of_residue_disk`: absolute prime energy
  converges at `1-r/8`.
- `joint_pole_common_absolute_summability`: one exponent works for
  every nearby real parameter.
- `joint_pole_common_isozeric_halfPlane`: all given pole germs extend
  to a common half-plane with exactly ζ's zero multiplicities.

The last theorem assumes only joint analyticity at `(0,1)`, nonzero value
there, and local agreement with actual regularized gauge fibres. It
requires no prime-coordinate analyticity or global continuation.
Final direct Lean check passed without warnings. All four capstone
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

[Complex normal summability](joint-gauge-germs-force-complex-normal-summability.md).

# Square-root discrepancy of actual elliptic orientation quotients

- **ID:** RIAC-elliptic-orientation-quotients
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Curve orientation counts](riac-curve-orientation-square-root.md)
- **Statement:** The original orientation-cover and ordinary tuple-orbit counts on the actual elliptic curve satisfy a square-root-scale discrepancy bound.

For `C:Y²Z=X³−XZ²` over `F₃`, take the actual extension `E/F₃` of
degree `n!`. Let `B_n` count Frobenius-stable `S_n`-orbits of `C(E)^n`.
Let `A_n` count stable orbits of `C(E)^n×{±1}` under
`σ·(x,u)=(σ·x,sign(σ)u)`, with Frobenius fixing the orientation label.
These are literal finite arithmetic orbit counts, defined without Möbius
coefficients, Euler-product coefficients or a presumed cancellation law.
Repeated points and both labels in degrees zero and one are retained.

For every finite point permutation, signed transporter counting gives

`n! (A_n−B_n)=Σ_x Σ_(σ·x=Frob(x)) sign(σ)`.

A collision supplies an odd swap stabilizer, pairing opposite transporter
signs. An injective tuple with invariant support has a unique transporter;
its sign equals the intrinsic permutation sign on that support. A moving
support has no transporter. Each `n`-point support has exactly `n!`
orderings, through an explicit bijection with `Fin n ≃ T`. Canceling
`n!` proves `A_n−B_n=J_n`, the signed stable-configuration sum.

The [actual closed-place and orientation comparison](riac-elliptic-stable-orientation.md)
then gives, for every `n≥0`,

`A_n−B_n=(-1)^n(E_n−O_n)`,

`|A_n−B_n|≤8(n+1)²(√3)^n`.

All residue-field, Frobenius-cycle and curve-root inputs are proved.
At `N=3^n`, this is square-root scale with a quadratic logarithmic loss.

Lean sources:
[TupleOrientationCounts.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/TupleOrientationCounts.lean),
[EllipticOrientationCounts.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/EllipticOrientationCounts.lean).
Main declarations: `pointTuple_orientationCount_sub`,
`arithmeticEllipticOrientationCover_sub`,
`arithmeticEllipticOrientationCover_eq_signedDivisors`,
`arithmeticEllipticOrientationCover_bound`.

Direct final Lean checks passed; all 12 transitive axiom audits across
these two modules use only `propext`, `Classical.choice`, `Quot.sound`.

The concrete elliptic orientation-quotient comparison is formalized. The
general hyperelliptic construction and any estimate for the integer local
indices `Σ_p index_p(N)=1−M(N)` remain open. A curve count does not by
itself control the integer product-height cutoff.

# Fifth native source at the compensation zero

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Target:** The complete native fifth even source is positive definite at the unique positive zero `τ` of the center compensation source `G`.

The established sign law is
`G(x)=Φ(x)²[3+2x(log Φ)'(x)]`, with one positive zero. Every constant
matrix correction `H(x)+G(x)K` equals `H(τ)` there. Thus this sign is a
necessary condition for every constant-load certificate, independently
of the chosen load directions or coefficient matrix.

`exists_thetaCuspCompensationNeutralAnchor` locates the zero at
`5 < π exp(2τ) < 45/8`. The crossing satisfies
`τ G'(τ) < -3 Φ(τ)²` (`ThetaCuspCompensationNeutralAnchor.lean`).

The complete fifth source is strict at scale seven, and one cross-load
is strict near the origin, near scale seven, and on a cofinal ray.
Neither result determines the source at the compensation zero.

Every individual atom's fifth even matrix is now strict when its own scale
is at least five; see [the atom theorem](../3-formalized/theta-cusp-fifth-even-first-atom.md).
Thus the first atom is strict throughout the neutral interval. The complete
source still requires control of unequal atom pairs and the omitted tail.
The three-atom Cauchy bound is
`n!·8000 f₁(x)² exp(-(529/50)q)/(3/20)^n`, valid for `q≥3`.

The retained affine target is `A(q)+8zB(q) ≻ 0` for `q≥5` and
`0≤z≤5^15/(20^5 q^15)`, where `Aᵢⱼ=P_(i+j)(q²,2q)` and
`Bᵢⱼ=P_(i+j)(4q²,5q)`. The actual weight `z=exp(-3q)` lies in this
interval by the exponential tangent inequality. An explicit quadratic
reserve is needed to absorb pairs `(1,3)`, `(2,3)` and the omitted tail.

**Unproved:** the transition-source sign. No positivity or obstruction
is asserted at `τ`.

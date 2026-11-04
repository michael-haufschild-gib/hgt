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

The leading pair now retains an explicit quadratic reserve on the full ray
`q≥5`: its normalized Gaussian-coordinate matrix is at least `(49/1000)I`.
See [the leading-pair theorem](../3-formalized/theta-cusp-fifth-even-leading-pair-reserve.md).
The remaining terms are the unequal pairs `(1,3)`, `(2,3)` and the Cauchy tail;
pure-atom matrices are positive.

A stronger sufficient conjecture is positivity of the complete native fifth
source whenever `q≥5`. Stationary exponential bounds reduce the remaining
pair estimates to finite rational bounds on their shifted polynomial
coefficients. These remainder bounds are not yet proved.

**Unproved:** the transition-source sign. No positivity or obstruction
is asserted at `τ`.

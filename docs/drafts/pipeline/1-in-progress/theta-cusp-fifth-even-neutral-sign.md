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

The proposed exact test uses the eighth Gaussian Hermite polynomial
with variance `8q`, where `q=π exp(2x)`. At `q=7` this is the already
used common-kernel vector. Its radial energy and the full fifth matrix
must be compared with the actual theta remainder on the transition
interval. A directional positive sign alone would not establish the
matrix target; a negative sign would exclude every constant matrix load.

**Unproved:** the transition-source sign. No positivity or obstruction
is asserted at `τ`.

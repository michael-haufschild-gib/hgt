# Fixed pair head with a positive all-rank Gaussian margin

- **Stage:** 5-failed
- **Wall:** Σ6
- **Failed claim:** Some fixed ordinary-pair cutoff dominates a positive multiple of the Gaussian moment form at every finite rank.

Every fixed head decays as frequency tends to positive infinity. Gaussian
Hankel completeness therefore gives a finite polynomial direction below
any proposed positive margin, including the explicit uniform remainder
`E_M(a)` for `a>0`. This does not prove that any head is negative.

**Positive survivor:** all Gaussian lower margins are exactly the pointwise
lower bounds of the head. For one atom, every finite section is strictly
positive definite despite the absence of a positive rank-uniform margin.
The exponential Gaussian remainder bound survives; it cannot be absorbed
by a fixed head through this proposed margin.

The [paper proof and Lean capstones](../3-formalized/full-theta-fixed-head-gaussian-margin.md)
are complete and axiom-audited. The full-theta all-rank sign remains open.

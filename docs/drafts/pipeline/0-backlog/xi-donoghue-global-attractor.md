# Global attraction for the Xi Donoghue map

- **Stage:** 0-backlog
- **Type:** CONJECTURE; strengthening of the existing dynamical endpoint family
- **Statement:** An upper-half-plane orbit of the normalized Xi Donoghue map that fails
  to converge to `i` falsifies RH.

## Source and distinction

`Bottcher.HalfPlane.xiDonoghue_cayleyRadius_strict_decrease_of_rh` gives a strict radial
Lyapunov function away from `i`. The Cayley-conjugate orbit stays in a compact disk
strictly inside the unit disk. Continuity and compactness should force the radius
limit to vanish: a nonzero subsequential limit would strictly decrease the same
limiting radius.

This excludes nonconvergent aperiodic orbits as well as periodic ones. It is a
stronger obstruction within the existing dynamical family, not another count for
the stationary equation.

## Open obligations

- Audit existing compact strict-Lyapunov convergence infrastructure.
- Prove convergence for the actual disk conjugate and transfer back through Cayley.
- Search for an existing equivalent Xi global-attractor theorem; audit the final endpoint.

No global-attraction theorem is yet claimed.

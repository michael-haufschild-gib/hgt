# Elapsed heat pays for surviving pairs

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Obstacles:** B13, B112; small-time nonreal heat counts.
- **Statement sought:** For every `q>0` and `t>0`, the upper nonreal roots of a real polynomial heat flow satisfy
  `Σ_z ((Im z)²+2t)^q ≤ Σ_{upper initial roots} (Im z)^(2q)`.
  Transfer this inequality to the actual Riemann heat flow, with the right side understood through finite-sum bounds. It would give `N(t) (2t)^q ≤ 2 Σ_upper depth^(2q)`.
- **Difference from a depth cutoff:** The corpus quartic `(X²+1)(X²+9)` disproves counting only initial depths above `sqrt(2t)`. The proposed moment cost permits the deep pair to support the shallow pair, while charging every surviving pair elapsed time.
- **Novelty search:** Searches for heat power-depth moments, logarithmic majorization and moment count budgets surfaced squared-depth majorization, global quadratic dissipation and the quartic cutoff counterexample; no general positive-exponent budget surfaced.

## Candidate mechanism

For upper heights `a,b>0`, horizontal separation `d`, and derivative weights `A=F'(a)`, `B=F'(b)`, pairing both roots with their conjugates gives the numerator
`2[(aA+bB)d²+(a²−b²)(aA−bB)]`.
It is nonnegative whenever `y F'(y)` is nonnegative and increasing. For `F_t(y)=(y²+2t)^q`, this follows from
`d/dy [y F_t'(y)] = 4q y (y²+2t)^(q−2) (2t+q y²) ≥ 0`.
The explicit time derivative cancels the force of each root's own conjugate. Other conjugate pairs and real roots dissipate the remaining moment. A real collision removes a term `(2t)^q`, hence gives a downward jump.

Remaining proof work: audit the paired-force formula with multiplicities; carry comparison through polynomial collisions; transfer finite root sums to `H_t`, using continuous cutoffs away from the real axis. No Lean result claimed or counted.

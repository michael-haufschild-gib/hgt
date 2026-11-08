# Elapsed heat pays for surviving pairs

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacles:** B13, B112; small-time nonreal heat counts.
- **Statement sought:** For every `q>0` and `t>0`, the upper nonreal roots of a real polynomial heat flow satisfy
  `Σ_z ((Im z)²+2t)^q ≤ Σ_{upper initial roots} (Im z)^(2q)`.
  Transfer this inequality to the actual Riemann heat flow, with the right side understood through finite-sum bounds. It would give `N(t) (2t)^q ≤ 2 Σ_upper depth^(2q)`.
- **Difference from a depth cutoff:** The corpus quartic `(X²+1)(X²+9)` disproves counting only initial depths above `sqrt(2t)`. The proposed moment cost permits the deep pair to support the shallow pair, while charging every surviving pair elapsed time.
- **Sharpness target:** An isolated quadratic pair `(X−x)²+y²` attains equality until `t=y²/2`; the coefficient `2` of elapsed heat cannot be increased.
- **Novelty search:** Searches for heat power-depth moments, logarithmic majorization and moment count budgets surfaced squared-depth majorization, global quadratic dissipation and the quartic cutoff counterexample; no general positive-exponent budget surfaced.
- **Existing boundary to sharpen:** `RHTower/AdmissibleFunctionalShape.lean` tests isolated pair terms and gives ordinary convexity as a sufficient condition. Grouping complete conjugate packets may enlarge the dissipating class to logarithmically convex profiles; `|y|^p` with `0<p<1` would distinguish the two criteria.

## Candidate mechanism

For upper heights `a,b>0`, horizontal separation `d`, and derivative weights `A=F'(a)`, `B=F'(b)`, pairing both roots with their conjugates gives the numerator
`2[(aA+bB)d²+(a²−b²)(aA−bB)]`.
It is nonnegative whenever `y F'(y)` is nonnegative and increasing. For `F_t(y)=(y²+2t)^q`, this follows from
`d/dy [y F_t'(y)] = 4q y (y²+2t)^(q−2) (2t+q y²) ≥ 0`.
The explicit time derivative cancels the force of each root's own conjugate. Other conjugate pairs and real roots dissipate the remaining moment. A real collision removes a term `(2t)^q`, hence gives a downward jump.

The paired-force condition may admit an exact classification: positivity for every `a,b>0` and every horizontal separation is equivalent to `g(y)=yF'(y)` being nonnegative and increasing. Equal heights with nonzero separation force `g≥0`; unequal heights with zero separation force monotonicity. This is convexity in logarithmic height, and explains why sharp depth cutoffs lie outside the admissible class.

For the power profile, monotonicity also has an algebraic proof:
`y²(y²+c)^(q−1) = [y²/(y²+c)] (y²+c)^q`.
Both factors are nonnegative and increasing for `c≥0`, `q>0`, `y>0`. This avoids differentiating a negative power.

For collision comparison, use the continuous corrected action
`J_q(t)=Σ_upper [((Im z)²+2t)^q−(2t)^q]`.
At simple times its derivative is at most `−2q(2t)^(q−1) N_upper(t)`.
Integrating and using nonincreasing nonreal count recovers monotonicity of
`J_q(t)+(2t)^q N_upper(t)`, including real collisions.
An initial offset `c=ε+2t`, `ε>0`, keeps the corrected weight differentiable
at real roots even at time zero; taking `ε↓0` recovers the stated finite
polynomial budget.

Remaining proof work: connect the finite paired field to polynomial zero velocities;
carry comparison through collisions; transfer finite root sums to `H_t`, using
continuous cutoffs away from the real axis. No contribution counted yet.

## Lean certificate for the paired mechanism

`ArithmeticElectrostatics/ConjugatePairsDissipateLogarithmicDepth.lean` proves
the exact classification (`conjugatePairWork_nonneg_iff`), admissibility of every
nonnegative exponent, the finite packet drift inequality, its stability under
additional downward velocity, and the actual chain-rule derivative of the
elapsed-depth weight. Direct Lean check passes; all five audited capstones use
only `propext`, `Classical.choice`, `Quot.sound`.

`ArithmeticElectrostatics/TheConjugatePacketPaysElapsedHeat.lean` identifies
the complex reciprocal field with the paired kernel and proves the same drift
inequality for a complete finite conjugate packet, including any finite real
exterior. Both capstones pass direct Lean check with the same standard axioms.
Multiplicity across collisions and the polynomial/entire-flow comparison remain
unformalized.

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
- **Existing boundary to sharpen:** `RHTower/AdmissibleFunctionalShape.lean` tests isolated pair terms and gives ordinary convexity as a sufficient condition. Grouping complete conjugate packets admits profiles convex in logarithmic height; `|y|^p` with `0<p<1` distinguishes the two criteria.

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
Equivalently, on `[a,b]` compare the continuous function
`J_q(t)+(2t)^q N_upper(b)`. Its forward derivative is nonpositive because
`N_upper(b)≤N_upper(t)`. Endpoint comparison then gives the full moment law,
without integrating the discontinuous count.
For a finite polynomial divisor and `q>0`, continuity at time zero suffices:
the comparison theorem uses derivatives only at interior positive times,
and the baseline `(2t)^q` vanishes at zero. No initial derivative or offset
regularization is needed.

For the polynomial comparison, first take an initially separable polynomial:
its heat discriminant is a polynomial in time, nonzero at time zero, so only
finitely many collision times occur. Constant real perturbations `p+ε` avoid
the finite critical-value set and approximate arbitrary nonzero real `p`.
Formalized continuity of finite root moments permits removing initial
separability once the separable polynomial budget is proved.
The corpus `polynomialPencil_separable_of_parameter_not_mem`, with pencil
direction `Q=1`, supplies the finite exceptional set for constant perturbations.
Fixed root cardinality upgrades locally uniform polynomial convergence to
continuity of nonnegative weighted root sums: a bounded cutoff detects any
escaping multiplicity copy, and the complementary weight gives the upper bound.

For the entire-function transfer, `xiRealApprox` consists of finite initial
zero copies and its heat converges below the Gaussian-growth horizon
(`tendstoLocallyUniformly_polyHeat_xiRealApprox`). On any finite nonreal target
set, choose `δ>0` below every absolute imaginary part. The continuous weight
`min(1, |Im z|/δ) ((Im z)²+2t)^q` equals the full elapsed weight on that set,
vanishes on the real axis, and never exceeds the nonreal moment. Weighted
zero-sum semicontinuity then transfers the polynomial budget. Positive-time
moment monotonicity extends a bound below the growth horizon to every later
time. The same cutoff can remove initial separability without asserting
continuity of the discontinuous nonreal count.

Remaining proof work: the polynomial budget and its transfer to the actual
initial divisor. Global moment comparison at positive times is formalized;
it does not by itself control the initial trace.
No contribution counted yet.

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

`ArithmeticElectrostatics/ThePolynomialHeatZerosHaveTheirReciprocalVelocity.lean`
proves the polynomial backward heat equation, analytic branches at simple
zeros, and their exact reciprocal-field velocity. Six audited declarations
pass direct Lean check with the standard axioms above.

`ArithmeticElectrostatics/TheSimpleHeatPacketPaysElapsedDepth.lean` proves the
upper-zero velocity comparison with the finite packet, the actual elapsed-depth
drift inequality, and `heatUpperElapsedDepthDrift_nonpos_forward`: after every
positive time, a punctured forward interval satisfies the drift inequality for
all nonnegative powers and offsets. Compact forward simplicity is proved by
the corpus, not assumed in this capstone. All three capstones pass direct Lean
check with the standard axioms above.

`ArithmeticElectrostatics/TheElapsedDepthActionIsContinuous.lean` proves that
every continuous real-axis-vanishing weight has a continuous global heat-zero
sum at positive times. In particular, the full corrected elapsed-depth action
is continuous through collisions for every real exponent. Both capstones pass
direct Lean check with the same standard axioms.

`ArithmeticElectrostatics/TheElapsedDepthActionHasItsZeroVelocityDerivative.lean`
identifies the corrected action's derivative with the actual zero velocities
and proves `J_q′(t) ≤ −2q(2t)^(q−1) N(t)` on punctured forward intervals,
with both conjugate halves counted. All three capstones pass direct Lean
check with the same standard axioms.

`ArithmeticElectrostatics/TheHeatDivisorPaysElapsedDepth.lean` proves that
`M_q(t)=Σ_nonreal m_z ((Im z)²+2t)^q` is antitone for `q≥0`, `t>0`,
including every collision. It also proves `(2b)^q N(b)≤M_q(a)` for `0<a≤b`.
All four capstones pass direct Lean check with the same standard axioms.

`HTGeometry/PolynomialRoots/WeightedSumContinuity.lean` proves convergence
of every continuous nonnegative root sum from locally uniform convergence,
a nonzero limit, and fixed root cardinality. Constant perturbations preserve
all nonnegative depth powers, including at multiple roots. All three
capstones pass direct Lean check with the same standard axioms.

`ArithmeticElectrostatics/ThePolynomialElapsedDepthActionHasItsDerivative.lean`
proves a local enumeration of every simple heat fibre, the exact corrected-action
derivative, and its bound by the full nonreal count. For every initially separable
nonzero real polynomial, every `q>0`, and `t≥0`, it proves the full elapsed moment
is at most the initial depth moment, through all later collisions. The exact
nonreal-moment identity is included. All five capstones pass direct Lean check
with the same standard axioms.

`ArithmeticElectrostatics/ThePolynomialHeatClockComposes.lean` proves the
polynomial heat semigroup, nonreal-count monotonicity between arbitrary times,
compatibility of real and complex heat, and commutation with constant addition.
All five capstones pass direct Lean check with the same standard axioms.

`ArithmeticElectrostatics/ThePolynomialHeatCollisionsAreFinite.lean` proves
that an initially separable nonzero complex polynomial has finitely many
nonsimple heat fibres. Its time resultant specializes without monic
normalization, and every real time admits a punctured forward interval of
simple fibres. All four capstones pass direct Lean check with the same
standard axioms.

`ArithmeticElectrostatics/ThePolynomialElapsedDepthActionIsContinuous.lean`
proves continuity of nonnegative weighted polynomial heat-root sums and of
the corrected elapsed-depth action on `[0,∞)`, including collisions. At zero,
every positive exponent recovers the initial depth moment. All four
capstones pass direct Lean check with the same standard axioms.

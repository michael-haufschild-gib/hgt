# Elapsed heat pays for surviving pairs

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacles:** B13, B112; small-time nonreal heat counts.
- **Statement:** For every `q>0` and `t>0`, with analytic multiplicities,
  `Σ_upper(H_t) ((Im z)²+2t)^q ≤ Σ_upper(H_0) (Im z)^(2q)`.
  This holds for every nonzero real polynomial and for the Riemann heat
  divisor. The entire-function initial sum is an extended nonnegative sum;
  no summability hypothesis is imposed. Consequently,
  `N(t)(2t)^q ≤ 2 Σ_upper(H_0) (Im z)^(2q)`.
- **Sharpness:** An isolated quadratic pair attains equality until collision.
  Every coefficient greater than `2` fails already for `X²+1` at `t=1/4`.
- **Contribution count:** One, including the paired-kernel classification,
  collision comparison, polynomial approximation, entire transfer, and sharpness.

## New mathematical content

The complete conjugate-pair interaction is dissipative exactly when
`g(y)=yF′(y)` is nonnegative and increasing. This is convexity in logarithmic
height. It admits every positive depth exponent, including powers below one;
ordinary convexity in height does not capture this class.

Every surviving root consumes elapsed time inside its depth power. This
replaces the false hard-cutoff rule: the corpus quartic `(X²+1)(X²+9)` permits
a deep pair to support a shallow one. The new moment law charges that support
without assigning independent lifetimes to initial pairs.

Corpus searches for heat power-depth moments, logarithmic majorization and
moment count budgets surfaced squared-depth majorization, global quadratic
dissipation and the quartic cutoff counterexample. No general positive-power
elapsed budget surfaced. The initial budget need not be finite, and no
finite-layer exclusion or RH proof is claimed.

## Proof

1. For upper heights `a,b>0`, derivative weights `A,B`, and horizontal
   separation `d`, clearing the two distances gives paired numerator
   `2[(aA+bB)d²+(a²−b²)(aA−bB)]`. Equal heights force nonnegativity of
   `yF′(y)`; vertical alignment forces monotonicity. These conditions also
   suffice for every pair.
2. For `F(y)=(y²+c)^q`, write
   `yF′(y)=2q [y²/(y²+c)] (y²+c)^q`. Both factors increase for `c≥0`,
   `q≥0`, and `y>0`. With `c=2t`, explicit time differentiation cancels
   the velocity `−1/y` from the root's own conjugate. Other pairs and real
   exterior roots contribute nonpositive work.
3. Subtract the real-axis baseline to form the continuous action
   `J_q(t)=Σ_nonreal m_z[((Im z)²+2t)^q−(2t)^q]`.
   Simple-fibre zero velocities give
   `J_q′(t)≤−2q(2t)^(q−1)N(t)`. On `[a,b]`, the continuous function
   `J_q(t)+(2t)^qN(b)` has nonpositive forward derivative because the
   nonreal count decreases. Forward-interval comparison passes through
   collisions and proves monotonicity of the full moment at positive times.
4. An initially separable polynomial has a time resultant nonzero at zero,
   hence only finitely many collision times. The corrected polynomial action
   is continuous at zero for `q>0`; its initial baseline vanishes. The same
   comparison therefore gives the initial polynomial budget.
5. Constant real perturbations avoid the finite critical-value set.
   Fixed-degree root-sum continuity removes initial separability. On a
   finite nonreal target set choose `δ>0` below all absolute imaginary parts;
   `min(1, |Im z|/δ)((Im z)²+2t)^q` is a continuous minorant, vanishes on
   the real axis, and equals the full target weight. This avoids asserting
   continuity of the nonreal count.
6. Canonical `xiRealApprox` roots are exact finite initial multiplicity copies.
   Their heat converges below the Gaussian-growth horizon. Weighted zero-sum
   semicontinuity transfers every finite initial budget. Positive-time
   monotonicity extends it to every later time. Extended nonnegative sums
   handle both finite and infinite initial mass. Reflection identifies the
   full budget with twice its upper half.
7. The exact quadratic flow is `X²+c ↦ X²+c−2t`. Its sole upper root has
   squared depth `c−2t`, proving equality and sharpness of the coefficient.

## Lean certificate

All paths below are relative to `formal/GaloisForLFunctions/ArithmeticElectrostatics/`.

| Module | Audited capstone |
|---|---|
| `ConjugatePairsDissipateLogarithmicDepth.lean` | `conjugatePairWork_nonneg_iff` |
| `ThePolynomialHeatDivisorPaysElapsedDepth.lean` | `polynomial_upper_elapsed_moment_le_initial` |
| `TheHeatDivisorPaysElapsedDepth.lean` | `antitoneOn_heatElapsedDepthMoment` |
| `TheInitialDivisorPaysElapsedDepth.lean` | `heat_upper_elapsed_moment_le_initial` |
| `TheInitialDivisorPaysElapsedDepth.lean` | `nonrealCount_elapsed_power_le_twice_initial_upper` |
| `TheElapsedHeatCoefficientIsSharp.lean` | `quadratic_upper_elapsed_moment_eq`, `elapsed_heat_coefficient_is_sharp` |

Every listed module passes direct `lake --old env lean` checking. Every
listed capstone's transitive `#print axioms` contains only `propext`,
`Classical.choice`, and `Quot.sound`. Supporting root enumeration, finite
collision, weighted-continuity, derivative, and comparison modules were
checked directly as well. Finished modules are wired into their umbrellas.

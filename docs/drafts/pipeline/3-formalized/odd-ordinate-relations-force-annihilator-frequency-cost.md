# Odd ordinate relations force annihilator frequency cost

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Obstacles:** B13, B112; simultaneous positive annihilation of finite vertical patterns.
- **Statement:** For an odd list of `q` target ordinates, put `Delta=abs(sum gamma_j)`, let `H` be positive tail mass at abscissa `beta`, and let `J=sum w_d log(n_d)` be its first logarithmic moment. If every target evaluation has norm at most `epsilon`, then `2H <= Delta J + q sqrt(2H(H-1+epsilon))`. Signed repetitions encode arbitrary odd integer relations. Exact zero-sum lists therefore force `(q^2-2)H >= q^2` at exact annihilation.
- **Novelty:** The consecutive-harmonic and sparse first/fourth-harmonic bounds do not control arbitrary approximate additive relations or the first frequency moment. This theorem retains relation error and weighted frequency cost together. Near-unit exact annihilation with `2q^2(H-1)<=1` forces `Delta J>=H`.

## Mechanism

For a monomial of log frequency `L`, multiply its `q` target phases. Their product is `exp(-i L sum gamma_j)`, while the product of `q` ideal cancelling phases is `-1`. Telescoping gives
`2 <= L Delta + sum_j abs(1+exp(-i L gamma_j))`.
Integrate against the positive damped coefficients. At each target, the exact squared phase defect is `2(H-1+Re P(beta+i gamma_j))`. Weighted Cauchy-Schwarz bounds the first phase defect by `sqrt(2H(H-1+epsilon))`, giving the claimed tradeoff.

## Proof

For unit complex numbers `u_j`, finite product telescoping gives
`abs(prod u_j-(-1)^q) <= sum abs(u_j+1)`: at each step write
`u A-(-1)B=u(A-B)+(u+1)B`, with both multiplying factors of norm one.
Since `q` is odd, the triangle inequality and
`abs(exp(i x)-1)<=abs(x)` give the displayed monomial inequality.
Each supported nonconstant logarithmic frequency is positive. Multiplication by
`w_d>=0` and exchange of finite sums therefore give
`2H <= Delta J + sum_j sum_d w_d abs(u_j+1)`.

The unit norm identity `abs(u+1)^2=2+2 Re u` and the exact Dirichlet expansion yield
`sum_d w_d abs(u_j+1)^2=2(H-1+Re P(beta+i gamma_j))`.
Weighted Cauchy-Schwarz, `Re P<=abs(P)<=epsilon`, and `H>=0` bound every
inner first moment by `sqrt(2H(H-1+epsilon))`. This proves the tradeoff.

If the ordinate sum and every evaluation vanish, a target exists because `q` is
odd, and cancellation of the constant term gives `H>=1`. Squaring
`2H<=q sqrt(2H(H-1))` and dividing by `2H>0` gives
`(q^2-2)H>=q^2`, hence `H>1`.

More generally, exact annihilation and `2q^2(H-1)<=1` imply `H<=Delta J`:
the squared error term is `2q^2 H(H-1)<=H<=H^2`, so it is at most `H`.
Thus mean logarithmic frequency `J/H` is at least `1/Delta` when `Delta>0`.

Dependencies: finite product telescoping; existing exact Dirichlet expansion;
`HTGeometry.norm_exp_ofReal_mul_I_sub_one_le`; existing weighted Cauchy-Schwarz
`GaloisForLFunctions.HTGeometry.sq_sum_weighted_le`. No unproved analytic input.
This mass/frequency tradeoff and its exact-relation consequence count together.

## Lean certificate

Module: `GaloisForLFunctions/ArithmeticPositiveDuality/OddOrdinateRelationsForceFrequencyCost.lean`.

- `odd_ordinate_accuracy_frequency_tradeoff`: full accuracy/mass/frequency inequality.
- `odd_ordinate_zero_relation_mass_gap`: exact-relation bound `(q^2-2)H>=q^2`.
- `odd_ordinate_near_unit_frequency_cost`: `Delta J>=H` in the stated near-unit range.
- `one_lt_mass_of_odd_zero_relation`: strict exclusion of unit mass.

Direct audit: `lake --old env lean GaloisForLFunctions/ArithmeticPositiveDuality/OddOrdinateRelationsForceFrequencyCost.lean` passed without warnings. All four capstones have exactly `[propext, Classical.choice, Quot.sound]` as axioms. Wired into `ArithmeticPositiveDuality.lean`; umbrella not compiled. No new analytic assumptions or RH claim.

# A sub-Weyl source bound lowers the heat floor

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** Original obstacle A5: an unconditional critical-line exponent
  below `1/6`, followed by a heat coefficient below `2/3`.

## Candidate

The `A B A³B` logarithmic block should give critical-line exponent `33/200`.
Together with the interior points `(11/18,1/9)`, `(5/7,1/14)` and
`(5/6,2/53)`, its linear interpolation profiles should give eventual
order-uniform slice positivity at heat `(133/200)/log|t|`.

The fifth-derivative dual estimate has leading correlation term
`(Th)^(11/30) N^(-1/5)`. Weyl differencing with
`H ≍ N^(36/41) T^(-11/41)` therefore gives weighted block term
`T^(11/82) N^(5/82)`, equal to `T^(27/164)` at `N=sqrt(T)`.
The existing `kth_derivative_test` at order five contributes secondary
correlation term `(Th)^(5/8) N^(-13/16)`. After differencing this gives
weighted term `T^(75/328) N^(-173/1312)`. Use trivial bounds below `t^(33/100)`, the direct fourth-derivative test
up to `t^(2/5)`, the fourth-derivative dual route up to `T^(97/200)`,
and the fifth-derivative dual route up to `T^(101/200)`. Each interval gives
`O(t^(33/200))`. The direct fourth-derivative interval is necessary:
the dual route's `TH/N²` error is too large near `N=T^(33/100)`.
The fourth-derivative dual bound already exists in
`RHTower/ZetaWeylCorrelationBound`; its differencing is implemented in
`RHTower/ZetaElevenEighteenthsWeylBlock`.

Use the exact two-series Gaussian AFE at cutoff `sqrt(t)`, with
`T=t/(2*pi)`. Truncate both series near `t²`; their absolute tails are
`O(t^(-1/2))`. Every remaining block lies in the existing Weyl range.
Beyond `N=T^(101/200)`, both weights pay `sqrt(t)/N`, giving block exponent
`2/3-101/200=97/600<33/200`. The finite dyadic decomposition costs
`O(log t)`. No second stationary-phase transformation is needed.

At `Re s=5/6`, the generic fifth-derivative secondary term and the sharp
fourth-derivative main term meet at `N=t^(15/53)`, both with exponent
`2/53`. The resulting slice slopes are `3/100`, `3/13`, `23/53`, `29/53`.
At heat coefficient `133/200`, their limiting saddle gaps are respectively
`8803/4000000`, `6/845`, `161/28090`, `459/70225`, all positive.

## Formalization

- Checked: the actual fifth dual derivative, its weighted exponential sum,
  stationary-phase correlation bound, and uniform Weyl differencing, ending in
  `ArithmeticHarmonicAnalysis.norm_prefix_sq_le_fifthWeyl`.
- Pending: the exponent comparisons and short-block splice; scale-difference
  bounds for the exact dual AFE weight. A mean-value
  estimate cancels the Mellin denominator before integration; positive and
  negative contours then give the required dyadic variation.
- Pending: finite critical-line AFE transfer, the `5/6` line bound, all four
  strip profiles, and the order-uniform heat conclusion.

The published Bourgain pair in `BourgainLogExponentPair` is a target with an
unproved analytic premise, not an available subconvexity theorem. Neither new
zeta exponent nor the heat conclusion is yet certified.

# Local heat zero counts uniform down to zero time

- **ID:** wd-heat-uniform-local-zero-count
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [WD source-extinction investigation](../1-in-progress/wd-directed-source-extinction.md); [small-time heat-count programme](../1-in-progress/heat-count-small-time-growth.md)
- **Statement:** For sufficiently large `X`, every finite set of zeros of `H_t` with `|Re z-X| ≤ 1` has total multiplicity at most `C log X`, uniformly for `0 ≤ t ≤ 1/8` and `t log X ≤ 1`.

## Contribution and remaining obstacle

This discharges the local zero-count input listed for the mean-field
persistence problem `(N₁)`. The bound also holds at every earlier heat
time `0 ≤ s ≤ t` in the stated range. It includes collisions through
analytic multiplicity.

It does not bound `nonrealZeroCount t`, establish `(N₁)` persistence, or
prove WD extinction. The uniform total nonreal count and the signed
source-cap upper estimate remain open.

## Exact Lean statements

Namespace: `RHTower.DeBruijn`.

- `HeatEulerAnchor.lean`:
  `norm_xiLine_sixteen_le_eight_mul_norm_riemannHeat` proves
  `‖xiLine X 16‖ ≤ 8 * ‖riemannHeat t (X-16i)‖` for `0<t≤1/8`,
  `X≥2048`, `alpha≥8`, and `2t alpha≤1`, where
  `alpha = (horizontalSlope X).re`.
- `HeatLocalGrowth.lean`:
  `norm_riemannHeat_near_le_of_nonneg` proves
  `‖H_t(x+iy)‖ ≤ 4 ‖xiLine X 16‖ exp(4096+264 log X)` for
  `X≥4096`, `log X≥20`, `0≤t≤1/8`, `t log X≤1`,
  `|x-X|≤64`, and `|y|≤64`.
- `HeatLocalZeroDensity.lean`:
  `sum_divisor_riemannHeat_local_le` bounds the full divisor mass in
  `closedBall (X-16i) 18` by
  `((log 32+4360)/log 2) * log X` under the explicit range conditions.
- `HeatLocalZeroDensity.lean`:
  `exists_sum_zeroMult_riemannHeat_near_le_log` removes the auxiliary
  height conditions and bounds every finite zero set in the unit window,
  using its full `zeroMult` sum.

One admissible threshold and constant are

\[
X_0=4096+2\pi e^{20},\qquad
C=\frac{\log 32+4360}{\log 2}.
\]

The theorem has no unproved arithmetic input. Its assumptions specify
only the height and heat range and which zeros are being counted.

## Paper proof

Write `f_X(w)=xiLine X w=xi(1/2+w+iX)` and
`alpha=(1/2)log(X/(2pi))`. For `X≥X₀`, we have `X≥4096`,
`log X≥20`, and `alpha≥8`. Since `log(X/(2pi))≤log X`,
`t log X≤1` implies `2t alpha≤1`.

### The fixed Euler anchor

First let `t>0`, set `u=16+2t alpha`, and put
`P=|f_X(u)| exp(-t alpha²)`. Thus `16≤u≤17`.

On `9/2≤w≤32`, the actual Euler-region logarithmic-slope estimate in
`XiLineHalfGaussInstance.lean` compares `f_X(w)` with
`f_X(u) exp((w-u) horizontalSlope X)`, with relative slope error at
most `1/8`. Its Gaussian integral has the following bounds:

1. The full exponential model has modulus at least `23P/25`, by
   `norm_main_eq` and `gaussPhase_ge`.
2. The integrated model error is at most `3P/10`, by `modelError_le`
   and `modelConstant_le`.
3. The lower and upper omitted model tails are each at most `P/32`.
   Completing the square centres the tilted Gaussian at `u`;
   Chernoff with parameter one bounds each tail by `exp(-10)P`.
4. The actual strip contribution `0<w≤9/2` is at most
   `200(6+X) exp(-(23/2)alpha+25/16) P ≤ P/32`.
   The first inequality is the actual strip comparison; the second
   uses `X=2pi exp(2alpha)` and `alpha≥8`.
5. For the actual upper tail `w≥32`, put `v=w-u≥15`.
   After tilting, its integrand is at most
   `P g_t(v) exp(3v+v²/(2X))`. In the stated range,
   `3v+v²/(2X)+20≤v²/(8t)`. Gaussian absorption therefore bounds
   this tail by `2 exp(-20)P≤P/32`.

The positive half-line differs from the full model by at most `17P/40`.
For the reflected half-line, the strip costs at most `P/32` again.
For `w≥9/2`, its Gaussian density satisfies
`g_t(w+16)≤exp(-20)g_t(w-16)`. The whole positive mass is at most
`2P`, so the reflected half-line costs at most `P/16` in total.
The exact half-line reflection identity for `H_t` now gives

\[
|H_t(X-16i)|\ge
\left(\frac{23}{25}-\frac{17}{40}-\frac1{16}\right)P
\ge \frac P4.
\]

The reverse Euler comparison gives
`|f_X(16)|≤P exp(1/8)≤2P`. Consequently

\[
|H_t(X-16i)|\ge |f_X(16)|/8.
\]

At `t=0`, the exact identity `H_0(X-16i)=f_X(16)` gives the same
bound directly. Euler nonvanishing gives `f_X(16)≠0`.

### Uniform local growth

The actual global slice envelope `xiSliceReal_le_global`, its monotonicity,
and `xiSliceGlobalConstant≤16` give

\[
|f_x(w)|\le |f_x(16)|\exp(B_x|w|+w^2/2),
\qquad B_x=(\log x+\texttt{xiSliceGlobalConstant})/2.
\]

Integrate this bound in the whole-line Gaussian formula for `H_t`.
Use `w²/2≤(w-y)²+y²`, Gaussian absorption from time `t` to `2t`,
and `exp(B|v|)≤exp(Bv)+exp(-Bv)`. The two Gaussian exponential
moments yield

\[
|H_t(x+iy)|\le
4|f_x(16)|\exp(B_x|y|+y^2+2tB_x^2).
\]

For `|x-X|≤64`, the actual Euler derivative estimate gives
`|d f_x(16)/dx|≤2 log X |f_x(16)|` along the entire segment from
`X` to `x`. Grönwall therefore yields
`|f_x(16)|≤|f_X(16)| exp(128 log X)`.
In the same window, `B_x≤2 log X`. Hence for `|y|≤64`,
`B_x|y|≤128 log X`, `y²≤4096`, and
`2tB_x²≤8 log X`. Combining the inequalities proves

\[
|H_t(x+iy)|\le4|f_X(16)|\exp(4096+264\log X).
\]

At `t=0`, the slice envelope and the same Euler comparison give this
bound directly.

### Jensen and multiplicities

Normalize by the nonzero value `f_X(16)`, and centre disks at
`c=X-16i`. On the radius-36 circle the normalized function has modulus
at most `M=4 exp(4096+264 log X)`; at the centre it has modulus at
least `1/8`. Jensen between radii 18 and 36 gives

\[
\sum_{|z-c|\le18}\operatorname{mult}_{H_t}(z)
\le\frac{\log32+4096+264\log X}{\log2}
\le C\log X.
\]

The last inequality uses `log X≥1`. Multiplication by the nonzero
normalizing scalar leaves every analytic order, hence the divisor,
unchanged. Entirety and `H_t(0)≠0` ensure finite analytic orders.

Every zero of `H_t` for `t≥0` lies in `|Im z|≤1/2`. Thus a zero with
`|Re z-X|≤1` satisfies
`|z-c|≤|Re z-X|+|Im z+16|≤35/2<18`.
The analytic divisor is nonnegative, so the multiplicity sum over any
finite set of these zeros is bounded by the full divisor mass. This is
the claimed unit-window count, including `t=0` and multiple zeros.

## Verification

All final plain-file checks passed without warnings, from `formal/`:

```text
lake --old env lean GaloisForLFunctions/RHTower/Heat/HeatEulerAnchor.lean
lake --old env lean GaloisForLFunctions/RHTower/Heat/HeatLocalGrowth.lean
lake --old env lean GaloisForLFunctions/RHTower/Heat/HeatLocalZeroDensity.lean
```

All three modules are imported by `GaloisForLFunctions/RHTower.lean`.
The lower-anchor and growth oleans were built for the local-count module's
imports. The umbrella was not compiled.

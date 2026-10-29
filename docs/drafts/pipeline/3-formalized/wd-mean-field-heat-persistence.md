# Mean-field heat persistence by a translated reverse Gaussian

- **ID:** wd-mean-field-heat-persistence
- **Stage:** 3-formalized
- **Type:** THEOREM; unconditional persistence and multiplicity counting
- **Source:** [WD investigation](../1-in-progress/wd-directed-source-extinction.md); [heat-count programme, N₁](../1-in-progress/heat-count-small-time-growth.md)
- **Statement:** For every `0<delta≤1/2`, there are `c_delta>0` and `X_delta≥4096` such that an unheated zero with real part `X≥X_delta` and `delta≤|Im z|≤1/2` forces a nonreal `H_t` zero in `|Re z-X|≤1` whenever `0<t` and `t log X≤c_delta`. At this scale, deep dyadic Xi zero copies satisfy `#F≤C_delta log X·N(t)`.
- **Main declarations:** `RHTower.DeBruijn.exists_nonreal_riemannHeat_zero_at_inverse_log_scale`; `RHTower.DeBruijn.exists_card_deep_le_heat_count_at_inverse_log_scale`.

## Goal and status

The fixed-depth mean-field persistence scale `(N₁)` is formalized for
the actual Riemann heat flow. It strengthens the earlier `(N₂)` scale
`log(X)^(-4)` to `log(X)^(-1)`. All analytic source inputs are discharged;
neither main declaration assumes an arithmetic estimate or a property
of the unknown off-line zeros.

The persistence theorem and its exact multiplicity counting theorem,
together with the four supporting modules below, passed final plain
Lean checks without warnings. This proves no upper bound for the total
nonreal heat count `N(t)` and does not close WD. The constants in this
card depend on each fixed positive depth. The
[shrinking-window theorem](wd-shrinking-window-heat-persistence.md)
now proves uniform `c delta²` dependence by retaining the centered
polynomial factors; its persistence and counting statements passed Lean.

## Verified inputs

All listed new modules passed plain `lake --old env lean` checks and are
wired into their owning umbrellas, `RHTower.lean` or `HTGeometry.lean`.

- `HeatEulerAnchor.lean`: `|xiLine X 16|≤8|H_t(X-16i)|`.
- `HeatLocalGrowth.lean`: the actual rectangle upper bound, and the
  whole-line Gaussian upper envelope relative to `xiLine x 16`.
- `HeatLocalZeroDensity.lean`: multiplicity-exact `O(log X)` local
  counts uniform for `0≤t≤1/8`, `t log X≤1`.
- `HeatLocalCofactor.lean`:
  `exists_uniform_riemannHeat_local_cofactor`, including the degree,
  both logarithmic-derivative bounds, cofactor minimum modulus, and
  actual heat-value lower bound away from positive-multiplicity factors.
- `HeatReverseGaussian.lean`:
  `riemannHeat_zero_eq_reverse_saddle`, arbitrary complex contour
  translation, and absolute integrability of the translated integral.
- `HeatRelativeGlobalBounds.lean`:
  `exists_riemannHeat_global_relative_bound`, a uniform envelope for
  every real height in the unit horizontal strip. Plain Lean check passed.
- `HTGeometry/LogDerivativeBound.lean`: `norm_logDeriv_le`.
- `HTGeometry/BallLogarithm.lean`: `norm_lower_bound_of_ball`.
- `HTGeometry/LogLinearGronwallModel.lean`: `norm_sub_mul_exp_le`.
- `HTGeometry/LogDerivativeSaddle.lean`: `exists_logDeriv_saddle` and
  `norm_exp_logDeriv_normalized_sub_one_le`, both checked without warnings.
- `HeatZeroFreeWindow.lean`: `exists_riemannHeat_window_bounds`, an
  unconditional alternative between a nearby nonreal heat zero and
  minimum-modulus and logarithmic-derivative bounds on a fixed-depth disk.
- `HeatGaussianQuadraticError.lean`:
  `integral_gaussDensity_quadratic_error_le`, including the full tail and
  integrability.
- `HeatMeanFieldPersistence.lean`:
  `exists_nonreal_riemannHeat_zero_at_inverse_log_scale`.
- `HeatMeanFieldZeroDensity.lean`:
  `exists_card_deep_le_heat_count_at_inverse_log_scale`.

## 1. Global relative growth: formalized

Target, with absolute constants `C₀,X₀`:

\[
|H_t(x+iy)|\le |\xiLine_X(16)|
 \exp\!\big(C_0\log X(1+|x-X|)\big)
\]

for `X≥X₀`, `0≤t≤1/8`, `t log X≤1`, every real `x`, and `|y|≤1`.
This is `exists_riemannHeat_global_relative_bound` in
`HeatRelativeGlobalBounds.lean`; its plain `lake --old env lean` check passed.

Write `L=log X` and `N_X=|xiLine X 16|`. The actual slope theorem
`norm_xiLineDeriv_le` bounds the derivative in height by `2L` times the
norm throughout `2048≤s≤X²`, provided `X≥4096` and `L≥20`:
`log(s/(2pi))/2≤L`, and the remaining coefficient is at most 3.
Grönwall therefore gives

\[
N_x\le N_Xe^{2L|x-X|}\quad(2048\le x\le X^2).
\]

In particular, with the fixed positive Euler value `N_*=N_2048`,
`N_*≤N_X exp(2XL)`.

Split according to `Delta=|x-X|`.

- If `Delta≤X/2`, then `x∈[X/2,3X/2]`. The existing Gaussian envelope
  has slope `B_x=(log x+xiSliceGlobalConstant)/2≤2L`, so for `|y|≤1`
  it gives `|H_t(x+iy)|≤4N_x exp(1+10L)`. Combine with the height
  comparison above.
- If `Delta≥X/2`, use the actual strip bound from
  `norm_riemannHeat_le_strip_integral`. For `t≤1/8` and `|y|≤1`, it is
  bounded by the fixed positive constant
  `M=1+integral Phi(u) exp(u²/8) exp(|u|) du`.
  Since `N_*≤N_X exp(2XL)`,
  `M≤(M/N_*)N_X exp(2XL)`.
  Here `2XL≤4L Delta`; also `L≥1`, so the fixed factor `M/N_*` can be
  absorbed into `exp(C₀L)`. This proves the same relative envelope.

The far-height argument thus costs only a linear exponential in
`|x-X| log X`; no separate far-tail Gaussian analysis is necessary.

## 2. A heat window containing only real zeros

Suppose every heat zero in `|Re z-X|≤1` is real. Let `z₀.re=X` and
`delta≤|z₀.im|≤1/2`. Put `c=X-16i`, `w₀=z₀-c`, so `|w₀|≤33/2<17`.

Use the formalized factorization `H_t(c+w)=P(w)g(w)`, with degree
`n≤C L`. Every extracted factor with positive multiplicity is an actual
heat zero. Its distance from `z₀` is at least `delta`: real zeros are
separated vertically; nonreal zeros outside the unit window are
separated horizontally. Consequently

\[
|H_t(z_0)|\ge \frac{N_X}{8}
 (\delta/18)^n e^{-CL}
\ge \frac{N_X}{8}e^{-A_\delta L},
\qquad A_\delta=C(1+\log(18/\delta)).
\]

The closed disk of radius `delta/2` about `z₀` is zero-free. Its real
parts stay in the unit window, and its imaginary parts stay separated
from zero. The already proved rectangle upper bound and the centre
lower bound have logarithmic ratio `O_delta(L)`.

Apply `norm_logDeriv_le` with radii `delta/2`, `3delta/8`, and
`delta/4`. Its coefficient is `48/delta`. Cauchy's derivative estimate
on radius `delta/8` then gives a derivative coefficient
`384/delta²`. Thus, for a constant `B_delta>0`,

\[
|H_t'/H_t|\le B_\delta L\quad(|z-z_0|\le\delta/4),
\qquad
|(H_t'/H_t)'|\le B_\delta L\quad(|z-z_0|\le\delta/8).
\]

The same cofactor estimate gives the disk lower bound directly. Every
extracted root has distance at least `delta` from `z₀`, hence distance
at least `delta/2` from every point in the closed disk of radius
`delta/2`. This disk stays within the cofactor's radius-17 disk. Taking
`A_delta=C(1+log(36/delta))` therefore gives

\[
|H_t(s)|\ge (N_X/8)e^{-A_\delta L}
\quad(|s-z_0|\le\delta/2).
\]

These window estimates are proved in `HeatZeroFreeWindow.lean`, whose
final plain check passed without warnings. They use no
assumption about the heat zeros outside the window, nor a partial-fraction
formula for the heat flow. The exported theorem gives an unconditional
alternative: a nearby nonreal heat zero, or all the displayed bounds.

## 3. The saddle and its local error

Let `q=H_t'/H_t` and `r=delta/32`. If `2tB_delta L≤r`, the holomorphic
map `s↦z₀+2t q(s)` maps the open radius-`2r` disk about `z₀` into
the closed radius-`r` disk. The existing corpus theorem
`DiscFixedPoint.exists_unique_fixedPoint`, with contraction ratio
`theta=1/2`, supplies a fixed point `s` with `|s-z₀|≤r`. Thus the
saddle needs no new Banach-space construction. Put `a=q(s)`.

For real `|u|≤r`, the segment from `s` to `s+u` stays in the disk
where `|q'|≤B_delta L`. Hence `|q(s+v)-a|≤B_delta L |u|` on that
segment. Apply `norm_sub_mul_exp_le` and divide by the nonzero
`H_t(s)exp(au)` to obtain

\[
\left|e^{-au}\frac{H_t(s+u)}{H_t(s)}-1\right|
\le e^{B_\delta L u^2}-1.
\]

The case `u=0` is exact. If `tB_delta L≤1/8`, Gaussian absorption
`g_t(u) exp(u²/(8t))≤2g_(2t)(u)`, together with
`exp(v)-1≤v exp(v)` for `v≥0`, bounds the integrated local error by

\[
2B_\delta L\int_{\mathbb R}u^2g_{2t}(u)\,du
=8tB_\delta L.
\]

The fixed point and normalized pointwise error are formalized in
`HTGeometry/LogDerivativeSaddle.lean`. Its plain Lean check passed.
Their application to the actual heat flow is proved in
`HeatMeanFieldPersistence.lean`.

## 4. The complete tail estimate

Combine the global relative envelope from step 1 with the lower bound
for `H_t(s)` from step 2. Since `|s-z₀|≤r<1`, `|Im s|≤1`, and
`|a|≤B_delta L`, there are constants `E_delta,D_delta>0` such that
for every real `u`,

\[
\left|e^{-au}\frac{H_t(s+u)}{H_t(s)}\right|
\le e^{E_\delta L+D_\delta L|u|}.
\]

Choose the constants nonnegative, so this envelope also dominates 1.
If `tD_delta L≤r/8`, then on `|u|≥r`,
`D_delta L|u|≤u²/(8t)`. Gaussian absorption and the two-sided
Chernoff bound give the full tail error

\[
\int_{|u|\ge r}g_t(u)
 \left|e^{-au}\frac{H_t(s+u)}{H_t(s)}-1\right|du
\le8\exp\!\left(E_\delta L-\frac{r^2}{8t}\right).
\]

Here `integral_(|u|≥r) g_(2t)(u)≤2 exp(-r²/(8t))` follows from
the Gaussian moment generating function with parameters
`±r/(4t)`. No numerical estimate is used.

`HeatGaussianQuadraticError.lean` proves the complete estimate
`8tK+8 exp(E-r²/(8t))` from local error `exp(Ku²)-1` and global
envelope `exp(E+D|u|)`. It also proves integrability. Its final plain
Lean check passed without warnings.

Take `c_delta>0` no larger than each of

\[
1,\quad \frac{\delta}{64B_\delta},\quad
\frac1{32B_\delta},\quad \frac r{8D_\delta},\quad
\frac{r^2}{8(E_\delta+\log32)}.
\]

If `tL≤c_delta`, the local error is at most `1/4`, and the full tail
error is at most `1/4`, using `L≥1`. The same choice guarantees the
saddle disk-map bound and `t≤1/8` once `L≥20`.

## 5. Persistence and counting

The proved reverse formula and the saddle equation give

\[
H_0(z_0)=e^{-ta^2}H_t(s)
 \int_{\mathbb R}g_t(u)e^{-au}\frac{H_t(s+u)}{H_t(s)}\,du.
\]

The integral differs from 1 by at most `1/2`. Both outside factors are
nonzero. This contradicts `H_0(z₀)=0`; thus the heat window contains
a nonreal zero. The full contradiction in `HeatMeanFieldPersistence.lean`
passed its final plain Lean check without warnings.

For the counting statement, let `F` be a finite set of `XiZeroCopy` with
ordinates `T` in `[X,2X]` and depth at least `delta`. Its spectral point
`z=(rho-1/2)(-i)` satisfies `H_0(z)=0`, `Re z=T`, and
`delta≤|Im z|≤1/2`, using the unconditional zero-free regions outside
the critical strip. Since `log T≤2 log X`, the persistence theorem
applies to every copy when `t log X≤c_delta/2`.

Choose a resulting nonreal heat zero `W(q)` for each copy `q`. Its real
part differs from the copy's ordinate by at most 1. For each image point
`w`, all copies in its fibre lie in `|Im rho-Re w|≤1`; hence the actual
local multiplicity theorem bounds that fibre by `C_xi log(Re w)`.
Also `Re w∈[X-1,2X+1]`, so this is at most `2C_xi log X` for large `X`.
The finite image has at most `N(t)` members because each distinct
nonreal heat zero contributes positive multiplicity to `N(t)`.
Summing the fibres proves

\[
\#F\le 2C_{\xi}\log X\,N(t)
\qquad(0<t,\ t\log X\le c_\delta/2).
\]

`HeatMeanFieldZeroDensity.lean` contains this unconditional counting
proof; its plain check passed without warnings. No upper bound on `N(t)` is assumed.

## Validation and remaining WD gap

Each command passed without warnings, run individually from `formal/`:

```sh
lake --old env lean GaloisForLFunctions/RHTower/HeatRelativeGlobalBounds.lean
lake --old env lean GaloisForLFunctions/RHTower/HeatZeroFreeWindow.lean
lake --old env lean GaloisForLFunctions/RHTower/HeatGaussianQuadraticError.lean
lake --old env lean GaloisForLFunctions/HTGeometry/LogDerivativeSaddle.lean
lake --old env lean GaloisForLFunctions/RHTower/HeatMeanFieldPersistence.lean
lake --old env lean GaloisForLFunctions/RHTower/HeatMeanFieldZeroDensity.lean
```

Imports are wired; umbrellas were not compiled. Scratch files were
removed. No web search, novelty checks, numerical experiments, or axiom
checks were performed, as instructed.

The actual source-cap upper sign, near-axis extinction, and total
nonreal-count upper bounds remain open. Uniform depth dependence is
provided by the linked shrinking-window theorem, rather than inferred
from the fixed-depth quantifiers of this card.
WD and the overarching goal remain open.

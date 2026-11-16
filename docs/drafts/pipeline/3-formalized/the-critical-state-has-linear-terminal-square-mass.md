# The critical state has linear terminal square mass

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** ECS Q9; actual-state boundary regularity and large-probe decay.

For the unit critical state `F`, a constant `C` bounds
`∫(-h,0) F² ≤ C h` for every `h>0`. The stronger intermediate estimate is

`δ ∫(-h,0) F² ≤ a W₈(F) (exp(8h)-1)`,

where `δ>0` is the proved transverse spectral gap. This improves the
domain-wide logarithmic boundary estimate without postulating a pointwise trace.

## Projection argument

Put `T_h F(u)=F(u+h)` and `c=∫F T_h F`. Both profiles have square norm one.
The profile `G=T_h F-cF` is orthogonal to `F`, so the spectral gap and exact
causal translation identity give `δ‖G‖²≤a W₈(F)(exp(8h)-1)`.
The reversed residual `J=F-c T_h F` has the same square norm as `G`.
On `(-h,0)`, the translated profile vanishes and `J=F`; hence
`∫(-h,0)F²≤‖J‖²=‖G‖²`. The exponential bound gives the linear estimate
for small `h`; normalization handles larger `h`.

## Laplace consequence

For a nonnegative integrable density `g` on `u<0`, Fubini gives

`(1/t) ∫g(u) exp(tu) du = ∫₀∞ exp(-th) (∫(-h,0) g) dh`.

With `g=F²` and terminal mass at most `Ch`, the right side is at most
`C/t²`. Weighted Cauchy–Schwarz gives `|LF(t)|≤√C/t` for every `t>0`.
Both modules passed final plain Lean checks and are umbrella-wired:

- `HTGeometry/Analysis/LinearCumulativeLaplaceBound.lean`:
  `integral_exp_mul_Iio_le_of_terminal_mass`,
  `abs_integral_exp_mul_Iio_le_of_terminal_square_mass`.
- `ExclusionOfTheCriticalState/TheCriticalStateHasLinearTerminalSquareMass.lean`:
  `criticalState_terminal_mass_exponential_bound`,
  `criticalState_wall_and_laplace_bounds`,
  `riemannHypothesis_or_criticalState_wall_and_laplace_bounds`.

## Remaining consequence

Inserting the inverse-linear sample bound into the archimedean resolvent
expansion should give `JF(-t)=O(log(t)/t)`. That estimate and leading
asymptotics remain unformalized. No contribution counted.

## Verified inputs

- `criticalHalfLineFullEnergy_transverse_L2_gap`
- `criticalHalfLineFullEnergy_causal_ground_shear`
- `hasSum_levyHead_resolvents`

This is boundary regularity for Q9. It supplies no Q8 arithmetic exclusion.

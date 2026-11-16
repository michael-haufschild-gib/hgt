# The critical state has linear terminal square mass

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** ECS Q9; actual-state boundary regularity and large-probe decay.

For the unit critical state `F`, conjecture that a constant `C` bounds
`∫(-h,0) F² ≤ C h` for every `h>0`. The stronger intermediate estimate is

`δ ∫(-h,0) F² ≤ a W₈(F) (exp(8h)-1)`,

where `δ>0` is the proved transverse spectral gap. This would improve the
domain-wide logarithmic boundary estimate without postulating a pointwise trace.

## Projection argument

Put `T_h F(u)=F(u+h)` and `c=∫F T_h F`. Both profiles have square norm one.
The profile `G=T_h F-cF` is orthogonal to `F`, so the spectral gap and exact
causal translation identity give `δ‖G‖²≤a W₈(F)(exp(8h)-1)`.
The reversed residual `J=F-c T_h F` has the same square norm as `G`.
On `(-h,0)`, the translated profile vanishes and `J=F`; hence
`∫(-h,0)F²≤‖J‖²=‖G‖²`. The exponential bound gives the linear estimate
for small `h`; normalization handles larger `h`.

## Analytic consequence to prove

Writing `f(t)=F(-t)`, the cumulative bound `∫₀ʰf²≤Ch` should give
`∫₀∞f² exp(-t·)≤C/t`. Cauchy–Schwarz then yields `|LF(t)|≤√C/t`.
Inserted into the archimedean resolvent expansion, this should sharpen the
head bound to `O(log(t)/t)` as the probe tends left. These consequences and
the projection argument require Lean verification. No contribution counted.

## Verified inputs

- `criticalHalfLineFullEnergy_transverse_L2_gap`
- `criticalHalfLineFullEnergy_causal_ground_shear`
- `hasSum_levyHead_resolvents`

This is boundary regularity for Q9. It supplies no Q8 arithmetic exclusion.

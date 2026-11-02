# Sharp norm and actual amplification of Mayer Cauchy averaging

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** PM

Let `T_w` be the actual Cauchy averaging operator on logarithmic `L²`,
with `Re w>0`, and let `m(w,u)` be its certified Gamma multiplier.

## Claims

1. `‖T_w‖ = |m(w,w/2)|`.
2. For fixed `σ>0`, `‖T_(σ+iτ)‖ → 2^((1−σ)/2)` as `τ→+∞`.
3. If `0<σ<1`, every sufficiently large `τ` admits an actual `L²` field
   `f` with `‖T_(σ+iτ) f‖ > ‖f‖`.
4. For fixed `σ>0`, strict contraction at every spectral height holds
   exactly when `σ≥1`.
5. A single bound `‖T_(σ+iτ)‖≤c<1` valid for all `τ` exists exactly when `σ>1`.

## Paper proof

Plancherel identifies `T_w` with multiplication by the continuous Fourier
symbol `φ_w(ξ)=m(w,w/2+2πiξ)`. The certified frequency maximum is at zero,
so the existing operator bound is `‖T_w‖≤|φ_w(0)|`. The corpus theorem
`HTGeometry.le_norm_fourierMulCLM`, proved using Fourier packets supported
in arbitrarily small intervals around a continuity point, gives the reverse
inequality. This proves claim 1 for the actual integral operator.

The certified high-height Gamma asymptotic at Mellin weight `σ/2` proves
claim 2. Its limit exceeds one when `σ<1`, hence the actual operator norm
eventually exceeds one. If every field satisfied `‖T_w f‖≤‖f‖`, the defining
operator-norm bound would imply `‖T_w‖≤1`; contradiction proves claim 3.
For `σ≥1`, the already certified strict central-multiplier bound gives
strict contraction at every height. Claim 3 excludes this when `σ<1`,
proving claim 4. For claim 5, the limit of any bound `c<1` must satisfy
`2^((1−σ)/2)≤c<1`, forcing `σ>1`. Conversely, the certified strict
Gamma envelope supplies the bound `c=2^((1−σ)/2)<1` when `σ>1`.
Thus `σ=1` has strict contraction at each finite height, but no common gap.

## Audit and scope

The corpus contains the actual operator, its multiplier identity, the upper
norm bound, scalar high-height amplification, and the generic continuous-symbol
lower bound. The missing statement is their exact operator-level combination.
No new analytic premise is introduced. This strengthens the positive result
from failed uniform complex contraction by producing amplified actual fields.
It does not identify Cauchy fixed vectors with Mayer transfer eigenfunctions.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerCauchySharpOperator.lean` proves
`operator_norm_eq`, `tendsto_operator_norm`, `exists_amplified_field`,
`eventually_operator_norm_gt_one`, `eventually_amplified_field`,
`all_heights_contraction_iff`, and `uniform_gap_iff`. The final direct production
audit passed without warnings; all seven declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

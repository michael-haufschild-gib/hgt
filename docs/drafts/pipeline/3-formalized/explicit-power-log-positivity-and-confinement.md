# Explicit power-log positivity and conductor confinement

- **ID:** explicit-power-log-positivity-and-confinement
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../../reports/review-3110/obstacles-summary.md, original A1 at `dbc7d26186`
- **Statement:** Explicit quadratic-accuracy conductor confinement; all-vector complete Weil positivity for every `0<α<1/19`; polynomial-conductor complement coercivity for `0<α<1/16`.

## Results

Write `L=log N`, `W=W_N,c` for the tilted-spline complete Weil form, and
`V_R` for the conductor subspace. Uniformly for `1≤c≤L^α`, eventually in `N`,

`W(x) ≥ κ/(2c⁷) ‖x‖²`, with `κ>0`, for every `0<α<1/19`.

Consequently the complete matrix is positive definite, the literal atomic Weil
quadratic form is nonnegative, and `W(x)≥b₁c⁻²³D_N(x)` for some fixed `b₁>0`.
In particular `α=1/20` is an explicit admissible exponent.
The endpoint `α=1/19` is not asserted.

For every `θ>0` and `0<α<1/16`, the companion theorem gives
`W(z)≥c_orth Lc⁻⁷‖z‖²` on `V_floor(N^θ)^⊥`, with `c_orth>0`.
This is the confinement ceiling; all-vector positivity also pays the stricter
relative residual budget.

## Explicit confinement

Set

`S=24/log 2+1715/(1−2^(−1/4))`, `T=max(1,512S)`,

`C₀=(1+4T) exp(3(1+1/(4T))T(4T+2))`,

`C₂=64[54(2(C₀+3)+2(log 4+4))+49]`, `D=256C₂`.

Finite-sieve comparison gives `P(n)log n≥1/128`. Dyadic shells and prime
peeling then bound smooth–rough conditioning error by `C₀D_N/log P`.
Weighted Jensen bounds the conditioned logarithmic moment by
`2D_N+3L(P)‖x‖²`. Spectral truncation therefore costs
`16(2K+3L(P))/log R`, without the former support logarithm.
Choosing each intermediate error at most `η/8` yields, for `0<η≤1`,

`log R≤C₂(K+1)/η²`, `dist(x,V_R)²≤η`

for all unit vectors with defect at most `K`, uniformly in the horizon.
The reverse defect gap is `(log Q/D−1)‖x‖²` outside the squared `1/16` tube.
Thus the former cubic accuracy loss becomes quadratic.

## Proof of the exponent range

Put `H=1+log R`, `E(a)=Σ(log m+tameDifferent(m))a_m²`,
`A=Σa_m²`, `G=Σ(1+log m)a_m²≤A+E`.

1. Exact prime dilation gives `Σ_k Λ(k)/k ‖Δ_k a‖²=E`; its logarithmic
   moment is at most `(1+log R)E`. Harmonic lower frames give
   `D_N≥(1−(3log R+1)/L)E` for normalized packets.
2. Take `T=growingDefectCutoff(c)=O(c⁸)` and `M=floor(N/T)`.
   Localization retains `W≥½D_M+bc⁻⁷D_N−Cc⁹‖x‖²`.
   Subtracting endpoint Gram formulas bounds terminal packet mass by
   `B A`, where `B=H_N−H_M+2R²/(M+1)≤4+log(2T)` when `R²≤M`.
   For `w⊥V_R`, prefix projection mass is at most `2B S_tail/log M`.
   Hence, for `k=log R/D−1≥Kc¹⁶` and `B/log M≤b/(4c⁷)`,
   `W(w)≥(k/4)S_prefix+(bk/(2c⁷))S_tail`.
3. Prime cross residuals squared are bounded by
   `(CH A+532H²E)/L` globally and `(CH A+28HBE)/L` terminally.
   Dyadic coefficient interpolation replaces squared logarithmic losses in
   the center and near kernels by `HG`. Paying the cross terms from the two
   reserves gives `2|cross|−W(w)≤E/8+‖u‖²/4` once a constant times
   `H/L+c⁷(1+B)/L+c¹¹(1+log c)/L+c¹¹R²L/N` is small.
4. Fixed squared projection tolerance `1/4` now suffices. Enlarging the cutoff
   gives `log R≤C_Rc¹⁶+log Q`, while retaining `‖u‖²≥3/4`, `‖u‖≤1`,
   `u⊥V_Q`, and `W(u)−E/8≤E₀+1`. This replaces the former `c⁴⁶` cutoff.
5. Orthogonality and Gram control give `A≥1/2`, low coefficient mass
   `≤1/200`, and `E≥(2/5)log Q`. The prime term retains
   `E/8+¼log Q−log 4−4`. Integer separation bounds the quadratic near term
   by `O(c²H(1+log c)/L+c²R√(L/N))‖u‖²`; Hilbert and mean-zero row
   bounds give center cost `600cH/L`. The middle overlap costs `O(c³/√Q)`.
   Together, `W(u)≥E/8+¼log Q−log c−C`.
6. With quotient cutoff `exp(L^(1/k))`, the linear conductor residual is
   `O(m(1+log m)²·rate)`, where
   `rate=c⁵/L+c¹⁰(L/N)²+c³L^(1/k)/L`.
   The conductor-dependent floor gives relative squared-residual sum
   `≤K(c¹⁴+Q²)(1+log Q)²·rate`.
7. For `0<α<1/19`, take `τ=(1−19α)/100`, `q=6α+τ`, `ν=τ/10`,
   `k=ceil(1/τ)+1`, and `Q=floor(L^q)`. Then `1/k≤τ`, `q≤1/3`,
   `18α+3ν≤1`, `3α−q/2≤−ν`,
   `19α+1/k+2ν−1≤−ν`, and `2q+5α+1/k+2ν−1≤−ν`.
   All error budgets decay as `O(L^−ν)`, while `q/4−α>0` makes the high
   packet lower bound contradict step 4. The relative residual criterion
   applies to the matrix shifted by `κ/(2c⁷)`, proving the spectral floor.
   Combining this floor with the polynomial defect reserve cancels its mass
   debit and yields the `c⁻²³` reserve.

## Lean declarations and audit

- `RenormalizedArithmeticPotentialTheory.Conductor.QuadraticConductorConfinement`:
  `exists_explicit_quadratic_conductor_cutoff`,
  `poleDefect_ge_explicit_of_norm_sub_starProjection_gt`.
  Final direct audit passed, including explicit conditioning and weighted approximation dependencies.
- `CriticalArithmeticCorrelationTheory.TheCompleteWeilMatrixIsPositiveBelowTheResidualCeiling`:
  `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_residual_ceiling`,
  `eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_residual_ceiling`,
  `eventually_tiltedUnitSpline_weilQuad_nonneg_below_residual_ceiling`,
  `exists_tiltedUnitSpline_completeWeilEnergy_ge_poleDefect_reserve_below_residual_ceiling`,
  `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_log_one_twentieth`.
  All six public axiom audits passed with only `propext`, `Classical.choice`, and `Quot.sound`.
  Final direct audit and all 21 support-file audits passed without warnings.
- Companion `PolynomialConductorComplementCoercivityAndSharpenedOverlap`:
  `eventually_completeWeilEnergy_ge_on_polynomialConductorOrthogonal`.
  Direct audit recorded on its [formalized card](../3-formalized/exceptional-conductor-emptiness-and-sharpened-power-log-positivity.md);
  dependency build and transitive axiom audit passed.

All 26 new or modified modules passed direct Lean checks and are imported by
their programme umbrellas. Transitive axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`; no proof holes or resource-limit overrides.

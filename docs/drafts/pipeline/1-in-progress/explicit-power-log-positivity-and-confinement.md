# Explicit power-log positivity and conductor confinement

- **ID:** explicit-power-log-positivity-and-confinement
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ../../../reports/review-3110/obstacles-summary.md, A1 at `dbc7d26186`
- **Statement:** Replace the unspecified conductor-confinement constant by a proved explicit constant and sharpen the accuracy and overlap exponents in complete Weil positivity.

## Mathematical targets

1. Explicit conductor confinement, uniformly in the horizon: squared projection error at most `η` for `log R ≤ C (K + 1) / η^p`, with numerical `C` and improved `p`.
2. An explicit reverse defect gap and numerical positive overlap exponent.
3. Optimize all-vector positivity toward the stated `1/19` residual and `1/16` confinement ceilings.

## Existing bounds

`ConductorBandTopTailBounds` proves `p = 3` with an unspecified constant. `TheCompleteWeilMatrixIsPositiveAtPowerOfLogOverlap` uses `Q₁ = floor((log N)^(1/12))`, squared error `η ≍ c⁻¹⁰`, cutoff `log R ≪ c⁴⁶`, and `α < min(1/500, 1/(60 C_cut))`. The constant originates in smooth–rough conditioning.

## Strengthened confinement proof

The finite-sieve harmonic comparison at horizon one, together with `L(P) ≤ 2(log P + log 4 + 4)`, gives `P(n) log n ≥ 1/128` for the Mertens product. Put

`S = 24/log 2 + 1715/(1 − 2^(−1/4))`, `T = max(1, 512S)`,
`C₀ = (1+4T) exp(3(1+1/(4T)) T(4T+2))`.

Dyadic shell summation and prime peeling give conditioning error `≤ C₀ D/log P` uniformly in the horizon.

For the conditioned profile `f`, weighted Jensen and the smooth-part moment give
`Σ_(a≤A) (log a+L(P)) w_N(a) f(a)² ≤ 2D+3L(P)‖x‖²`.
Spectral truncation, retaining this moment, gives error at most `16(2K+3L(P))/log R`. The former support bound `16(log A+L(P))/log R` is unnecessary.

Set `δ=η/8`. Choose `log P ≥ C₀(K+1)/δ`, `log A ≥ 2(K+L(P))/δ`, and
`log R ≥ 2log A+2L(P)+4+16(2K+3L(P))/δ`, with logarithmic rounding error at most three. These choices give squared approximation error at most `6δ≤η` and

`log R ≤ C₂(K+1)/η²`,
`C₂ = 64[54(2(C₀+3)+2(log 4+4))+49]`.

The reverse gap constant is consequently `256C₂`. Explicit conditioning, weighted approximation, and quadratic confinement compile with only `propext`, `Classical.choice`, and `Quot.sound`. Conditioning passed its final direct audit; the other two direct audits remain pending.

## Numerical prime coercivity

For a packet supported on `Q<m≤R`, assume `R²≤N` and `18(1+log R)≤log N`.
The direct defect bound below gives `D_N(y)≥¾E`, where
`E=Σ(log m+tameDifferent(m))a_m²`. Since `log Q·Σa_m²≤E` and
`‖y‖²≤3/2·Σa_m²`, the bounded row counterterm gives

`primeEnergy(y) ≥ (½ log Q − log 4 − 4) ‖y‖²`.

The logarithmic coefficient and additive loss are numerical; no prime residual
smallness is required. Direct defect transfer and prime coercivity passed Lean
with standard axioms. Final direct audits remain pending.

## All-vector exponent

Fixed squared projection tolerance `1/4` suffices. Enlarge `R` so
`log R ≥ D[1+(B+4C_cross²)/b]c¹⁶`, where `D` is the explicit reverse-gap constant.
Orthogonality gives `D_N(w)≥(log R/D−1)‖w‖²`; the polynomial reserve gives
`W(w)≥4C_cross²c⁶‖w‖²`. Completing a square pays the cross term by `1/4`.
Thus `log R≪c¹⁶`, without a shrinking projection tolerance.

Put `L=log N`. For `α<1/59`, choose
`τ=(1−59α)/40`, `q=8α+τ`, `ν=min(τ/4,1/1000)`, and `k=ceil(1/τ)+1`.
Use `Q=floor(L^q)` and the variable quotient cutoff below. The binding exponents are

`4α−q/2=−τ/2≤−ν`,
`5q+19α+1/k−1≤−35τ+1/k≤−34τ≤−ν`.

The prime cross residual at the confinement cutoff need only satisfy
`(1+log R)²/√L≤c³`, since the cross-bound already has this factor.
Its growing term is `O(c²⁹/√L)`, which decays uniformly for `α≤1/59`.
The low-band prime residual uses `log Q`, while its adjunction contribution
costs `(1+log R)²/L`. Remaining errors decay with fixed positive margins.
High-packet coercivity contributes `¼log Q−log c−O(1)`;
`q/4−α=α+τ/4>0`.

All-vector positivity with the uniform `c⁻⁷` spectral floor is proved in Lean
for every `0<α<1/59`. The main module passed its direct audit; all six public
axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`.
The literal Weil nonnegativity and `c⁻²³` prime-defect reserve follow with the
same exponent. The stronger structural ceilings `1/19` and `1/16` require
improvements beyond these residual and overlap budgets.

## Direct prime-defect transfer

For `F(n)=Σ_(m≤Q) a_m r_m(n)`, put `E=Σ_(m≤Q)(log m+tameDifferent(m))a_m²`. The exact prime-dilation identity gives `Σ_k Λ(k)/k ‖Δ_k a‖²=E`; its logarithmic moment is at most `(1+log Q)E`. Harmonic lower frames give

`Σ_(n≤N/k) (F(kn)−F(n))²/n ≥ (log N−log k−2log Q)‖Δ_k a‖²`.

The same lower bound holds when `k>N`, since its right side is nonpositive. Sum over all prime powers and use the exact defect edge identity. This proves

`D_N(F/√n) ≥ (log N−3log Q−1)E`.

Thus relative defect coercivity loses only `O(log Q/log N)`. This bypasses the squared logarithmic loss from prime residual norms. Both the raw and normalized Lean statements compile with standard axioms.

## Variable quotient cutoff

For every fixed integer `k≥1`, use `Y=exp((log N)^(1/k))` in the affine-shell
source bound, with conductor exponent `Ak` and source decay power `k`.
For `m≤(log N)^A`, the large-quotient error is `≤Cc/log N`; the complementary
harmonic mass is at most `4c+(log N)^(1/k)`. Thus one constant, independent of
`A,k`, gives normalized squared source error

`≤K φ(m)² c³ (log N)^(1/k−1)`.

This removes the forced square-root logarithmic rate. The reciprocal row,
actual upward row, and complete residual are formalized in
`VariableCutoffConductorResiduals`; all axiom audits report standard axioms.

## Remaining work

Finish direct support-module audits. The ceiling exponents remain unattained.
`ConductorScaleControlsTheCompletedEnergy` already proves the stronger floor
`κ(m/φ(m)) min(1,(m/c)⁷)`. Using it can remove the uniform `c¹⁴` loss from
conductors above `c`; the remaining high-packet residual then costs `Q⁵c⁵/L`.
Current high-band overlap still costs `c⁴/√Q`, and the prime cross bound costs
`(1+log R)²/√L`. These estimates need sharper treatment to reach `1/19`.

The proposed weighted residual bound is
`Σ_(m≤Q) ‖r_m‖²/E_m(c)² ≤ K(c¹⁴+Q⁵)·rate`.
Indeed `m⁴/E_m(c)² ≤ κ⁻²(c¹⁴/m¹⁰+m⁴)`, and `Σ_(m≥1)m⁻¹⁰≤2`.
The Lean proof is drafted but unverified. This separates the low-conductor
condition `19α<1` from the high-conductor condition `5q+5α<1`.

## Gates

- [x] Precise target and source dependencies identified.
- [x] Dependency-closed proof of the strengthened bounds.
- [ ] Lean formalization, direct file audit, and transitive axiom audit.

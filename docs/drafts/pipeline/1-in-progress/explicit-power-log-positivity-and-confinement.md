# Explicit power-log positivity and conductor confinement

- **ID:** explicit-power-log-positivity-and-confinement
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ../../../reports/review-3110/obstacles-summary.md, A1
- **Statement:** Replace the unspecified conductor-confinement constant by a proved explicit constant and sharpen the accuracy and overlap exponents in complete Weil positivity.

## Mathematical targets

1. Explicit conductor confinement, uniformly in the horizon: squared projection error at most `η` for `log R ≤ C (K + 1) / η^p`, with numerical `C` and improved `p`.
2. An explicit reverse defect gap and numerical positive overlap exponent.
3. Optimized low-band, projection-accuracy, and high-cutoff exponents in all-vector positivity, with the residual and confinement ceilings accounted for.

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

The reverse gap constant is consequently `256C₂`. Explicit conditioning, weighted approximation, and quadratic confinement compile with only `propext`, `Classical.choice`, and `Quot.sound`. Final direct audits remain pending.

## Numerical prime coercivity

For a packet supported on `Q<m≤R`, assume `R⁶≤N`, `18(1+log R)≤log N`, and `(1+log R)²/√log N≤1`. The existing prime residual estimate and polarized Gram bound imply

`primeEnergy(y) ≥ (½ log Q − C) ‖y‖²`.

Indeed, shift adjunction energies by `g=|γ|`. They lie between `log m` and `2(g+1)(1+log R)`. Polarization bounds the diagonal discrepancy by `36(g+1)‖y‖²`; the prime residual costs `2C_res‖y‖²`; the Riesz bounds give `½‖y‖²≤Σa_m²≤2‖y‖²`. Thus `C=37g+36+2C_res`. This removes the confinement constant from the logarithmic slope. Lean verification is pending in `CompletedArithmeticForms/PrimePacketCoercivity.lean`.

## All-vector exponent

Fixed squared projection tolerance `1/4` suffices. Enlarge `R` so
`log R ≥ D[1+(B+4C_cross²)/b]c¹⁶`, where `D` is the explicit reverse-gap constant. Orthogonality gives `D_N(w)≥(log R/D−1)‖w‖²`; the polynomial reserve then gives `W(w)≥4C_cross²c⁶‖w‖²`. Since `‖u‖≤1`, completing a square yields `2|W(u,w)|−W(w)≤1/4`. Thus `log R≪c¹⁶` suffices without a shrinking projection tolerance.

Put `L=log N`, `Q=floor(L^(1/16))`, and `α<1/144`. Eventually `1+log R≤L^(6/25)`, since `16/144<19/80` and the constant is absorbed by `L^(1/400)`. The binding error exponents are

`5/16+24/144−1/2=−1/48`,
`4/144−1/32=−1/288`,
`2(6/25)−1/2=−1/50`.

All admit margin `L^(−1/500)`. High-packet prime coercivity contributes `¼log Q−O(1)`, which dominates `log c` since `1/64−α>0`. The existing all-vector reduction then retains its uniform `c⁻⁷` spectral floor. This strengthened positivity proof is written but not yet Lean-verified.

## Remaining mathematical work

Complete Lean verification and umbrella wiring. Determine whether sharper confinement or residual transfer reaches the stated `1/19` and `1/16` method ceilings; `1/144` does not settle that request. A2–A18 remain outside this card and unsolved by these bounds.

## Gates

- [x] Precise target and source dependencies identified.
- [ ] Dependency-closed proof of the strengthened bounds.
- [ ] Lean formalization, direct file audit, and transitive axiom audit.

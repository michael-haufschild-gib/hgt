# Lag sums along all long spacings: local finiteness is the dividing line

- **ID:** lag-band-limited-dichotomy
- **Stage:** 3-formalized
- **Source:** JAS goal loop row 195; STATUS MUST-1379

## Statement
1. **Band-limited blindness.** For every `ε > 0` and `Θ > 0` there is a countable configuration `ρ_i` with `½ < Re ρ_i < ½ + Θ` and weights `c_i > 0`, `Σ c_i < ∞`, such that `Σ c_i e^{s(ρ_i − ½)} = 0` for every real `|s| ≥ ε`.
   - The same holds for the symmetric copies.
   - Every sample `m ≠ 0` of every progression with spacing `ℓ ≥ ε` vanishes.
2. **Locally finite rigidity.** Assume:
   - the ordinates are locally finite;
   - the real parts are bounded above;
   - the weights are summable;
   - the lag sum vanishes on a half-line, or along all progressions `mℓ` (`m ≥ 1`, `ℓ ∈ (c, d)`).

   Then all weights are zero.

## Proof
1. **The density.**
   - `g(y) = sinc(πy)²` is the Fourier transform of the triangle `χ ⋆ χ`, where `χ = 1_{[−½,½]}`.
   - Fourier inversion gives `∫ e^{2πiyw} g(y) dy = (1 − |w|)_+`.
2. **The configuration.**
   - The open region `W = {x₁ < Re z < x₂, 0 < c < g(εIm z/2π)}` of `ℂ × ℝ` is packed a.e. by disjoint closed sup-metric balls, which are cylinders `D(a,r) × [c − r, c + r]` (Besicovitch).
   - The cylinder integral of `e^{sz}` equals `2πr³ e^{sa}`, by the disc mean value from the power series and `∫_D z^k = πr²a^k`.
   - The `W`-integral equals `∫_{x₁}^{x₂} e^{sx}dx · ∫ e^{isy} g(εy/2π) dy` (Fubini), which vanishes for `|s| ≥ ε`.
3. **Rigidity.**
   - For `Re z > B`, `C(z) = Σ b_i/(z − w_i)` with `b_i = a_i e^{s₁w_i}` equals `∫_0^∞ e^{−zt} Σ_i a_i e^{(s₁+t)w_i} dt`, which is `0`.
   - `C` is holomorphic on the complement of the closed countable point set, and that complement is path-connected, so `C ≡ 0`.
   - Near `w_j` the series minus `b_j/(z − w_j)` is bounded, so `b_j = 0`.
   - For an interval of spacings, the products `mℓ` cover `(cd/(d − c), ∞)`.

## Lean
- Modules:
  - `HTGeometry/BandLimitedPositiveDensity`: `integral_cexp_mul_sincSq`, `fourier_triangle`, `integral_sincSq`.
  - `HTGeometry/BandLimitedPositiveConfiguration`: `setIntegral_closedBall_cexp`, `exists_ball_packing`, `exists_disc_configuration_of_density`, `exists_positive_configuration_bandLimited`.
  - `HTGeometry/LocallyFiniteExponentialSumRigidity`: `eq_zero_of_hasSum_cexp_eq_zero`, `cauchySeries_eq_zero_of_hasSum`, `differentiableOn_cauchySeries`, `isClosed_range`.
  - `RHTower/WeilLagBandLimitedDichotomy`: `exists_positive_lag_configuration_bandLimited`, `exists_symmetric_lag_configuration_bandLimited`, `exists_positive_lag_configuration_vanishing_long_progressions`, `eq_zero_of_lag_vanishing_halfLine`, `eq_zero_of_lag_vanishing_interval_spacings`.
- Axioms: propext, Classical.choice, Quot.sound.

## Consequence
- Multi-spacing zero-side rigidity comes only from local finiteness.
- Two-base blindness must spread points to infinite height without a common fold.
  - Product-grid circle quadrature at growing heights does this for sector weights (`HTGeometry/TwoBaseCircleQuadrature`).
  - Intervals of spacings cannot be blinded this way.

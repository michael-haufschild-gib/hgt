# Divisor Bernstein cone rigidifies all symmetric integer-scale theta gauges — Lean certificate

- **Paper card:** `theta-divisor-bernstein-gauge-rigidity.md`
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaDivisorBernsteinGauge`, on top of the real-shift
  gauge layer `GaloisForLFunctions.RHTower.ThetaTranslationGaugeFlux`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build`; `#print axioms` = `propext`, `Classical.choice`,
  `Quot.sound` for all 16 audited theorems; no `sorry`.

Notation: `g = thetaDivisorGauge c` (encoded as `thetaTranslationGauge (divisorGaugeCoeff c) divisorShift`
over `ℤ`, `j ↦ c_{|j|+1} k(· + sign(j) log(|j|+1))`); hypothesis `hc : Summable (|c n| √n)`;
`Q_b = divisorTail c b`, `R_a = divisorIntegerWeight c a`, `M₀ = divisorGaugeMass c`,
`M_{1/2} = divisorGaugeCharge c`, `F = divisorAbelWeight`, `β = divisorMoebiusWeight`,
`φ = divisorTotient`, `J_{1/2} = divisorJordanHalf`.

| Card item | Lean theorem |
|-|-|
| (1) theta flux `b_k = 2π∑r²e^{-πr²t}` | `thetaNormalizedFlux_thetaCuspFullSource` |
| (3) the gauge `c₁k + ∑_{n≥2} c_n(k(·+log n)+k(·-log n))` | `thetaDivisorGauge_apply` |
| (11) flux formula; absolute convergence; termwise Mellin on `|Re w| ≤ 1/2` | `thetaNormalizedFlux_thetaDivisorGauge`, `integral_exp_mul_thetaTranslationGauge`, `integral_cexp_mul_thetaTranslationGauge` |
| rate weights `2π(a/b)²Q_b`, `2πa²R_a` | `divisorGauge_rate_weights` (via `divisorRateCoeff_frac`, `divisorRateCoeff_nat`) |
| (6) `b_g` CM ⇔ `Q_b ≥ 0 ∀b≥2` and `R_a ≥ 0 ∀a≥1` | `completelyMonotoneOn_divisorGauge_iff` |
| (7) `M₀`, `M_{1/2}` are the anchor multipliers | `divisorGauge_integral`, `divisorGauge_integral_exp_half` |
| (8) `F(n) = ∑_{d∣n} β(d)`; `β(1) = 0` | `sum_divisors_divisorMoebiusWeight`, `divisorMoebiusWeight_one` |
| (9) `β(d) = φ(d) - 2J_{1/2}(d) > 0` for `d > 1`; `φ` = Euler totient; `J_{1/2}(d) = √d∏(1-1/√p)` | `divisorMoebiusWeight_eq`, `divisorMoebiusWeight_pos`, `divisorTotient_eq_totient`, `divisorJordanHalf_eq_prod` |
| (12) `φ(d)/J_{1/2}(d) = ∏ p^{(e-1)/2}(√p+1) > 2` | `divisorTotient_eq_jordan_mul_prod` (and the product bound inside `divisorMoebiusWeight_pos`) |
| (10) `Δ = ∑_{d≥2} β(d)Q_d` | `hasSum_divisorChargeGap` (with `divisorGaugeCharge_sub_mass`) |
| (6) ⇒ `M_{1/2} ≥ M₀` | `divisorChargeGap_nonneg` |
| (13) `v_n = ∑_k μ(k)Q_{nk}` | `hasSum_moebius_divisorTail` |
| equality ⇔ `c_n = 0 ∀ n ≥ 2` | `divisorChargeGap_eq_zero_iff` |
| both anchors ⇒ `c₁ = 1`, `g = k` | `divisorGauge_rigidity` |
| prime-power chain `β(p^j) = F(p^j) - F(p^{j-1})` | `divisorMoebiusWeight_prime_pow` |

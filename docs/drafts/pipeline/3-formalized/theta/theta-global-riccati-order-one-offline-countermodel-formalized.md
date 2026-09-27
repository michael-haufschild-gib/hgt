# Global reflected Riccati positivity does not orient an order-one Fourier divisor — Lean certificate

- **Paper card:** `theta-global-riccati-order-one-offline-countermodel.md`
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaRiccatiGaussianCountermodel`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build`; `#print axioms` = `propext`, `Classical.choice`,
  `Quot.sound` for all 16 audited theorems; no `sorry`.

The family is `g = riccatiSource a σ ε`, `g_ε(x) = exp(-ε(cosh(x/σ)-1)) g₀(x)` with
`g₀ = h_σ + a h_σ(·-L) + a h_σ(·+L)`, `L = σ/2` (the card's `σ ≥ 2L` with equality, so `δ = 1/2`,
`K = 3`, `c = 1/(2σ)`); `F = riccatiFourier a σ ε`, `ℓ = log g = riccatiLog`,
`A = riccatiAction`, `A_t, A_tt, A_ttt = riccatiJetOne/Two/Three`, margin `riccatiMargin`.

| Card item | Lean theorem |
|-|-|
| Theorem (all of 1–3 for every `N`, `η > 0`, interval `(α, β)`) | `globalRiccati_offline_countermodel` |
| 1. positive, even, real-analytic | `riccatiSource_pos`, `riccatiSource_neg`, `analyticAt_riccatiSource` |
| 1. superexponential decay of every derivative | `iteratedDeriv_riccatiSource_decay` (Cauchy estimates on the entire extension `riccatiSourceC`) |
| 1. `F` entire of order at most one | `differentiable_riccatiFourier`, `norm_riccatiFourier_le`, `riccatiFourier_order_le_one` |
| 1. `log g` globally strictly concave, `(log g)'' ≤ -3/(4σ²)` | `strictConcaveOn_log_riccatiSource`, `riccatiLogTwo_le` |
| 2. `A, A_t, A_tt > 0`, `2A_tA_tt - A_ttt > 0` (jets are the `t`-derivatives) | `riccati_reflected_positivity`, `hasDerivAt_riccatiAction`, `hasDerivAt_riccatiJetOne`, `hasDerivAt_riccatiJetTwo` |
| (1) cumulants: `0 ≤ f'' ≤ 1`, `f'''' ≥ -3`, `f'''(y+v)-f'''(y-v) ≥ -6v` | `riccatiCumulantTwo_mem`, `riccatiCumulantFour_ge`, `riccatiCumulantThree_increment` |
| (2) `2A_tA_tt - A_ttt ≥ 66 c⁴ t`, damping decomposition | `riccatiMargin_ge`, `riccatiJetOne_split`, `riccatiJetTwo_split`, `riccatiJetThree_split` |
| `log g₀ = -x²/(2σ²) + f(cx)` | `riccatiBase_eq`, `riccatiSource_eq_exp` |
| `F₀(z) = √(2π)σ e^{-σ²z²/2}(1 + 2a cos(Lz))` | `riccatiFourier_zero`, `integral_riccatiGauss_mul_cexp` |
| simple zeros `z_n = ((2n+1)π + iA₀)/L`, isolation | `riccatiFourier_riccatiZero`, `riccatiZero_simple`, `riccatiZero_isolated`, `riccatiFourier_zero_eq_zero_lattice` |
| `F_ε → F₀` locally uniformly; Rouché/Hurwitz persistence | `tendstoLocallyUniformly_riccatiFourier`, `eventually_riccatiZeros` |
| 3. at least `N` distinct zeros in `Re z ∈ I`, `0 < Im z < η` | `globalRiccati_offline_countermodel` |
| `F` even, `F(z̄) = conj F(z)` | `riccatiFourier_neg`, `riccatiFourier_conj` |
| growth via `max(sy - κe^y)` | `mul_sub_exp_le_mul_log` |

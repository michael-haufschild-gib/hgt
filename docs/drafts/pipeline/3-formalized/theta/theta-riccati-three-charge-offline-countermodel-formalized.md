# Exact scalar theta charges do not repair global Riccati zero control — Lean certificate

- **Paper card:** `theta-riccati-three-charge-offline-countermodel.md`
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaRiccatiThreeChargeCountermodel`
  (on top of `GaloisForLFunctions.RHTower.ThetaRiccatiGaussianCountermodel`)
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build`; `lake env lean` audit clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

The density is `g = C · riccatiSource a σ ε` with `L = σ/2`; `riccatiMass`/`riccatiCharge` are
`∫ g_ε` and `∫ e^{x/2} g_ε`; `R₀ = riccatiRatioZero a σ`.

| Card item | Lean theorem |
|-|-|
| Theorem 1–4 for every `0 < M < Q`, `η > 0` | `riccati_three_charge_countermodel` |
| 1. `∫g = M`, `∫e^{±x/2}g = Q` | `riccati_three_charge_countermodel`, `riccatiCharge_eq_integral_neg` |
| 2. positive, even, analytic, superexponential derivative decay | `riccati_three_charge_countermodel` (from `riccatiSource_pos`, `riccatiSource_neg`, `analyticAt_riccatiSource`, `iteratedDeriv_riccatiSource_decay`) |
| 2. `log g` strictly (strongly) concave, `(log g)'' ≤ -3/(4σ²)` | `riccati_three_charge_countermodel`, `riccatiLogTwo_le`, `hasDerivAt_riccatiLog`, `hasDerivAt_riccatiLogOne` (scaling by `C` adds a constant) |
| 2. `F` entire of order at most one; `∫ g e^{izx} = C F` | `riccati_three_charge_countermodel` (`differentiable_riccatiFourier`, `riccatiFourier_order_le_one`) |
| 3. `A, A_t, A_tt > 0`, `2A_tA_tt - A_ttt > 0` for `A` built from `log g` | `riccati_three_charge_countermodel` (`riccati_reflected_positivity`) |
| 4. zero with `0 < Im z < η`; reflection quartet | `riccati_three_charge_countermodel`, `riccatiFourier_neg`, `riccatiFourier_conj` |
| literal theta: `0 < Mθ < 1/2`, `∫e^{-x/2}φ = 1/2` | `integral_thetaCuspFullSource_mem`, `integral_exp_neg_half_mul_thetaCuspFullSource` |
| `(M,Q) = (Mθ, 1/2)` matches all three literal budgets | `riccati_three_charge_theta_budgets` |
| (1) `R₀ = e^{σ²/8}(1+2a cosh(σ/4))/(1+2a)` | `riccatiMass_zero`, `riccatiCharge_zero`, `riccatiCharge_div_mass_zero` |
| `σ ↦ R₀` continuous, strictly increasing, from `1` to `∞` | `continuous_riccatiRatioZero`, `riccatiRatioZero_strictMonoOn`, `riccatiRatioZero_ge`, `riccatiRatioZero_le` |
| continuity of `Rε` on compact `σ` intervals, `Rε → R₀` | `continuousOn_riccatiIntegral`, `continuousOn_riccatiMass`, `continuousOn_riccatiCharge`, `tendsto_riccatiIntegrals` |
| `F(0) = mass`, `F(-i/2) = charge` | `riccatiFourier_eq_mass`, `riccatiFourier_eq_charge`, `riccatiMass_pos` |
| zero height `2 arcosh(1/(2a))/σ` | `riccatiDepth_of_cosh`, `riccatiZero_im` |
| Rouché/Hurwitz persistence of the simple zero | `eventually_riccatiZeros`, `tendstoLocallyUniformly_riccatiFourier` |

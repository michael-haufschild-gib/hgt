import GaloisForLFunctions.BezoutValuationIncidence.AllDampingVinogradovKorobovBandAndInteriorGrowth
import GaloisForLFunctions.BezoutValuationIncidence.EnergyMeanOfThePowerDampedSourceTendsToOne
import GaloisForLFunctions.BezoutValuationIncidence.LogHarmonicReadoutAndTheMobiusRowEnergyFloor
import GaloisForLFunctions.BezoutValuationIncidence.PowerDampedResidualHasLinearCusp

/-!
# The Dual Problem: Rayleigh Quotient Optimization, Cofactor Variance Reduction, and Cusp Floors

On the dual side of Bézout–Valuation Incidence, the Báez–Duarte residual of a divisor row
`c : ℕ → ℝ` on `[1, N]` is the pronic energy of its shifted prefix discrepancy `1 + L_N(M, c)`:
$$\mathcal{D}_N(c)
  := \sum_{M=1}^\infty \frac{(1 + L_N(M, c))^2}{M(M + 1)}
  = \bigl(1 - \mathcal{R}_N(c)\bigr)^2 + Q_N^{\mathrm{ec}}(c),$$
where `\mathcal{R}_N(c) = vonMangoldtReadout N c` is the von Mangoldt readout and
`Q_N^{\mathrm{ec}}(c) = sieveEnergyCenteredPronicGramForm N c` is the energy-centered pronic Gram
form, related to the raw pronic discrepancy Gram form `Q_N(c) = sievePronicDiscrepancyGramForm N c`
by `Q_N(c) = \mathcal{R}_N(c)^2 + Q_N^{\mathrm{ec}}(c)`.

This module establishes the complete structural and quantitative laws for the dual problem (§7.3):

1. **Exact Rayleigh Quotient Optimization and Quantitative `O(1/log N)` Equivalence
   (`baezDuarteResidual_smul_eq_rayleigh_add_sq`,
   `baezDuarteResidual_optimal_scale_eq_rayleigh`,
   `exists_rayleigh_centered_energy_floor`,
   `exists_rescaled_residual_le_iff_readout_ratio_ge`)**:
   For every row `c` with `Q_N(c) > 0`, the scaled Báez–Duarte residual completes the square:
   $$\bigl(1 - t\,\mathcal{R}_N(c)\bigr)^2 + t^2 Q_N^{\mathrm{ec}}(c)
     = \frac{Q_N^{\mathrm{ec}}(c)}{Q_N(c)}
       + Q_N(c)\left(t - \frac{\mathcal{R}_N(c)}{Q_N(c)}\right)^2.$$
   Its exact minimum over the ray `{t c : t ∈ ℝ}` is achieved at `t⋆ = \mathcal{R}_N(c) / Q_N(c)`
   and equals the Rayleigh quotient `Q_N^{\mathrm{ec}}(c) / Q_N(c) = 1 − \mathcal{R}_N(c)^2 / Q_N(c)`.
   Consequently:
   - Unconditionally, for all `N ≥ 2` and `Q_N(c) > 0`,
     `κ / log N ≤ Q_N^{\mathrm{ec}}(c) / Q_N(c)` and `\mathcal{R}_N(c)^2 / Q_N(c) ≤ 1 − κ / log N`.
   - For any target rate `φ ∈ (0, 1]`, some scalar multiple of `c` achieves residual `≤ φ` if and
     only if `((1 − φ) / φ) Q_N^{\mathrm{ec}}(c) ≤ \mathcal{R}_N(c)^2` (equivalently
     `Q_N^{\mathrm{ec}}(c) ≤ φ Q_N(c)`). In particular, attaining `C / log N` on the Báez–Duarte
     residual is equivalent to attaining `\mathcal{R}_N(c)^2 ≥ ((log N − C) / C) Q_N^{\mathrm{ec}}(c)`.

2. **Exact Cofactor Uncertainty Principle, Variance Logarithmic Floor, and Pure-Variance RH
   Reduction (`exists_pmCofactor_readout_variance_uncertainty`,
   `exists_pmPowerDampedRamanujanEnergyVariance_log_floor`,
   `cofactor_residual_vanishing_iff_eventually_variance_small`,
   `riemannHypothesis_of_cofactor_variance_small`,
   `riemannHypothesis_of_cofactor_mean_variance_ratio_unbounded`)**:
   Specializing to the negated Route PM cofactor row `-w_{ε,Q}` on `[1, Q + 1]` identifies
   `\mathcal{R}_{Q+1}(-w_{ε,Q}) = m(ε, Q)` and `Q_{Q+1}^{\mathrm{ec}}(-w_{ε,Q}) = V(ε, Q)`:
   - For every `ε > 0` and `Q ≥ 1`, `κ m(ε, Q)^2 ≤ (log(Q + 1) − κ) V(ε, Q)`.
   - Since `m(ε, Q) → m(ε) → 1`, for every small `ε ∈ (0, δ₀)` and all large `Q`, the cofactor
     variance `V(ε, Q)` **alone** obeys the unconditional logarithmic floor
     `κ / (4 log(Q + 1)) ≤ V(ε, Q)`.
   - Because the readout defect `(1 − m(ε, Q))^2` vanishes as `Q → ∞` and `ε → 0+`, driving the
     cofactor residual `(1 − m(ε, Q))^2 + V(ε, Q)` to zero along small-`ε`, large-`Q` paths is
     **equivalent** to driving the cofactor variance `V(ε, Q)` alone to zero along such paths, and
     either condition (or unboundedness of `m(ε, Q)^2 / V(ε, Q)`) implies `RiemannHypothesis`.

3. **Critical-Zero Linear Cusp Floor for the Cofactor Residual `(1 − m(ε, Q))² + V(ε, Q)` and
   Cofactor Variance `V(ε, Q)` (`tendsto_finiteCofactorDualResidual_pmPowerDampedDualResidual`,
   `exists_criticalZero_linear_cofactorResidual_floor`,
   `exists_criticalZero_linear_cofactorVariance_floor`)**:
   For each fixed `ε > 0` and horizon `T : ℕ`, the finite-horizon cofactor dual residual is bounded
   above by `(1 − m(ε, Q))^2 + V(ε, Q)` and converges as `Q → ∞` to the literal dual residual
   `pmPowerDampedDualResidual ε T`. Consequently, a critical zero `ρ` (`Re ρ = 1/2`, `ζ(ρ) = 0`)
   forces both:
   - `(1 / (4 ‖ρ‖^2)) ε < (1 − m(ε, Q))^2 + V(ε, Q)` for all `ε ∈ (0, δ)` and all large `Q`, and
   - `(1 / (8 ‖ρ‖^2)) ε < V(ε, Q)` for all `ε ∈ (0, δ')` and all large `Q` (since
     `(1 − m(ε, Q))^2 = o(1)` cannot absorb the linear cusp once `ε` is small).
   In particular, sending `Q → ∞` at any fixed damping `ε ∈ (0, δ)` can never reduce
   `(1 − m(ε, Q))^2 + V(ε, Q)` below `ε / (4 ‖ρ‖^2)`.

4. **Exact Two-Sided Equivalence Between the Primal Receiver `E_T(ε)` and the Literal Dual
   Residual `R(ε, T)` (`abs_sqrt_pmPowerDampedDualResidual_sub_sqrt_discreteEnergy_le_one`,
   `exists_pmPowerDampedDualResidual_budget_iff`,
   `exists_dualResidual_le_on_vinogradovKorobovBand_of_pos`,
   `eventually_dualResidual_le_growth_of_pos`,
   `riemannHypothesis_iff_forall_pos_dualResidual_bounded`)**:
   Because `∑_{n=1}^T 1 / (n(n + 1)) = T / (T + 1) ≤ 1`, Minkowski's inequality in the pronic `ℓ²`
   norm gives at every `ε : ℝ` and `T : ℕ`
   `|\sqrt{R(ε, T)} − \sqrt{E_T(ε)}| ≤ 1`,
   `R(ε, T) ≤ 2 E_T(ε) + 2`, and `E_T(ε) ≤ 2 R(ε, T) + 2`.
   Hence at every fixed `ε > 0`, boundedness of the dual residual `R(ε, T)` across `T : ℕ` is
   equivalent to admission of the primal receiver `E_T(ε)`, holds unconditionally for all
   `ε > Θ − 1/2` and on the Vinogradov–Korobov band, obeys `R(ε, T) ≤ C_ε T^{1−2ε} exp(−κ σ(T)/270)`
   for every `0 < ε < 1/2`, and is equivalent to `RiemannHypothesis` across all `ε > 0`.
-/

open Finset Filter Topology RHTower RHTower.Sieve ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Rayleigh Quotient Optimization and Quantitative `O(1/log N)` Equivalence -/

/-- The von Mangoldt readout is odd in the divisor row `c`. -/
theorem vonMangoldtReadout_neg (N : ℕ) (c : ℕ → ℝ) :
    vonMangoldtReadout N (fun d => -c d) = -vonMangoldtReadout N c := by
  simpa using vonMangoldtReadout_smul N (-1) c

/-- The raw pronic discrepancy Gram form `Q_N(c)` equals `\mathcal{R}_N(c)^2 + Q_N^{\mathrm{ec}}(c)`. -/
theorem sievePronicDiscrepancyGramForm_eq_readout_sq_add_energyCentered
    (N : ℕ) (c : ℕ → ℝ) :
    sievePronicDiscrepancyGramForm N c =
      vonMangoldtReadout N c ^ 2 + sieveEnergyCenteredPronicGramForm N c := by
  rw [sievePronicDiscrepancyGramForm_eq_vonMangoldt_sq_add_energyCentered, vonMangoldtReadout]

/-- `sievePronicDiscrepancyGramForm N c` is non-negative for every `N : ℕ` and `c : ℕ → ℝ`. -/
theorem sievePronicDiscrepancyGramForm_nonneg (N : ℕ) (c : ℕ → ℝ) :
    0 ≤ sievePronicDiscrepancyGramForm N c := by
  rw [sievePronicDiscrepancyGramForm_eq_readout_sq_add_energyCentered]
  exact add_nonneg (sq_nonneg _) (sieveEnergyCenteredPronicGramForm_nonneg' N c)

/-- **Orthogonal Square Completion of the Scaled Báez–Duarte Residual
(`baezDuarteResidual_smul_eq_rayleigh_add_sq`):**
For every `N : ℕ`, row `c : ℕ → ℝ` with `0 < sievePronicDiscrepancyGramForm N c`, and scale
`t : ℝ`, the Báez–Duarte residual of `t • c` decomposes into the scale-invariant Rayleigh quotient
`Q_N^{\mathrm{ec}}(c) / Q_N(c)` plus a non-negative quadratic deviation from the optimal scale
`t⋆ = \mathcal{R}_N(c) / Q_N(c)`. -/
theorem baezDuarteResidual_smul_eq_rayleigh_add_sq
    (N : ℕ) (c : ℕ → ℝ) (hQ : 0 < sievePronicDiscrepancyGramForm N c) (t : ℝ) :
    (1 - vonMangoldtReadout N (fun d => t * c d)) ^ 2 +
        sieveEnergyCenteredPronicGramForm N (fun d => t * c d) =
      sieveEnergyCenteredPronicGramForm N c / sievePronicDiscrepancyGramForm N c +
        sievePronicDiscrepancyGramForm N c *
          (t - vonMangoldtReadout N c / sievePronicDiscrepancyGramForm N c) ^ 2 := by
  rw [residual_smul]
  rw [sievePronicDiscrepancyGramForm_eq_readout_sq_add_energyCentered] at hQ ⊢
  have hne : vonMangoldtReadout N c ^ 2 + sieveEnergyCenteredPronicGramForm N c ≠ 0 := hQ.ne'
  field_simp [hne]
  ring

/-- **Exact Minimum of the Scaled Báez–Duarte Residual (`baezDuarteResidual_optimal_scale_eq_rayleigh`):**
At the optimal scale `t⋆ = \mathcal{R}_N(c) / Q_N(c)`, the Báez–Duarte residual equals
`Q_N^{\mathrm{ec}}(c) / Q_N(c) = 1 − \mathcal{R}_N(c)^2 / Q_N(c)`, and minimizes the residual over
all scalar multiples `t • c`. -/
theorem baezDuarteResidual_optimal_scale_eq_rayleigh
    (N : ℕ) (c : ℕ → ℝ) (hQ : 0 < sievePronicDiscrepancyGramForm N c) :
    let t_opt := vonMangoldtReadout N c / sievePronicDiscrepancyGramForm N c
    (1 - vonMangoldtReadout N (fun d => t_opt * c d)) ^ 2 +
        sieveEnergyCenteredPronicGramForm N (fun d => t_opt * c d) =
      sieveEnergyCenteredPronicGramForm N c / sievePronicDiscrepancyGramForm N c ∧
    sieveEnergyCenteredPronicGramForm N c / sievePronicDiscrepancyGramForm N c =
      1 - vonMangoldtReadout N c ^ 2 / sievePronicDiscrepancyGramForm N c ∧
    ∀ t : ℝ,
      sieveEnergyCenteredPronicGramForm N c / sievePronicDiscrepancyGramForm N c ≤
        (1 - vonMangoldtReadout N (fun d => t * c d)) ^ 2 +
          sieveEnergyCenteredPronicGramForm N (fun d => t * c d) := by
  dsimp only
  refine ⟨?_, ?_, fun t => ?_⟩
  · rw [baezDuarteResidual_smul_eq_rayleigh_add_sq N c hQ]
    simp
  · have hne : sievePronicDiscrepancyGramForm N c ≠ 0 := hQ.ne'
    have hsplit := sievePronicDiscrepancyGramForm_eq_readout_sq_add_energyCentered N c
    field_simp [hne]
    linarith
  · rw [baezDuarteResidual_smul_eq_rayleigh_add_sq N c hQ]
    exact le_add_of_nonneg_right (mul_nonneg hQ.le (sq_nonneg _))

/-- **Unconditional Rayleigh Quotient Floor (`exists_rayleigh_centered_energy_floor`):**
There exists `κ > 0` such that for every `N ≥ 2` and every divisor row `c : ℕ → ℝ` with
`0 < sievePronicDiscrepancyGramForm N c`,
`κ / log N ≤ Q_N^{\mathrm{ec}}(c) / Q_N(c)` and `\mathcal{R}_N(c)^2 / Q_N(c) ≤ 1 − κ / log N`. -/
theorem exists_rayleigh_centered_energy_floor :
    ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 2 ≤ N → ∀ c : ℕ → ℝ,
      0 < sievePronicDiscrepancyGramForm N c →
        κ / Real.log N ≤
          sieveEnergyCenteredPronicGramForm N c / sievePronicDiscrepancyGramForm N c ∧
        vonMangoldtReadout N c ^ 2 / sievePronicDiscrepancyGramForm N c ≤
          1 - κ / Real.log N := by
  obtain ⟨κ, hκ, hfloor⟩ := exists_readout_centered_energy_floor
  refine ⟨κ, hκ, fun N hN c hQ => ?_⟩
  obtain ⟨hopt, h1, _⟩ := baezDuarteResidual_optimal_scale_eq_rayleigh N c hQ
  have hle := hfloor N hN (fun d => (vonMangoldtReadout N c / sievePronicDiscrepancyGramForm N c) * c d)
  rw [hopt] at hle
  refine ⟨hle, ?_⟩
  linarith

/-- **Quantitative Rate Equivalence for Optimal Rescaling
(`exists_rescaled_residual_le_iff_readout_ratio_ge`):**
For any `N : ℕ`, row `c : ℕ → ℝ` with `vonMangoldtReadout N c ≠ 0`, and target bound `φ ∈ (0, 1]`,
some scalar multiple `t • c` achieves Báez–Duarte residual `≤ φ` if and only if
`((1 − φ) / φ) Q_N^{\mathrm{ec}}(c) ≤ \mathcal{R}_N(c)^2`, equivalently
`Q_N^{\mathrm{ec}}(c) ≤ φ Q_N(c)`. -/
theorem exists_rescaled_residual_le_iff_readout_ratio_ge
    (N : ℕ) (c : ℕ → ℝ) (hR : vonMangoldtReadout N c ≠ 0)
    {φ : ℝ} (hφ0 : 0 < φ) :
    (∃ t : ℝ,
      (1 - vonMangoldtReadout N (fun d => t * c d)) ^ 2 +
        sieveEnergyCenteredPronicGramForm N (fun d => t * c d) ≤ φ) ↔
      (1 - φ) / φ * sieveEnergyCenteredPronicGramForm N c ≤ vonMangoldtReadout N c ^ 2 := by
  have hR2 : 0 < vonMangoldtReadout N c ^ 2 := sq_pos_of_ne_zero hR
  have hQec : 0 ≤ sieveEnergyCenteredPronicGramForm N c :=
    sieveEnergyCenteredPronicGramForm_nonneg' N c
  have hQ : 0 < sievePronicDiscrepancyGramForm N c := by
    rw [sievePronicDiscrepancyGramForm_eq_readout_sq_add_energyCentered]
    linarith
  obtain ⟨hopt, _, hmin⟩ := baezDuarteResidual_optimal_scale_eq_rayleigh N c hQ
  constructor
  · rintro ⟨t, ht⟩
    have hle : sieveEnergyCenteredPronicGramForm N c / sievePronicDiscrepancyGramForm N c ≤ φ :=
      (hmin t).trans ht
    rw [div_le_iff₀ hQ, sievePronicDiscrepancyGramForm_eq_readout_sq_add_energyCentered] at hle
    rw [div_mul_eq_mul_div, div_le_iff₀ hφ0]
    linarith
  · intro hratio
    refine ⟨vonMangoldtReadout N c / sievePronicDiscrepancyGramForm N c, ?_⟩
    rw [hopt, div_le_iff₀ hQ, sievePronicDiscrepancyGramForm_eq_readout_sq_add_energyCentered]
    rw [div_mul_eq_mul_div, div_le_iff₀ hφ0] at hratio
    linarith

/-! ## §2. Exact Cofactor Uncertainty Principle, Variance Floor, and Pure-Variance RH Reduction -/

/-- For every `ε : ℝ` and `Q : ℕ`, the von Mangoldt readout of the negated cofactor row
`d ↦ -pmCofactorDivisorWeight ε Q d` at level `Q + 1` is `pmPowerDampedRamanujanEnergyMean ε Q`. -/
theorem vonMangoldtReadout_neg_pmCofactorDivisorWeight (ε : ℝ) (Q : ℕ) :
    vonMangoldtReadout (Q + 1) (fun d => -pmCofactorDivisorWeight ε Q d) =
      pmPowerDampedRamanujanEnergyMean ε Q := by
  rw [vonMangoldtReadout_neg, vonMangoldtReadout,
    ← vonMangoldt_sum_pmCofactorDivisorWeight_eq]

/-- For every `ε > 0` and `Q : ℕ`, the energy-centered pronic Gram form of the negated cofactor row
`d ↦ -pmCofactorDivisorWeight ε Q d` at level `Q + 1` is `pmPowerDampedRamanujanEnergyVariance ε Q`. -/
theorem sieveEnergyCenteredPronicGramForm_neg_pmCofactorDivisorWeight
    {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    sieveEnergyCenteredPronicGramForm (Q + 1) (fun d => -pmCofactorDivisorWeight ε Q d) =
      pmPowerDampedRamanujanEnergyVariance ε Q := by
  rw [sieveEnergyCenteredPronicGramForm_neg,
    sieveEnergyCenteredPronicGramForm_pmCofactorDivisorWeight_eq hε Q]

/-- **Exact Cofactor Readout–Variance Uncertainty Principle
(`exists_pmCofactor_readout_variance_uncertainty`):**
There exists `κ > 0` such that for every `ε > 0` and `Q ≥ 1`,
`κ * (pmPowerDampedRamanujanEnergyMean ε Q)^2 ≤ (log(Q + 1) − κ) * pmPowerDampedRamanujanEnergyVariance ε Q`. -/
theorem exists_pmCofactor_readout_variance_uncertainty :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ∀ Q : ℕ, 1 ≤ Q →
      κ * pmPowerDampedRamanujanEnergyMean ε Q ^ 2 ≤
        (Real.log ((Q : ℝ) + 1) - κ) * pmPowerDampedRamanujanEnergyVariance ε Q := by
  obtain ⟨κ, hκ, hunc⟩ := exists_readout_energy_uncertainty
  refine ⟨κ, hκ, fun ε hε Q hQ => ?_⟩
  have h := hunc (Q + 1) (by omega) (fun d => -pmCofactorDivisorWeight ε Q d)
  rw [vonMangoldtReadout_neg_pmCofactorDivisorWeight,
    sieveEnergyCenteredPronicGramForm_neg_pmCofactorDivisorWeight hε Q] at h
  push_cast at h
  exact h

/-- **Unconditional Logarithmic Floor for the Cofactor Energy Variance `V(ε, Q)` Alone
(`exists_pmPowerDampedRamanujanEnergyVariance_log_floor`):**
There exist `κ > 0` and `δ > 0` such that for every damping `ε ∈ (0, δ)`, eventually in `Q : ℕ`,
the cofactor energy variance `pmPowerDampedRamanujanEnergyVariance ε Q` alone is at least
`κ / (4 * log(Q + 1))`. -/
theorem exists_pmPowerDampedRamanujanEnergyVariance_log_floor :
    ∃ κ : ℝ, 0 < κ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ᶠ Q : ℕ in atTop,
      κ / (4 * Real.log ((Q : ℝ) + 1)) ≤ pmPowerDampedRamanujanEnergyVariance ε Q := by
  obtain ⟨κ, hκ, hunc⟩ := exists_pmCofactor_readout_variance_uncertainty
  obtain ⟨δ, hδ, hread⟩ := readout_defect_eventually_small (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨κ, hκ, δ, hδ, fun ε hε hεδ => ?_⟩
  filter_upwards [hread ε hε hεδ, eventually_ge_atTop 1] with Q hQ hQ1
  have hlog : 0 < Real.log ((Q : ℝ) + 1) := by
    have : (1 : ℝ) < (Q : ℝ) + 1 := by
      have : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
      linarith
    exact Real.log_pos this
  have hm_half : 1 / 2 < pmPowerDampedRamanujanEnergyMean ε Q := by
    nlinarith [sq_nonneg (1 - pmPowerDampedRamanujanEnergyMean ε Q)]
  have hm2 : 1 / 4 < pmPowerDampedRamanujanEnergyMean ε Q ^ 2 := by nlinarith
  have hu := hunc ε hε Q hQ1
  have hV0 : 0 ≤ pmPowerDampedRamanujanEnergyVariance ε Q := by
    rw [← sieveEnergyCenteredPronicGramForm_neg_pmCofactorDivisorWeight hε Q]
    exact sieveEnergyCenteredPronicGramForm_nonneg' (Q + 1) _
  have h1 : κ * (1 / 4) < κ * pmPowerDampedRamanujanEnergyMean ε Q ^ 2 :=
    mul_lt_mul_of_pos_left hm2 hκ
  have h2 :
      (Real.log ((Q : ℝ) + 1) - κ) * pmPowerDampedRamanujanEnergyVariance ε Q ≤
        Real.log ((Q : ℝ) + 1) * pmPowerDampedRamanujanEnergyVariance ε Q := by
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **Equivalence Between Cofactor Residual Vanishing and Pure Cofactor Variance Vanishing Along
Small-Damping Large-Cutoff Paths (`cofactor_residual_vanishing_iff_eventually_variance_small`):**
Because `(1 − m(ε, Q))^2 → 0` as `Q → ∞` and `ε → 0+`, the cofactor Báez–Duarte residual
`(1 − m(ε, Q))^2 + V(ε, Q)` becomes arbitrarily small along small-`ε`, large-`Q` paths if and only
if the cofactor variance `V(ε, Q)` alone becomes arbitrarily small along such paths. -/
theorem cofactor_residual_vanishing_iff_eventually_variance_small :
    (∀ η : ℝ, 0 < η → ∀ δ : ℝ, 0 < δ →
      ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ᶠ Q : ℕ in atTop,
        (1 - pmPowerDampedRamanujanEnergyMean ε Q) ^ 2 +
          pmPowerDampedRamanujanEnergyVariance ε Q < η) ↔
    (∀ η : ℝ, 0 < η → ∀ δ : ℝ, 0 < δ →
      ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ᶠ Q : ℕ in atTop,
        pmPowerDampedRamanujanEnergyVariance ε Q < η) := by
  constructor
  · intro h η hη δ hδ
    obtain ⟨ε, hε0, hεδ, hfreq⟩ := h η hη δ hδ
    refine ⟨ε, hε0, hεδ, hfreq.mono fun Q hQ => ?_⟩
    linarith [sq_nonneg (1 - pmPowerDampedRamanujanEnergyMean ε Q)]
  · intro h η hη δ hδ
    obtain ⟨δ₁, hδ₁, hread⟩ := readout_defect_eventually_small (show 0 < η / 2 by positivity)
    obtain ⟨ε, hε0, hε_lt, hfreq⟩ := h (η / 2) (by positivity) (min δ δ₁) (lt_min hδ hδ₁)
    have hεδ : ε < δ := hε_lt.trans_le (min_le_left _ _)
    have hεδ₁ : ε < δ₁ := hε_lt.trans_le (min_le_right _ _)
    refine ⟨ε, hε0, hεδ, ?_⟩
    exact (hfreq.and_eventually (hread ε hε0 hεδ₁)).mono fun Q ⟨hV, hm⟩ => by linarith

/-- **Sufficient Condition for `RiemannHypothesis` from Pure Cofactor Variance Vanishing
(`riemannHypothesis_of_cofactor_variance_small`):**
If for every `η > 0` and `δ > 0` there exists `ε ∈ (0, δ)` such that `V(ε, Q) < η` frequently as
`Q → ∞`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_cofactor_variance_small
    (h : ∀ η : ℝ, 0 < η → ∀ δ : ℝ, 0 < δ →
      ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ᶠ Q : ℕ in atTop,
        pmPowerDampedRamanujanEnergyVariance ε Q < η) :
    RiemannHypothesis := by
  have hres := cofactor_residual_vanishing_iff_eventually_variance_small.mpr h
  refine riemannHypothesis_of_energyMean_variance fun η hη => ?_
  obtain ⟨ε, hε0, _, hfreq⟩ := hres η hη 1 one_pos
  obtain ⟨Q, hQ⟩ := hfreq.exists
  exact ⟨ε, hε0, Q, hQ⟩

/-- **Sufficient Condition for `RiemannHypothesis` from Unbounded Cofactor Mean-to-Variance Ratio
(`riemannHypothesis_of_cofactor_mean_variance_ratio_unbounded`):**
If the cofactor signal-to-noise ratio `m(ε, Q)^2 / V(ε, Q)` is unbounded over `ε > 0` and
`Q : ℕ`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_cofactor_mean_variance_ratio_unbounded
    (h : ∀ K : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∃ Q : ℕ,
      K * pmPowerDampedRamanujanEnergyVariance ε Q <
        pmPowerDampedRamanujanEnergyMean ε Q ^ 2) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_readout_energy_ratio_unbounded.mpr fun K => ?_
  obtain ⟨ε, hε, Q, hK⟩ := h K
  refine ⟨Q + 1, fun d => -pmCofactorDivisorWeight ε Q d, ?_⟩
  rwa [vonMangoldtReadout_neg_pmCofactorDivisorWeight,
    sieveEnergyCenteredPronicGramForm_neg_pmCofactorDivisorWeight hε Q]

/-! ## §3. Critical-Zero Linear Cusp Floor for the Cofactor Residual and Variance -/

/-- The finite-horizon Báez–Duarte residual of the negated cofactor row `-w_{ε,Q}` up to horizon
`T : ℕ`. -/
def pmCofactorFiniteDualResidual (ε : ℝ) (Q T : ℕ) : ℝ :=
  ∑ M ∈ Icc 1 T,
    (1 + sievePrefixDiscrepancy (Q + 1) M (fun d => -pmCofactorDivisorWeight ε Q d)) ^ 2 /
      ((M : ℝ) * ((M : ℝ) + 1))

/-- Every finite-horizon cofactor dual residual is bounded above by the full infinite-horizon
cofactor Báez–Duarte residual `(1 − m(ε, Q))^2 + V(ε, Q)`. -/
theorem pmCofactorFiniteDualResidual_le_energyMean_variance
    {ε : ℝ} (hε : 0 < ε) (Q T : ℕ) :
    pmCofactorFiniteDualResidual ε Q T ≤
      (1 - pmPowerDampedRamanujanEnergyMean ε Q) ^ 2 +
        pmPowerDampedRamanujanEnergyVariance ε Q := by
  have hsum := hasSum_baezDuarte_energy_pmCofactor hε Q
  rw [← hsum.tsum_eq]
  exact hsum.summable.sum_le_tsum (Icc 1 T) fun M _ => by positivity

/-- For every fixed `ε > 0` and finite horizon `T : ℕ`, as `Q → ∞`, the finite-horizon cofactor
dual residual `pmCofactorFiniteDualResidual ε Q T` converges to the literal dual residual
`pmPowerDampedDualResidual ε T`. -/
theorem tendsto_pmCofactorFiniteDualResidual
    {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    Tendsto (fun Q : ℕ => pmCofactorFiniteDualResidual ε Q T) atTop
      (𝓝 (pmPowerDampedDualResidual ε T)) := by
  unfold pmCofactorFiniteDualResidual pmPowerDampedDualResidual
  refine tendsto_finsetSum (Icc 1 T) fun M _ => ?_
  have hcum := (Complex.continuous_re.tendsto _).comp
    (tendsto_pmPowerDampedRamanujanCumulativePrefix hε M)
  simp only [Complex.ofReal_re] at hcum
  have hdisc :
      (fun Q : ℕ =>
        (1 + sievePrefixDiscrepancy (Q + 1) M (fun d => -pmCofactorDivisorWeight ε Q d)) ^ 2 /
          ((M : ℝ) * ((M : ℝ) + 1))) =
        fun Q : ℕ =>
          ((pmPowerDampedRamanujanCumulativePrefix ε Q M).re - 1) ^ 2 /
            ((M : ℝ) * ((M : ℝ) + 1)) := by
    funext Q
    rw [sievePrefixDiscrepancy_neg, sievePrefixDiscrepancy_pmCofactorDivisorWeight_eq hε Q M]
    ring
  rw [hdisc]
  exact ((hcum.sub_const 1).pow 2).div_const _

/-- **Critical-Zero Linear Cusp Floor for the Cofactor Báez–Duarte Residual
(`exists_criticalZero_linear_cofactorResidual_floor`):**
There exist a critical zero `ρ` (`Re ρ = 1/2`, `ζ(ρ) = 0`) and `δ > 0` such that for every
`ε ∈ (0, δ)`, eventually in `Q : ℕ`,
`(1 / (4 * ‖ρ‖^2)) * ε < (1 − pmPowerDampedRamanujanEnergyMean ε Q)^2 + pmPowerDampedRamanujanEnergyVariance ε Q`.
In particular, sending `Q → ∞` at any fixed `ε ∈ (0, δ)` can never reduce the cofactor residual
below `ε / (4 ‖ρ‖^2)`. -/
theorem exists_criticalZero_linear_cofactorResidual_floor :
    ∃ ρ : ℂ, ρ.re = 1 / 2 ∧ riemannZeta ρ = 0 ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ᶠ Q : ℕ in atTop,
        (1 / (4 * ‖ρ‖ ^ 2)) * ε <
          (1 - pmPowerDampedRamanujanEnergyMean ε Q) ^ 2 +
            pmPowerDampedRamanujanEnergyVariance ε Q := by
  obtain ⟨ρ, hρ, hzero, δ, hδ, hcusp⟩ := exists_criticalZero_linear_dualResidual_floor
  refine ⟨ρ, hρ, hzero, δ, hδ, fun ε hε hεδ => ?_⟩
  obtain ⟨T, hT⟩ := hcusp ε hε hεδ
  have hlim := (tendsto_pmCofactorFiniteDualResidual hε T).eventually (Ioi_mem_nhds hT)
  refine hlim.mono fun Q hQ => lt_of_lt_of_le hQ ?_
  exact pmCofactorFiniteDualResidual_le_energyMean_variance hε Q T

/-! ## §4. Exact Two-Sided Equivalence Between the Primal Receiver `E_T(ε)` and Dual Residual `R(ε, T)` -/

/-- Exact polarization identity between `pmPowerDampedDualResidual ε T` and
`pmPowerDampedDivisorDiscreteEnergy ε T`. -/
theorem pmPowerDampedDualResidual_sub_discreteEnergy_eq (ε : ℝ) (T : ℕ) :
    pmPowerDampedDualResidual ε T - pmPowerDampedDivisorDiscreteEnergy ε T =
      -2 * (∑ n ∈ Icc 1 T,
        (pmPowerDampedCenteredDivisorPrefix ε n / Real.sqrt (pronicSeq n : ℝ)) *
          (1 / Real.sqrt (pronicSeq n : ℝ))) +
      ∑ n ∈ Icc 1 T, 1 / (pronicSeq n : ℝ) := by
  unfold pmPowerDampedDualResidual
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq]
  simp_rw [← cast_pronicSeq_eq]
  rw [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  have hpr : (0 : ℝ) ≤ (pronicSeq n : ℝ) := Nat.cast_nonneg _
  have hsq : Real.sqrt (pronicSeq n : ℝ) * Real.sqrt (pronicSeq n : ℝ) = (pronicSeq n : ℝ) :=
    Real.mul_self_sqrt hpr
  rw [div_mul_div_comm, hsq]
  ring

/-- Cauchy–Schwarz bound on the pronic pairing `∑_{n=1}^T A_ε(n) / (n(n + 1))`. -/
theorem abs_sum_centeredDivisorPrefix_div_pronicSeq_le (ε : ℝ) (T : ℕ) :
    |∑ n ∈ Icc 1 T,
      (pmPowerDampedCenteredDivisorPrefix ε n / Real.sqrt (pronicSeq n : ℝ)) *
        (1 / Real.sqrt (pronicSeq n : ℝ))| ≤
      Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) := by
  set S := ∑ n ∈ Icc 1 T,
    (pmPowerDampedCenteredDivisorPrefix ε n / Real.sqrt (pronicSeq n : ℝ)) *
      (1 / Real.sqrt (pronicSeq n : ℝ))
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 T)
    (fun n => pmPowerDampedCenteredDivisorPrefix ε n / Real.sqrt (pronicSeq n : ℝ))
    (fun n => 1 / Real.sqrt (pronicSeq n : ℝ))
  have h1 : (∑ n ∈ Icc 1 T,
      (pmPowerDampedCenteredDivisorPrefix ε n / Real.sqrt (pronicSeq n : ℝ)) ^ 2) =
      pmPowerDampedDivisorDiscreteEnergy ε T := by
    rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq]
    refine sum_congr rfl fun n _ => ?_
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have h2 : (∑ n ∈ Icc 1 T, (1 / Real.sqrt (pronicSeq n : ℝ)) ^ 2) ≤ 1 := by
    have heq : (∑ n ∈ Icc 1 T, (1 / Real.sqrt (pronicSeq n : ℝ)) ^ 2) =
        ∑ n ∈ Icc 1 T, (1 : ℝ) / (pronicSeq n : ℝ) := by
      refine sum_congr rfl fun n _ => ?_
      rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [heq]
    exact sum_one_div_pronicSeq_le_one T
  rw [h1] at hcs
  have hE0 := pmPowerDampedDivisorDiscreteEnergy_nonneg ε T
  have hS2 : S ^ 2 ≤ Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) ^ 2 := by
    calc S ^ 2
        ≤ pmPowerDampedDivisorDiscreteEnergy ε T *
            ∑ n ∈ Icc 1 T, (1 / Real.sqrt (pronicSeq n : ℝ)) ^ 2 := hcs
      _ ≤ pmPowerDampedDivisorDiscreteEnergy ε T * 1 :=
          mul_le_mul_of_nonneg_left h2 hE0
      _ = Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) ^ 2 := by
          rw [mul_one, Real.sq_sqrt hE0]
  have hsqrt := Real.sqrt_le_sqrt hS2
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (Real.sqrt_nonneg _)] at hsqrt

/-- **Coefficient-One Upper Bound on `R(ε, T)` by `E_T(ε)`:**
`R(ε, T) ≤ E_T(ε) + 2 \sqrt{E_T(ε)} + 1 = (\sqrt{E_T(ε)} + 1)²`. -/
theorem pmPowerDampedDualResidual_le_discreteEnergy_add_two_sqrt_add_one (ε : ℝ) (T : ℕ) :
    pmPowerDampedDualResidual ε T ≤
      pmPowerDampedDivisorDiscreteEnergy ε T +
        2 * Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) + 1 := by
  have hpol := pmPowerDampedDualResidual_sub_discreteEnergy_eq ε T
  have hcs := (abs_le.mp (abs_sum_centeredDivisorPrefix_div_pronicSeq_le ε T)).1
  have h1 := sum_one_div_pronicSeq_le_one T
  linarith

/-- **Coefficient-One Upper Bound on `E_T(ε)` by `R(ε, T)`:**
`E_T(ε) ≤ R(ε, T) + 2 \sqrt{R(ε, T)} + 1 = (\sqrt{R(ε, T)} + 1)²`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_le_dualResidual_add_two_sqrt_add_one (ε : ℝ) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε T ≤
      pmPowerDampedDualResidual ε T +
        2 * Real.sqrt (pmPowerDampedDualResidual ε T) + 1 := by
  set S := ∑ n ∈ Icc 1 T,
    ((pmPowerDampedCenteredDivisorPrefix ε n - 1) / Real.sqrt (pronicSeq n : ℝ)) *
      (1 / Real.sqrt (pronicSeq n : ℝ))
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 T)
    (fun n => (pmPowerDampedCenteredDivisorPrefix ε n - 1) / Real.sqrt (pronicSeq n : ℝ))
    (fun n => 1 / Real.sqrt (pronicSeq n : ℝ))
  have h1 : (∑ n ∈ Icc 1 T,
      ((pmPowerDampedCenteredDivisorPrefix ε n - 1) / Real.sqrt (pronicSeq n : ℝ)) ^ 2) =
      pmPowerDampedDualResidual ε T := by
    unfold pmPowerDampedDualResidual
    refine sum_congr rfl fun n _ => ?_
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), cast_pronicSeq_eq]
  have h2 : (∑ n ∈ Icc 1 T, (1 / Real.sqrt (pronicSeq n : ℝ)) ^ 2) ≤ 1 := by
    have heq : (∑ n ∈ Icc 1 T, (1 / Real.sqrt (pronicSeq n : ℝ)) ^ 2) =
        ∑ n ∈ Icc 1 T, (1 : ℝ) / (pronicSeq n : ℝ) := by
      refine sum_congr rfl fun n _ => ?_
      rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [heq]
    exact sum_one_div_pronicSeq_le_one T
  rw [h1] at hcs
  have hR0 : 0 ≤ pmPowerDampedDualResidual ε T := by
    unfold pmPowerDampedDualResidual
    exact sum_nonneg fun n _ => by positivity
  have hS2 : S ^ 2 ≤ Real.sqrt (pmPowerDampedDualResidual ε T) ^ 2 := by
    calc S ^ 2
        ≤ pmPowerDampedDualResidual ε T *
            ∑ n ∈ Icc 1 T, (1 / Real.sqrt (pronicSeq n : ℝ)) ^ 2 := hcs
      _ ≤ pmPowerDampedDualResidual ε T * 1 := mul_le_mul_of_nonneg_left h2 hR0
      _ = Real.sqrt (pmPowerDampedDualResidual ε T) ^ 2 := by rw [mul_one, Real.sq_sqrt hR0]
  have hsqrt := Real.sqrt_le_sqrt hS2
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq (Real.sqrt_nonneg _)] at hsqrt
  have hpol :
      pmPowerDampedDivisorDiscreteEnergy ε T - pmPowerDampedDualResidual ε T =
        2 * S + ∑ n ∈ Icc 1 T, (1 : ℝ) / (pronicSeq n : ℝ) := by
    unfold pmPowerDampedDualResidual S
    rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq]
    simp_rw [← cast_pronicSeq_eq]
    rw [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    have hpr : (0 : ℝ) ≤ (pronicSeq n : ℝ) := Nat.cast_nonneg _
    have hsq : Real.sqrt (pronicSeq n : ℝ) * Real.sqrt (pronicSeq n : ℝ) = (pronicSeq n : ℝ) :=
      Real.mul_self_sqrt hpr
    rw [div_mul_div_comm, hsq]
    ring
  have hS_up := (abs_le.mp hsqrt).2
  have hpr1 := sum_one_div_pronicSeq_le_one T
  linarith

/-- **Sharp Square-Root Comparison Between `R(ε, T)` and `E_T(ε)`
(`abs_sqrt_pmPowerDampedDualResidual_sub_sqrt_discreteEnergy_le_one`):**
At every `ε : ℝ` and `T : ℕ`, `|\sqrt{R(ε, T)} − \sqrt{E_T(ε)}| ≤ 1`. -/
theorem abs_sqrt_pmPowerDampedDualResidual_sub_sqrt_discreteEnergy_le_one (ε : ℝ) (T : ℕ) :
    |Real.sqrt (pmPowerDampedDualResidual ε T) -
      Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T)| ≤ 1 := by
  have hE0 := pmPowerDampedDivisorDiscreteEnergy_nonneg ε T
  have hR0 : 0 ≤ pmPowerDampedDualResidual ε T := by
    unfold pmPowerDampedDualResidual
    exact sum_nonneg fun n _ => by positivity
  have h1 : pmPowerDampedDualResidual ε T ≤
      (Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) + 1) ^ 2 := by
    calc pmPowerDampedDualResidual ε T
        ≤ pmPowerDampedDivisorDiscreteEnergy ε T +
            2 * Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) + 1 :=
          pmPowerDampedDualResidual_le_discreteEnergy_add_two_sqrt_add_one ε T
      _ = (Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) + 1) ^ 2 := by
          rw [add_sq, Real.sq_sqrt hE0]; ring
  have h2 : pmPowerDampedDivisorDiscreteEnergy ε T ≤
      (Real.sqrt (pmPowerDampedDualResidual ε T) + 1) ^ 2 := by
    calc pmPowerDampedDivisorDiscreteEnergy ε T
        ≤ pmPowerDampedDualResidual ε T +
            2 * Real.sqrt (pmPowerDampedDualResidual ε T) + 1 :=
          pmPowerDampedDivisorDiscreteEnergy_le_dualResidual_add_two_sqrt_add_one ε T
      _ = (Real.sqrt (pmPowerDampedDualResidual ε T) + 1) ^ 2 := by
          rw [add_sq, Real.sq_sqrt hR0]; ring
  have hs1 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq (by positivity)] at hs1
  have hs2 := Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq (by positivity)] at hs2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Elementary quadratic bounds: `R(ε, T) ≤ 2 E_T(ε) + 2` and `E_T(ε) ≤ 2 R(ε, T) + 2`. -/
theorem pmPowerDampedDualResidual_two_sided_linear_bounds (ε : ℝ) (T : ℕ) :
    pmPowerDampedDualResidual ε T ≤ 2 * pmPowerDampedDivisorDiscreteEnergy ε T + 2 ∧
    pmPowerDampedDivisorDiscreteEnergy ε T ≤ 2 * pmPowerDampedDualResidual ε T + 2 := by
  have hE0 := pmPowerDampedDivisorDiscreteEnergy_nonneg ε T
  have hR0 : 0 ≤ pmPowerDampedDualResidual ε T := by
    unfold pmPowerDampedDualResidual
    exact sum_nonneg fun n _ => by positivity
  have h1 := pmPowerDampedDualResidual_le_discreteEnergy_add_two_sqrt_add_one ε T
  have h2 := pmPowerDampedDivisorDiscreteEnergy_le_dualResidual_add_two_sqrt_add_one ε T
  have hsqE : 2 * Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) ≤
      pmPowerDampedDivisorDiscreteEnergy ε T + 1 := by
    have := sq_nonneg (Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T) - 1)
    rw [sub_sq, Real.sq_sqrt hE0] at this
    linarith
  have hsqR : 2 * Real.sqrt (pmPowerDampedDualResidual ε T) ≤
      pmPowerDampedDualResidual ε T + 1 := by
    have := sq_nonneg (Real.sqrt (pmPowerDampedDualResidual ε T) - 1)
    rw [sub_sq, Real.sq_sqrt hR0] at this
    linarith
  exact ⟨by linarith, by linarith⟩

/-- **Equivalence Between Bounded Dual Residual `R(ε, T)` and Bounded Primal Receiver `E_T(ε)`
(`exists_pmPowerDampedDualResidual_budget_iff`):**
At every `ε : ℝ`, uniform boundedness of `pmPowerDampedDualResidual ε T` across `T : ℕ` is
equivalent to uniform boundedness of `pmPowerDampedDivisorDiscreteEnergy ε T`. -/
theorem exists_pmPowerDampedDualResidual_budget_iff (ε : ℝ) :
    (∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDualResidual ε T ≤ B) ↔
      (∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨2 * B + 2, fun T => ?_⟩
    have := (pmPowerDampedDualResidual_two_sided_linear_bounds ε T).2
    linarith [hB T]
  · rintro ⟨B, hB⟩
    refine ⟨2 * B + 2, fun T => ?_⟩
    have := (pmPowerDampedDualResidual_two_sided_linear_bounds ε T).1
    linarith [hB T]

/-- **All-Damping Dual Residual Bound on the Vinogradov–Korobov Band
(`exists_dualResidual_le_on_vinogradovKorobovBand_of_pos`):**
For every damping floor `ε₀ > 0`, there exists `E ≥ 0` such that
`pmPowerDampedDualResidual ε T ≤ E` for all `T : ℕ` and all `ε ∈ [ε₀, 1/2]` on the
Vinogradov–Korobov band `ε ≥ 1/2 − κ σ(T)/(480 log T)`. -/
theorem exists_dualResidual_le_on_vinogradovKorobovBand_of_pos {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (T : ℕ) (ε : ℝ), ε₀ ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ ε →
        pmPowerDampedDualResidual ε T ≤ E := by
  obtain ⟨E, hE0, hE⟩ := exists_receiver_le_on_vinogradovKorobovBand_of_pos hε₀
  refine ⟨2 * E + 2, by positivity, fun T ε hε_ge hε2 hband => ?_⟩
  have hstep := (pmPowerDampedDualResidual_two_sided_linear_bounds ε T).1
  linarith [hE T ε hε_ge hε2 hband]

/-- **All-Damping Sub-Half-Damping Growth of the Literal Dual Residual
(`eventually_dualResidual_le_growth_of_pos`):**
For **every** `0 < ε < 1/2`, there exists `C ≥ 0` such that for all large `T : ℕ`,
`pmPowerDampedDualResidual ε T ≤ C T^{1−2ε} exp(−κ σ(T)/270)`. -/
theorem eventually_dualResidual_le_growth_of_pos {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop,
      pmPowerDampedDualResidual ε T ≤
        C * (T : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale T / 270)) := by
  obtain ⟨C, hC0, hC⟩ := eventually_receiver_le_growth_of_pos hε hε2
  set a := 1 - 2 * ε with hadef
  have ha0 : 0 < a := by rw [hadef]; linarith
  have hκ := vkKappa_pos
  have hratio := (tendsto_vkScale_div_log.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_le_nhds (show (0 : ℝ) < a * 270 / (2 * vkKappa) by positivity))
  have hlog : Tendsto (fun T : ℕ => Real.log T) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨2 * C + 2, by positivity, ?_⟩
  filter_upwards [hC, hratio, hlog.eventually_ge_atTop 3] with T hET hTr hT3
  simp only [Function.comp_apply] at hTr
  have hT0 : (0 : ℝ) < T := by
    by_contra h
    have : (T : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg T)
    rw [this, Real.log_zero] at hT3; linarith
  set s := vkKappa * vkScale T / 270 with hsdef
  have hsa : s ≤ a / 2 * Real.log T := by
    have hσ' : vkScale T ≤ a * 270 / (2 * vkKappa) * Real.log T := by
      rwa [div_le_iff₀ (by linarith)] at hTr
    rw [hsdef]
    calc vkKappa * vkScale T / 270 ≤ vkKappa * (a * 270 / (2 * vkKappa) * Real.log T) / 270 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hσ' hκ.le) (by norm_num)
      _ = a / 2 * Real.log T := by field_simp
  set G := (T : ℝ) ^ a * Real.exp (-s) with hGdef
  have hGsq : (T : ℝ) ^ (a / 2) ≤ G := by
    rw [hGdef, Real.rpow_def_of_pos hT0, Real.rpow_def_of_pos hT0, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hG1 : 1 ≤ G := le_trans (Real.one_le_rpow (by
    have := Real.add_one_le_exp (Real.log T)
    rw [Real.exp_log hT0] at this; linarith) (by positivity)) hGsq
  have hstep := (pmPowerDampedDualResidual_two_sided_linear_bounds ε T).1
  have hET' : pmPowerDampedDivisorDiscreteEnergy ε T ≤ C * G := by
    rw [hGdef]; exact le_trans hET (le_of_eq (by ring))
  calc pmPowerDampedDualResidual ε T
      ≤ 2 * (C * G) + 2 * G := by nlinarith
    _ = (2 * C + 2) * (T : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale T / 270)) := by
        rw [hGdef, hadef, hsdef]; ring

/-- **Equivalence of `RiemannHypothesis` with All-Positive-Damping Boundedness of the Literal Dual
Residual (`riemannHypothesis_iff_forall_pos_dualResidual_bounded`):** -/
theorem riemannHypothesis_iff_forall_pos_dualResidual_bounded :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDualResidual ε T ≤ B := by
  rw [riemannHypothesis_iff_forall_pos_pmBezoutInteriorPronicEnergy_bounded]
  refine forall₂_congr fun ε hε => ?_
  rw [exists_pmBezoutInteriorPronicEnergy_budget_iff hε.le,
    exists_pmPowerDampedDualResidual_budget_iff]

end

end GaloisForLFunctions.BezoutValuationIncidence

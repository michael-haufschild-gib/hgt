import GaloisForLFunctions.BezoutValuationIncidence.InteriorMartingaleQuadraticGradientAndRenormalizedDriftBudget
import GaloisForLFunctions.RHTower.PMActivePairLogarithmicDrift
import GaloisForLFunctions.RHTower.RegularizedDivisorHarmonicLimit

/-!
# Compensated Harmonic Asymptotics, Predecessor-Peak Euler Drift, and Universal Divisor-Harmonic Defect Bounds

In `InteriorMartingaleQuadraticGradientAndRenormalizedDriftBudget`, the Route PM discrete energy
`pmPowerDampedDivisorDiscreteEnergy ε T` was decomposed for arbitrary drift parameters `v, κ : ℝ`
against the compensated harmonic sum
$$\operatorname{pmCompensatedHarmonicSum}\,T =
  \sum_{n=1}^{T-1} \left(\frac{1}{n + 1} - \frac{1}{T + 1}\right)$$
into three renormalized brackets:
$$\operatorname{pmPowerDampedDivisorDiscreteEnergy}\,\varepsilon\,T =
  \bigl[\operatorname{pmActiveDeletedCovarianceDiagonal}\,\varepsilon\,T - v\,H_T^{\text{comp}}\bigr] +
  2\,\bigl[\operatorname{pmPredecessorPeakMartingaleSum}\,\varepsilon\,T - \kappa\,H_T^{\text{comp}}\bigr] +
  2\,\bigl[\operatorname{pmBezoutInteriorMartingaleSum}\,\varepsilon\,T + \bigl(\tfrac{1}{2}v + \kappa\bigr)H_T^{\text{comp}}\bigr].$$

In this module, we complete **Step 1** of the Wall 1 Bézout programme by establishing four groups
of 100% unconditional theorems:

1. **Exact Closed Form & Logarithmic Asymptotics of `pmCompensatedHarmonicSum T`
   (`pmCompensatedHarmonicSum_eq_harmonic_sub`,
   `harmonic_sub_pmCompensatedHarmonicSum_bounds`,
   `abs_pmCompensatedHarmonicSum_sub_log_le`,
   `tendsto_pmCompensatedHarmonicSum_div_log`):**
   For every $T \ge 1$:
   $$\operatorname{pmCompensatedHarmonicSum}\,T = (\operatorname{harmonic}\,T : \mathbb{R}) - \frac{2T}{T + 1},$$
   so $0 \le (\operatorname{harmonic}\,T : \mathbb{R}) - \operatorname{pmCompensatedHarmonicSum}\,T \le 2$,
   $\bigl|\operatorname{pmCompensatedHarmonicSum}\,T - \log T\bigr| \le |\gamma| + 3$, and
   $$\lim_{T \to \infty} \frac{\operatorname{pmCompensatedHarmonicSum}\,T}{\log T} = 1.$$

2. **Exact Predecessor-Peak Logarithmic Drift `pmPredecessorPeakLogDrift ε` & Small-Damping Slope
   (`pmPredecessorPeakLogDrift`, `pmPredecessorPeakLogDrift_eq_adjacent`,
   `pmInteriorLogCounterterm_eq_half_shiftedCovariance_add_predecessorPeak`,
   `tendsto_pmPredecessorPeakMartingaleSum_div_log`,
   `tendsto_pmPredecessorPeakLogDrift_div_parameter`):**
   Combining the active-plus-predecessor drift `pmActivePairLogDrift ε` (`PMActivePairLogarithmicDrift`)
   with the active predictable martingale drift `pmActivePredictableMartingaleDrift ε`
   (`ShiftedExponentSmallDampingCovarianceRateAndActiveDrift`) isolates the exact unconditional
   logarithmic drift of `pmPredecessorPeakMartingaleSum ε N` alone for all $\varepsilon > 0$:
   $$\lim_{N \to \infty} \frac{\operatorname{pmPredecessorPeakMartingaleSum}\,\varepsilon\,N}{\log N} =
     \operatorname{pmPredecessorPeakLogDrift}\,\varepsilon :=
     \operatorname{pmActivePairLogDrift}\,\varepsilon - \operatorname{pmActivePredictableMartingaleDrift}\,\varepsilon,$$
   with exact small-damping slope
   $$\lim_{\varepsilon \to 0^+} \frac{\operatorname{pmPredecessorPeakLogDrift}\,\varepsilon}{\varepsilon} =
     \frac{(\operatorname{pmPowerDampedDivisorDensity}\,1).\text{re} - \operatorname{pmAdjacentArtinConstant}}{2},$$
   and exact counterterm reconciliation
   $$\frac{1}{2}\,\operatorname{pmShiftedExponentCovariance}\,\varepsilon +
     \operatorname{pmPredecessorPeakLogDrift}\,\varepsilon =
     \operatorname{pmInteriorLogCounterterm}\,\varepsilon.$$

3. **Canonical Renormalized Energy Decomposition Against `pmCompensatedHarmonicSum`
   (`pmPowerDampedDivisorDiscreteEnergy_eq_canonical_compensated_budget`,
   `tendsto_pmActiveDeletedCovarianceDiagonal_sub_compensated_div_log`,
   `tendsto_pmPredecessorPeakMartingaleSum_sub_compensated_div_log`,
   `tendsto_pmBezoutInterior_compensated_energy_residual`):**
   At the canonical arithmetic rates $v = \operatorname{pmShiftedExponentCovariance}\,\varepsilon$
   and $\kappa = \operatorname{pmPredecessorPeakLogDrift}\,\varepsilon$, the first two brackets are
   unconditionally $o(\log T)$ for every $\varepsilon > 0$, so the compensated-harmonic interior
   counterterm bracket tracks $\frac{1}{2}\operatorname{pmPowerDampedDivisorDiscreteEnergy}\,\varepsilon\,T$
   to within $o(\log T)$.

4. **Universal Uniform $O(1)$ Divisor-Harmonic Defect Bounds via `RegularizedDivisorHarmonic`
   (`regError_le_const_mul_tsum_logWeight`,
   `abs_divisorHarmonic_sub_coeffDensity_mul_log_le`,
   `abs_divisorHarmonic_sub_coeffDensity_mul_compensated_le`):**
   For any arithmetic coefficient sequence $a : \mathbb{N} \to \mathbb{R}$ with
   `Summable (RegularizedDivisorHarmonic.logWeight a)`, the regularization error `regError a N` is
   uniformly bounded for **all** $N \ge 1$ by $(6 + |\gamma|)\sum_{d=0}^\infty \operatorname{logWeight}\,a\,d$,
   giving an explicit finite uniform bound on both
   $\bigl|\sum_{k=1}^N \frac{\sum_{d \mid k} a(d)}{k} - \operatorname{coeffDensity}(a)\,\log N\bigr|$
   and $\bigl|\sum_{k=1}^N \frac{\sum_{d \mid k} a(d)}{k} - \operatorname{coeffDensity}(a)\,H_N^{\text{comp}}\bigr|$
   across all $N \ge 1$.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Closed Form & Logarithmic Asymptotics of `pmCompensatedHarmonicSum T` -/

/-- **Closed-Form Identity for `pmCompensatedHarmonicSum T`
(`pmCompensatedHarmonicSum_eq_harmonic_sub`):**
For every `T ≥ 1`:
`pmCompensatedHarmonicSum T = (harmonic T : ℝ) - 2 * T / (T + 1)`. -/
theorem pmCompensatedHarmonicSum_eq_harmonic_sub {T : ℕ} (hT : 1 ≤ T) :
    pmCompensatedHarmonicSum T = (harmonic T : ℝ) - 2 * (T : ℝ) / ((T : ℝ) + 1) := by
  unfold pmCompensatedHarmonicSum
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc,
    Nat.sub_add_cancel hT, nsmul_eq_mul]
  have hshift :
      (∑ n ∈ Finset.Icc 1 (T - 1), (1 / ((n : ℝ) + 1))) = (harmonic T : ℝ) - 1 := by
    have hsplit := sum_Icc_one_split_head_and_shift (fun m : ℕ => ((m : ℝ))⁻¹) hT
    rw [ ← RegularizedDivisorHarmonic.harmonic_cast_eq_sum T] at hsplit
    have hcongr :
        (∑ n ∈ Finset.Icc 1 (T - 1), (1 / ((n : ℝ) + 1))) =
          ∑ k ∈ Finset.Icc 1 (T - 1), (((k + 1 : ℕ) : ℝ))⁻¹ := by
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    rw [hcongr]
    linarith [show (((1 : ℕ) : ℝ))⁻¹ = (1 : ℝ) by norm_num]
  rw [hshift]
  have hTpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  push_cast [Nat.cast_sub hT]
  field_simp [hTpos.ne']
  ring

/-- **Uniform Two-Sided Sandwich Between `harmonic T` and `pmCompensatedHarmonicSum T`
(`harmonic_sub_pmCompensatedHarmonicSum_bounds`):**
For every `T : ℕ`, `0 ≤ (harmonic T : ℝ) - pmCompensatedHarmonicSum T` and
`(harmonic T : ℝ) - pmCompensatedHarmonicSum T ≤ 2`. -/
theorem harmonic_sub_pmCompensatedHarmonicSum_bounds (T : ℕ) :
    0 ≤ (harmonic T : ℝ) - pmCompensatedHarmonicSum T ∧
      (harmonic T : ℝ) - pmCompensatedHarmonicSum T ≤ 2 := by
  by_cases hT : 1 ≤ T
  · rw [pmCompensatedHarmonicSum_eq_harmonic_sub hT]
    have hTpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    have hnonneg : 0 ≤ 2 * (T : ℝ) / ((T : ℝ) + 1) := by positivity
    have hle : 2 * (T : ℝ) / ((T : ℝ) + 1) ≤ 2 := by
      rw [div_le_iff₀ hTpos]
      linarith
    exact ⟨by linarith, by linarith⟩
  · have hT0 : T = 0 := by omega
    subst hT0
    unfold pmCompensatedHarmonicSum
    simp

/-- **Uniform Boundedness of `|pmCompensatedHarmonicSum T - log T|`
(`abs_pmCompensatedHarmonicSum_sub_log_le`):**
For every `T ≥ 1`:
`|pmCompensatedHarmonicSum T - Real.log T| ≤ |Real.eulerMascheroniConstant| + 3`. -/
theorem abs_pmCompensatedHarmonicSum_sub_log_le {T : ℕ} (hT : 1 ≤ T) :
    |pmCompensatedHarmonicSum T - Real.log T| ≤ |Real.eulerMascheroniConstant| + 3 := by
  have hharm := HTGeometry.abs_harmonic_sub_log_sub_eulerMascheroni_le hT
  have h1T : (1 : ℝ) / (T : ℝ) ≤ 1 := by
    have hTR : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    exact div_le_self zero_le_one hTR
  have hcomp := harmonic_sub_pmCompensatedHarmonicSum_bounds T
  have hsplit :
      pmCompensatedHarmonicSum T - Real.log T =
        ((harmonic T : ℝ) - Real.log T - Real.eulerMascheroniConstant) +
          Real.eulerMascheroniConstant -
          ((harmonic T : ℝ) - pmCompensatedHarmonicSum T) := by
    ring
  rw [hsplit]
  have habs1 := abs_sub
    (((harmonic T : ℝ) - Real.log T - Real.eulerMascheroniConstant) +
      Real.eulerMascheroniConstant)
    ((harmonic T : ℝ) - pmCompensatedHarmonicSum T)
  have habs2 := abs_add_le
    ((harmonic T : ℝ) - Real.log T - Real.eulerMascheroniConstant)
    Real.eulerMascheroniConstant
  have habs3 : |(harmonic T : ℝ) - pmCompensatedHarmonicSum T| ≤ 2 := by
    rw [abs_of_nonneg hcomp.1]
    exact hcomp.2
  linarith

/-- **Unit Logarithmic Limit of `pmCompensatedHarmonicSum T`
(`tendsto_pmCompensatedHarmonicSum_div_log`):**
As `T → ∞`, `pmCompensatedHarmonicSum T / log T → 1`. -/
theorem tendsto_pmCompensatedHarmonicSum_div_log :
    Tendsto (fun T : ℕ => pmCompensatedHarmonicSum T / Real.log T) atTop (𝓝 1) := by
  have hlog : Tendsto (fun T : ℕ => Real.log T) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdiff : Tendsto (fun T : ℕ => (pmCompensatedHarmonicSum T - Real.log T) / Real.log T)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_
      ((tendsto_const_nhds (x := |Real.eulerMascheroniConstant| + 3)).div_atTop hlog)
    filter_upwards [eventually_ge_atTop 2] with T hT
    have hlog0 : 0 < Real.log T := Real.log_pos (by exact_mod_cast hT)
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlog0]
    exact div_le_div_of_nonneg_right
      (abs_pmCompensatedHarmonicSum_sub_log_le (by omega)) hlog0.le
  have hmain := (tendsto_const_nhds (x := (1 : ℝ))).add hdiff
  simpa only [add_zero] using hmain.congr' (by
    filter_upwards [eventually_ge_atTop 2] with T hT
    have hlog0 : Real.log T ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hT))
    field_simp [hlog0]
    ring)

/-! ## §2. Exact Predecessor-Peak Logarithmic Drift `pmPredecessorPeakLogDrift ε` & Small-Damping Slope -/

/-- The exact asymptotic logarithmic drift rate of `pmPredecessorPeakMartingaleSum ε N` alone:
`pmPredecessorPeakLogDrift ε = pmActivePairLogDrift ε - pmActivePredictableMartingaleDrift ε`. -/
def pmPredecessorPeakLogDrift (ε : ℝ) : ℝ :=
  pmActivePairLogDrift ε - pmActivePredictableMartingaleDrift ε

/-- **Adjacent-Density Formula for `pmPredecessorPeakLogDrift ε`
(`pmPredecessorPeakLogDrift_eq_adjacent`):**
For every `ε : ℝ`, `pmPredecessorPeakLogDrift ε` is given explicitly in terms of the adjacent
divisor densities `pmAdjacentDivisorDensity` and single divisor densities by:
`(pmAdjacentDivisorDensity ε ε - pmAdjacentDivisorDensity ε (1 + ε) + (pmPowerDampedDivisorDensity ε).re * ((pmPowerDampedDivisorDensity (1 + ε)).re - (pmPowerDampedDivisorDensity ε).re)) / 2`. -/
theorem pmPredecessorPeakLogDrift_eq_adjacent (ε : ℝ) :
    pmPredecessorPeakLogDrift ε =
      (pmAdjacentDivisorDensity ε ε - pmAdjacentDivisorDensity ε (1 + ε) +
        (pmPowerDampedDivisorDensity ε).re *
          ((pmPowerDampedDivisorDensity (1 + ε)).re -
            (pmPowerDampedDivisorDensity ε).re)) / 2 := by
  unfold pmPredecessorPeakLogDrift pmActivePairLogDrift pmActivePredictableMartingaleDrift
    pmShiftedExponentCovariance pmPowerDampedDivisorVariance
  ring

/-- **Additive Decomposition of `pmActivePairLogDrift ε`
(`pmActivePairLogDrift_eq_active_add_predecessorPeak`):**
For every `ε : ℝ`:
`pmActivePairLogDrift ε = pmActivePredictableMartingaleDrift ε + pmPredecessorPeakLogDrift ε`. -/
theorem pmActivePairLogDrift_eq_active_add_predecessorPeak (ε : ℝ) :
    pmActivePairLogDrift ε =
      pmActivePredictableMartingaleDrift ε + pmPredecessorPeakLogDrift ε := by
  unfold pmPredecessorPeakLogDrift
  ring

/-- **Exact Reconciliation of `pmInteriorLogCounterterm` with `pmShiftedExponentCovariance` and `pmPredecessorPeakLogDrift`
(`pmInteriorLogCounterterm_eq_half_shiftedCovariance_add_predecessorPeak`):**
Whether one groups the energy into `(diagonal, active + predecessor-peak, interior)` or into
`(active-deleted diagonal, predecessor-peak, interior)`, the resulting interior counterterm rate is identical:
`pmShiftedExponentCovariance ε / 2 + pmPredecessorPeakLogDrift ε = pmInteriorLogCounterterm ε`. -/
theorem pmInteriorLogCounterterm_eq_half_shiftedCovariance_add_predecessorPeak (ε : ℝ) :
    pmShiftedExponentCovariance ε / 2 + pmPredecessorPeakLogDrift ε =
      pmInteriorLogCounterterm ε := by
  unfold pmInteriorLogCounterterm pmPredecessorPeakLogDrift pmActivePredictableMartingaleDrift
  ring

/-- **Unconditional Logarithmic Drift of `pmPredecessorPeakMartingaleSum ε N` for All `ε > 0`
(`tendsto_pmPredecessorPeakMartingaleSum_div_log`):**
For **every** `ε > 0` (without any `MemLp` hypothesis),
`pmPredecessorPeakMartingaleSum ε N / log N → pmPredecessorPeakLogDrift ε` as `N → ∞`. -/
theorem tendsto_pmPredecessorPeakMartingaleSum_div_log {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => pmPredecessorPeakMartingaleSum ε N / Real.log N)
      atTop (𝓝 (pmPredecessorPeakLogDrift ε)) := by
  have h := (tendsto_pmActivePair_div_log hε).sub
    (tendsto_pmActivePredictableMartingaleSum_div_log hε)
  have hl : Tendsto (fun N : ℕ =>
      (pmActivePredictableMartingaleSum ε N + pmPredecessorPeakMartingaleSum ε N) /
        Real.log N -
      pmActivePredictableMartingaleSum ε N / Real.log N)
      atTop (𝓝 (pmPredecessorPeakLogDrift ε)) := by
    simpa [pmPredecessorPeakLogDrift, Pi.sub_def] using h
  refine hl.congr fun N => ?_
  ring

/-- **Exact Small-Damping Slope of `pmPredecessorPeakLogDrift ε` (`ε → 0⁺`)
(`tendsto_pmPredecessorPeakLogDrift_div_parameter`):**
As `ε → 0⁺`, `pmPredecessorPeakLogDrift ε / ε` converges to
`((pmPowerDampedDivisorDensity 1).re - pmAdjacentArtinConstant) / 2`. -/
theorem tendsto_pmPredecessorPeakLogDrift_div_parameter :
    Tendsto (fun ε : ℝ => pmPredecessorPeakLogDrift ε / ε) (𝓝[>] 0)
      (𝓝 (((pmPowerDampedDivisorDensity 1).re - pmAdjacentArtinConstant) / 2)) := by
  have h := tendsto_pmActivePairLogDrift_div_parameter.sub
    tendsto_pmActivePredictableMartingaleDrift_div_parameter
  have hl : Tendsto (fun ε : ℝ =>
      pmActivePairLogDrift ε / ε - pmActivePredictableMartingaleDrift ε / ε) (𝓝[>] 0)
      (𝓝 ((1 / 4 - pmAdjacentArtinConstant / 2) -
        (1 / 4 - (pmPowerDampedDivisorDensity 1).re / 2))) := by
    simpa [Pi.sub_def] using h
  have heq :
      (1 / 4 - pmAdjacentArtinConstant / 2) -
        (1 / 4 - (pmPowerDampedDivisorDensity 1).re / 2) =
      ((pmPowerDampedDivisorDensity 1).re - pmAdjacentArtinConstant) / 2 := by
    ring
  rw [heq] at hl
  refine hl.congr fun ε => ?_
  dsimp only [pmPredecessorPeakLogDrift]
  ring

/-! ## §3. Canonical Renormalized Energy Decomposition Against `pmCompensatedHarmonicSum` -/

/-- **Canonical Arithmetic Renormalized Energy Identity Against `pmCompensatedHarmonicSum`
(`pmPowerDampedDivisorDiscreteEnergy_eq_canonical_compensated_budget`):**
For every `ε : ℝ` and `T : ℕ`:
`pmPowerDampedDivisorDiscreteEnergy ε T` equals the sum of:
1. `pmActiveDeletedCovarianceDiagonal ε T - pmShiftedExponentCovariance ε * pmCompensatedHarmonicSum T`,
2. `2 * (pmPredecessorPeakMartingaleSum ε T - pmPredecessorPeakLogDrift ε * pmCompensatedHarmonicSum T)`,
3. `2 * (pmBezoutInteriorMartingaleSum ε T + pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T)`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_eq_canonical_compensated_budget
    (ε : ℝ) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε T =
      (pmActiveDeletedCovarianceDiagonal ε T -
        pmShiftedExponentCovariance ε * pmCompensatedHarmonicSum T) +
      2 * (pmPredecessorPeakMartingaleSum ε T -
        pmPredecessorPeakLogDrift ε * pmCompensatedHarmonicSum T) +
      2 * (pmBezoutInteriorMartingaleSum ε T +
        pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T) := by
  have h := pmPowerDampedDivisorDiscreteEnergy_renormalized_budget_eq ε T
    (pmShiftedExponentCovariance ε) (pmPredecessorPeakLogDrift ε)
  rw [pmInteriorLogCounterterm_eq_half_shiftedCovariance_add_predecessorPeak] at h
  exact h

/-- **Unconditional `o(log T)` Vanishing of the Renormalized Active-Deleted Diagonal Bracket
(`tendsto_pmActiveDeletedCovarianceDiagonal_sub_compensated_div_log`):**
For every `ε > 0`:
`(pmActiveDeletedCovarianceDiagonal ε T - pmShiftedExponentCovariance ε * pmCompensatedHarmonicSum T) / log T → 0`. -/
theorem tendsto_pmActiveDeletedCovarianceDiagonal_sub_compensated_div_log
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T : ℕ =>
      (pmActiveDeletedCovarianceDiagonal ε T -
        pmShiftedExponentCovariance ε * pmCompensatedHarmonicSum T) / Real.log T)
      atTop (𝓝 0) := by
  have h := (tendsto_pmActiveDeletedCovarianceDiagonal_div_log hε).sub
    (tendsto_pmCompensatedHarmonicSum_div_log.const_mul (pmShiftedExponentCovariance ε))
  simpa only [mul_one, sub_self] using h.congr (fun T => by ring)

/-- **Unconditional `o(log T)` Vanishing of the Renormalized Predecessor-Peak Bracket
(`tendsto_pmPredecessorPeakMartingaleSum_sub_compensated_div_log`):**
For every `ε > 0`:
`(pmPredecessorPeakMartingaleSum ε T - pmPredecessorPeakLogDrift ε * pmCompensatedHarmonicSum T) / log T → 0`. -/
theorem tendsto_pmPredecessorPeakMartingaleSum_sub_compensated_div_log
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T : ℕ =>
      (pmPredecessorPeakMartingaleSum ε T -
        pmPredecessorPeakLogDrift ε * pmCompensatedHarmonicSum T) / Real.log T)
      atTop (𝓝 0) := by
  have h := (tendsto_pmPredecessorPeakMartingaleSum_div_log hε).sub
    (tendsto_pmCompensatedHarmonicSum_div_log.const_mul (pmPredecessorPeakLogDrift ε))
  simpa only [mul_one, sub_self] using h.congr (fun T => by ring)

/-- **Unconditional `o(log T)` Equivalence of the Compensated Interior Counterterm Bracket and Half the Discrete Energy
(`tendsto_pmBezoutInterior_compensated_energy_residual`):**
For every `ε > 0` (without any `MemLp` hypothesis):
`(pmBezoutInteriorMartingaleSum ε T + pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T - pmPowerDampedDivisorDiscreteEnergy ε T / 2) / log T → 0`. -/
theorem tendsto_pmBezoutInterior_compensated_energy_residual {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T : ℕ =>
      (pmBezoutInteriorMartingaleSum ε T +
        pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T -
        pmPowerDampedDivisorDiscreteEnergy ε T / 2) / Real.log T)
      atTop (𝓝 0) := by
  have h1 := (tendsto_pmActiveDeletedCovarianceDiagonal_sub_compensated_div_log hε).div_const
    (2 : ℝ)
  have h2 := tendsto_pmPredecessorPeakMartingaleSum_sub_compensated_div_log hε
  have h := (h1.add h2).neg
  have hz : (-(0 / 2 + 0) : ℝ) = 0 := by ring
  rw [hz] at h
  refine h.congr fun T => ?_
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_canonical_compensated_budget ε T]
  ring

/-! ## §4. Universal Uniform `O(1)` Divisor-Harmonic Defect Bounds via `RegularizedDivisorHarmonic` -/

/-- For every `a : ℕ → ℝ` with `Summable (RegularizedDivisorHarmonic.logWeight a)` and every `N ≥ 1`,
`RegularizedDivisorHarmonic.regError a N` is bounded uniformly by
`(6 + |Real.eulerMascheroniConstant|) * ∑' d : ℕ, RegularizedDivisorHarmonic.logWeight a d`. -/
theorem regError_le_const_mul_tsum_logWeight {a : ℕ → ℝ}
    (h1 : Summable (RegularizedDivisorHarmonic.logWeight a)) {N : ℕ} (hN : 1 ≤ N) :
    RegularizedDivisorHarmonic.regError a N ≤
      (6 + |Real.eulerMascheroniConstant|) *
        ∑' d : ℕ, RegularizedDivisorHarmonic.logWeight a d := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hhead_le :
      (∑ d ∈ Finset.Icc 1 N, |a d|) / (N : ℝ) ≤
        ∑' d : ℕ, RegularizedDivisorHarmonic.logWeight a d := by
    rw [Finset.sum_div]
    calc
      (∑ d ∈ Finset.Icc 1 N, |a d| / (N : ℝ))
        ≤ ∑ d ∈ Finset.Icc 1 N, RegularizedDivisorHarmonic.logWeight a d := by
          refine Finset.sum_le_sum fun d hd => ?_
          obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
          have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
          have hdNR : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdN
          have hlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1)
          calc
            |a d| / (N : ℝ) ≤ |a d| / (d : ℝ) :=
              div_le_div_of_nonneg_left (abs_nonneg _) hdpos hdNR
            _ ≤ |a d| * (1 + Real.log d) / (d : ℝ) := by
              rw [div_le_div_iff_of_pos_right hdpos]
              nlinarith [abs_nonneg (a d)]
            _ = RegularizedDivisorHarmonic.logWeight a d := rfl
      _ ≤ ∑' d : ℕ, RegularizedDivisorHarmonic.logWeight a d :=
        h1.sum_le_tsum (Finset.Icc 1 N)
          (fun d _ => RegularizedDivisorHarmonic.logWeight_nonneg a d)
  have htail_le :
      (∑' i : ℕ, RegularizedDivisorHarmonic.logWeight a (i + (N + 1))) ≤
        ∑' d : ℕ, RegularizedDivisorHarmonic.logWeight a d := by
    rw [← h1.sum_add_tsum_nat_add (N + 1)]
    have hsum_nonneg :
        0 ≤ ∑ i ∈ Finset.range (N + 1), RegularizedDivisorHarmonic.logWeight a i :=
      Finset.sum_nonneg fun i _ => RegularizedDivisorHarmonic.logWeight_nonneg a i
    linarith
  unfold RegularizedDivisorHarmonic.regError
  have htsum_nonneg : 0 ≤ ∑' d : ℕ, RegularizedDivisorHarmonic.logWeight a d :=
    tsum_nonneg (RegularizedDivisorHarmonic.logWeight_nonneg a)
  have h4 : 4 * (∑ d ∈ Finset.Icc 1 N, |a d|) / (N : ℝ) =
      4 * ((∑ d ∈ Finset.Icc 1 N, |a d|) / (N : ℝ)) := by ring
  rw [h4]
  nlinarith [abs_nonneg Real.eulerMascheroniConstant]

/-- **Universal Uniform `O(1)` Divisor-Harmonic Defect Bound Against `Real.log N`
(`abs_divisorHarmonic_sub_coeffDensity_mul_log_le`):**
For any `a : ℕ → ℝ` with `Summable (RegularizedDivisorHarmonic.logWeight a)` and every `N ≥ 1`:
`|(∑ k ∈ Icc 1 N, (∑ d ∈ k.divisors, a d) / k) - coeffDensity a * Real.log N|` is bounded by the
`N`-independent constant
`|coeffDensity a * eulerMascheroniConstant - coeffLogMass a| + (6 + |eulerMascheroniConstant|) * ∑' d, logWeight a d`. -/
theorem abs_divisorHarmonic_sub_coeffDensity_mul_log_le {a : ℕ → ℝ}
    (h1 : Summable (RegularizedDivisorHarmonic.logWeight a)) {N : ℕ} (hN : 1 ≤ N) :
    |(∑ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, a d) / (k : ℝ)) -
      RegularizedDivisorHarmonic.coeffDensity a * Real.log N| ≤
      |RegularizedDivisorHarmonic.coeffDensity a * Real.eulerMascheroniConstant -
        RegularizedDivisorHarmonic.coeffLogMass a| +
      (6 + |Real.eulerMascheroniConstant|) *
        ∑' d : ℕ, RegularizedDivisorHarmonic.logWeight a d := by
  have hdef := RegularizedDivisorHarmonic.abs_regDefect_le h1 hN
  rw [RegularizedDivisorHarmonic.tsum_modelSummand h1 N] at hdef
  have hreg := regError_le_const_mul_tsum_logWeight h1 hN
  have hsplit :
      (∑ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, a d) / (k : ℝ)) -
        RegularizedDivisorHarmonic.coeffDensity a * Real.log N =
      ((∑ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, a d) / (k : ℝ)) -
        (RegularizedDivisorHarmonic.coeffDensity a *
          (Real.log N + Real.eulerMascheroniConstant) -
          RegularizedDivisorHarmonic.coeffLogMass a)) +
      (RegularizedDivisorHarmonic.coeffDensity a * Real.eulerMascheroniConstant -
        RegularizedDivisorHarmonic.coeffLogMass a) := by
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (by linarith)

/-- **Universal Uniform `O(1)` Divisor-Harmonic Defect Bound Against `pmCompensatedHarmonicSum N`
(`abs_divisorHarmonic_sub_coeffDensity_mul_compensated_le`):**
For any `a : ℕ → ℝ` with `Summable (RegularizedDivisorHarmonic.logWeight a)` and every `N ≥ 1`:
`|(∑ k ∈ Icc 1 N, (∑ d ∈ k.divisors, a d) / k) - coeffDensity a * pmCompensatedHarmonicSum N|`
is bounded uniformly in `N` by an explicit finite constant depending only on `a`. -/
theorem abs_divisorHarmonic_sub_coeffDensity_mul_compensated_le {a : ℕ → ℝ}
    (h1 : Summable (RegularizedDivisorHarmonic.logWeight a)) {N : ℕ} (hN : 1 ≤ N) :
    |(∑ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, a d) / (k : ℝ)) -
      RegularizedDivisorHarmonic.coeffDensity a * pmCompensatedHarmonicSum N| ≤
      |RegularizedDivisorHarmonic.coeffDensity a * Real.eulerMascheroniConstant -
        RegularizedDivisorHarmonic.coeffLogMass a| +
      (6 + |Real.eulerMascheroniConstant|) *
        ∑' d : ℕ, RegularizedDivisorHarmonic.logWeight a d +
      |RegularizedDivisorHarmonic.coeffDensity a| *
        (|Real.eulerMascheroniConstant| + 3) := by
  have hlog := abs_divisorHarmonic_sub_coeffDensity_mul_log_le h1 hN
  have hcomp := abs_pmCompensatedHarmonicSum_sub_log_le hN
  have hsplit :
      (∑ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, a d) / (k : ℝ)) -
        RegularizedDivisorHarmonic.coeffDensity a * pmCompensatedHarmonicSum N =
      ((∑ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, a d) / (k : ℝ)) -
        RegularizedDivisorHarmonic.coeffDensity a * Real.log N) -
      RegularizedDivisorHarmonic.coeffDensity a *
        (pmCompensatedHarmonicSum N - Real.log N) := by
    ring
  rw [hsplit]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul]
  have hmul :
      |RegularizedDivisorHarmonic.coeffDensity a| *
        |pmCompensatedHarmonicSum N - Real.log N| ≤
      |RegularizedDivisorHarmonic.coeffDensity a| *
        (|Real.eulerMascheroniConstant| + 3) :=
    mul_le_mul_of_nonneg_left hcomp (abs_nonneg _)
  linarith

end
end GaloisForLFunctions.BezoutValuationIncidence

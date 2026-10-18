import GaloisForLFunctions.BezoutValuationIncidence.HorizonFreeActiveDeletedEnergyAndShiftedCovariance

/-!
# Pillar XXII: Unconditional Active Martingale Logarithmic Drift & Small-Damping Rate of `pmShiftedExponentCovariance` (`ε → 0⁺`)

In Pillar XXI (`HorizonFreeActiveDeletedEnergyAndShiftedCovariance`), we decomposed the horizon-free
Route PM discrete energy and predictable martingale sum into their active pre-jump and inactive
residual components:
$$\operatorname{pmPredictableMartingaleSum}\,\varepsilon\,T =
  \operatorname{pmActivePredictableMartingaleSum}\,\varepsilon\,T +
  \operatorname{pmInactivePredictableMartingaleSum}\,\varepsilon\,T,$$
$$\operatorname{pmActiveDeletedCovarianceDiagonal}\,\varepsilon\,T =
  \operatorname{pmPowerDampedDivisorCovarianceDiagonal}\,\varepsilon\,T +
  2\,\operatorname{pmActivePredictableMartingaleSum}\,\varepsilon\,T.$$

In this twenty-second pillar of **Bézout–Valuation Incidence Mechanics**, we exploit this exact
identity to prove two foundational analytic laws:
1. Whereas the total predictable martingale sum `pmPredictableMartingaleSum ε N / log N` requires
   `pmPowerDampedFermiSource ε ∈ L²((0, ∞))` to control its logarithmic limit, the **active
   predictable martingale sum** `pmActivePredictableMartingaleSum ε N / log N` converges
   **unconditionally for ALL `ε > 0`** (including `0 < ε < 1/2`!) to
   $$\operatorname{pmActivePredictableMartingaleDrift}\,\varepsilon :=
     \frac{\operatorname{pmShiftedExponentCovariance}\,\varepsilon -
       \operatorname{pmPowerDampedDivisorVariance}\,\varepsilon}{2}.$$
2. As $\varepsilon \to 0^+$, `pmShiftedExponentCovariance ε / ε` converges to the strictly positive
   constant $1 - (\operatorname{pmPowerDampedDivisorDensity}\,1).\text{re} = 1 - 1/\zeta(2) \ge 1/4 > 0$,
   fixing the exact small-damping rates of both the active-deleted covariance diagonal and the
   active/inactive predictable martingale drifts.

## Core Main Theorems (100% Unconditional)

1. **Unconditional Logarithmic Drift of `pmActivePredictableMartingaleSum` for All `ε > 0`
   (`tendsto_pmActivePredictableMartingaleSum_div_log`,
   `tendsto_pmPredictableMartingaleSum_sub_inactive_div_log`)**:
   For **every** $\varepsilon > 0$ (with no `MemLp` hypothesis):
   $$\lim_{N \to \infty} \frac{\operatorname{pmActivePredictableMartingaleSum}\,\varepsilon\,N}{\log N} =
     \frac{\operatorname{pmShiftedExponentCovariance}\,\varepsilon -
       \operatorname{pmPowerDampedDivisorVariance}\,\varepsilon}{2}.$$

2. **Euler Factor Bound at `σ = 1` & Exact Small-Damping Rate of `pmShiftedExponentCovariance`
   (`pmPowerDampedDivisorDensity_one_re_le_three_quarters`,
   `one_quarter_le_one_sub_pmPowerDampedDivisorDensity_one_re`,
   `tendsto_pmPowerDampedDivisorDensity_add_one_re`,
   `tendsto_pmShiftedExponentCovariance_div_parameter`)**:
   At $\sigma = 1$, $0 < (\operatorname{pmPowerDampedDivisorDensity}\,1).\text{re} \le 3/4$, so
   $1 - (\operatorname{pmPowerDampedDivisorDensity}\,1).\text{re} \ge 1/4 > 0$, and as $\varepsilon \to 0^+$:
   $$\lim_{\varepsilon \to 0^+} \frac{\operatorname{pmShiftedExponentCovariance}\,\varepsilon}{\varepsilon} =
     1 - (\operatorname{pmPowerDampedDivisorDensity}\,1).\text{re}.$$

3. **Small-Damping Rates of Active & Inactive Predictable Martingale Drifts
   (`tendsto_pmActivePredictableMartingaleDrift_div_parameter`,
   `tendsto_neg_half_pmShiftedExponentCovariance_div_parameter`)**:
   As $\varepsilon \to 0^+$:
   $$\lim_{\varepsilon \to 0^+} \frac{\operatorname{pmActivePredictableMartingaleDrift}\,\varepsilon}{\varepsilon} =
     \frac{1}{4} - \frac{(\operatorname{pmPowerDampedDivisorDensity}\,1).\text{re}}{2},$$
   $$\lim_{\varepsilon \to 0^+} \frac{-\operatorname{pmShiftedExponentCovariance}\,\varepsilon / 2}{\varepsilon} =
     -\frac{1 - (\operatorname{pmPowerDampedDivisorDensity}\,1).\text{re}}{2}.$$
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Unconditional Logarithmic Drift of `pmActivePredictableMartingaleSum` for All `ε > 0` -/

/-- The asymptotic logarithmic drift rate of `pmActivePredictableMartingaleSum ε N`:
`pmActivePredictableMartingaleDrift ε = (pmShiftedExponentCovariance ε - pmPowerDampedDivisorVariance ε) / 2`. -/
def pmActivePredictableMartingaleDrift (ε : ℝ) : ℝ :=
  (pmShiftedExponentCovariance ε - pmPowerDampedDivisorVariance ε) / 2

/-- Pointwise identity expressing `pmActivePredictableMartingaleSum ε T` as half the difference
between `pmActiveDeletedCovarianceDiagonal ε T` and `pmPowerDampedDivisorCovarianceDiagonal ε T`. -/
theorem pmActivePredictableMartingaleSum_eq_half_sub_diagonal (ε : ℝ) (T : ℕ) :
    pmActivePredictableMartingaleSum ε T =
      (pmActiveDeletedCovarianceDiagonal ε T -
        pmPowerDampedDivisorCovarianceDiagonal ε T) / 2 := by
  have h := pmActiveDeletedCovarianceDiagonal_eq_diagonal_add_two_mul_active ε T
  linarith

/-- **Unconditional Logarithmic Drift of `pmActivePredictableMartingaleSum` for All `ε > 0`
(`tendsto_pmActivePredictableMartingaleSum_div_log`):**
For **every** `ε > 0` (without any `MemLp` hypothesis or `ε ≥ 1/2` restriction),
`pmActivePredictableMartingaleSum ε N / log N` converges as `N → ∞` to
`pmActivePredictableMartingaleDrift ε`. -/
theorem tendsto_pmActivePredictableMartingaleSum_div_log {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => pmActivePredictableMartingaleSum ε N / Real.log N)
      atTop (𝓝 (pmActivePredictableMartingaleDrift ε)) := by
  have h := ((tendsto_pmActiveDeletedCovarianceDiagonal_div_log hε).sub
    (tendsto_pmPowerDampedDivisorCovarianceDiagonal_div_log hε)).div_const (2 : ℝ)
  have hl : Tendsto (fun N : ℕ =>
      (pmActiveDeletedCovarianceDiagonal ε N / Real.log N -
        pmPowerDampedDivisorCovarianceDiagonal ε N / Real.log N) / 2)
      atTop (𝓝 (pmActivePredictableMartingaleDrift ε)) := by
    simpa [pmActivePredictableMartingaleDrift, Pi.sub_def] using h
  refine hl.congr fun N => ?_
  rw [pmActivePredictableMartingaleSum_eq_half_sub_diagonal]
  ring

/-- **Unconditional Logarithmic Drift of `pmPredictableMartingaleSum - pmInactivePredictableMartingaleSum`
(`tendsto_pmPredictableMartingaleSum_sub_inactive_div_log`):**
For every `ε > 0`, the difference between the full and inactive predictable martingale sums divided
by `log N` converges unconditionally to `pmActivePredictableMartingaleDrift ε`. -/
theorem tendsto_pmPredictableMartingaleSum_sub_inactive_div_log {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ =>
      (pmPredictableMartingaleSum ε N - pmInactivePredictableMartingaleSum ε N) / Real.log N)
      atTop (𝓝 (pmActivePredictableMartingaleDrift ε)) := by
  refine (tendsto_pmActivePredictableMartingaleSum_div_log hε).congr fun N => ?_
  rw [pmPredictableMartingaleSum_eq_active_add_inactive]
  ring

/-! ## §2. Euler Factor Bound at `σ = 1` & Exact Small-Damping Rate of `pmShiftedExponentCovariance` -/

/-- **Two-Adic Euler Upper Bound on `(pmPowerDampedDivisorDensity 1).re`
(`pmPowerDampedDivisorDensity_one_re_le_three_quarters`):**
At exponent `1`, `0 < (pmPowerDampedDivisorDensity 1).re` and
`(pmPowerDampedDivisorDensity 1).re ≤ 3 / 4` (from the `p = 2` Euler factor `1 - 1 / 2² = 3 / 4`). -/
theorem pmPowerDampedDivisorDensity_one_re_le_three_quarters :
    0 < (pmPowerDampedDivisorDensity 1).re ∧
      (pmPowerDampedDivisorDensity 1).re ≤ 3 / 4 := by
  refine ⟨pmPowerDampedDivisorDensity_re_pos (by norm_num), ?_⟩
  let f : Nat.Primes → ℝ := fun p => 1 - (p : ℝ) ^ (-(1 : ℝ)) / (p : ℝ)
  have hf0 : ∀ p : Nat.Primes, 0 ≤ f p := by
    intro p
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_le
    have hp0 : (0 : ℝ) < p := by linarith
    have ht1 : (p : ℝ) ^ (-(1 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hp1 (by norm_num)
    exact sub_nonneg.mpr ((div_le_one hp0).mpr (by linarith))
  have hf1 : ∀ p : Nat.Primes, f p ≤ 1 := by
    intro p
    have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
    have hdiv : 0 ≤ (p : ℝ) ^ (-(1 : ℝ)) / (p : ℝ) :=
      div_nonneg (Real.rpow_nonneg hp0.le _) hp0.le
    linarith
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hp2_val : f p2 = 3 / 4 := by
    dsimp only [f, p2]
    rw [Real.rpow_neg_one]
    norm_num
  apply le_of_tendsto (pmPowerDampedDivisorDensity_hasProd_real (by norm_num : (0 : ℝ) < 1))
  refine eventually_atTop.2 ⟨{p2}, fun S hS => ?_⟩
  have hp2_mem : p2 ∈ S := hS (Finset.mem_singleton_self p2)
  rw [← Finset.mul_prod_erase S f hp2_mem, hp2_val]
  have hrest : (∏ p ∈ S.erase p2, f p) ≤ 1 :=
    Finset.prod_le_one (fun p _ => hf0 p) (fun p _ => hf1 p)
  linarith

/-- Consequently, `1 / 4 ≤ 1 - (pmPowerDampedDivisorDensity 1).re`. -/
theorem one_quarter_le_one_sub_pmPowerDampedDivisorDensity_one_re :
    (1 / 4 : ℝ) ≤ 1 - (pmPowerDampedDivisorDensity 1).re := by
  have h := pmPowerDampedDivisorDensity_one_re_le_three_quarters.2
  linarith

/-- **Right-Continuity of `(pmPowerDampedDivisorDensity (1 + ε)).re` at `ε = 0`
(`tendsto_pmPowerDampedDivisorDensity_add_one_re`):**
As `ε → 0⁺`, `(pmPowerDampedDivisorDensity (1 + ε)).re → (pmPowerDampedDivisorDensity 1).re`. -/
theorem tendsto_pmPowerDampedDivisorDensity_add_one_re :
    Tendsto (fun ε : ℝ => (pmPowerDampedDivisorDensity (1 + ε)).re)
      (𝓝[>] 0) (𝓝 (pmPowerDampedDivisorDensity 1).re) := by
  have hs : Tendsto (fun ε : ℝ => (1 : ℂ) + ((1 + ε : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 ((1 : ℂ) + ((1 : ℝ) : ℂ))) := by
    have hc : Continuous (fun ε : ℝ => (1 : ℂ) + ((1 + ε : ℝ) : ℂ)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hne1 : (1 : ℂ) + ((1 : ℝ) : ℂ) ≠ 1 := by norm_num
  have hzeta := (differentiableAt_riemannZeta hne1).continuousAt.tendsto.comp hs
  have hzne : riemannZeta ((1 : ℂ) + ((1 : ℝ) : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have hdiv : Tendsto (fun ε : ℝ => pmPowerDampedDivisorDensity (1 + ε))
      (𝓝[>] 0) (𝓝 (pmPowerDampedDivisorDensity 1)) :=
    (tendsto_const_nhds (x := (1 : ℂ))).div hzeta hzne
  exact (Complex.continuous_re.tendsto _).comp hdiv

/-- **Exact Small-Damping Rate of `pmShiftedExponentCovariance`
(`tendsto_pmShiftedExponentCovariance_div_parameter`):**
As `ε → 0⁺`, `pmShiftedExponentCovariance ε / ε` converges to the strictly positive constant
`1 - (pmPowerDampedDivisorDensity 1).re ≥ 1 / 4 > 0`:
`Tendsto (fun ε : ℝ => pmShiftedExponentCovariance ε / ε) (𝓝[>] 0) (𝓝 (1 - (pmPowerDampedDivisorDensity 1).re))`. -/
theorem tendsto_pmShiftedExponentCovariance_div_parameter :
    Tendsto (fun ε : ℝ => pmShiftedExponentCovariance ε / ε)
      (𝓝[>] 0) (𝓝 (1 - (pmPowerDampedDivisorDensity 1).re)) := by
  have hprod := tendsto_pmPowerDampedDivisorDensity_re_div_parameter.mul
    tendsto_pmPowerDampedDivisorDensity_add_one_re
  have hprod' : Tendsto (fun ε : ℝ =>
      ((pmPowerDampedDivisorDensity ε).re / ε) * (pmPowerDampedDivisorDensity (1 + ε)).re)
      (𝓝[>] 0) (𝓝 (pmPowerDampedDivisorDensity 1).re) := by
    simpa [Pi.mul_def] using hprod
  have h := tendsto_pmShiftedExponentSecondDensity_div_parameter.sub hprod'
  have hl : Tendsto (fun ε : ℝ =>
      pmShiftedExponentSecondDensity ε / ε -
        ((pmPowerDampedDivisorDensity ε).re / ε) * (pmPowerDampedDivisorDensity (1 + ε)).re)
      (𝓝[>] 0) (𝓝 (1 - (pmPowerDampedDivisorDensity 1).re)) := by
    simpa [Pi.sub_def] using h
  refine hl.congr fun ε => ?_
  dsimp only [pmShiftedExponentCovariance]
  ring

/-! ## §3. Small-Damping Rates of the Active & Inactive Predictable Martingale Drifts -/

/-- **Exact Small-Damping Rate of `pmActivePredictableMartingaleDrift`
(`tendsto_pmActivePredictableMartingaleDrift_div_parameter`):**
As `ε → 0⁺`, `pmActivePredictableMartingaleDrift ε / ε` converges to
`1 / 4 - (pmPowerDampedDivisorDensity 1).re / 2`:
`Tendsto (fun ε : ℝ => pmActivePredictableMartingaleDrift ε / ε) (𝓝[>] 0) (𝓝 (1 / 4 - (pmPowerDampedDivisorDensity 1).re / 2))`. -/
theorem tendsto_pmActivePredictableMartingaleDrift_div_parameter :
    Tendsto (fun ε : ℝ => pmActivePredictableMartingaleDrift ε / ε)
      (𝓝[>] 0) (𝓝 (1 / 4 - (pmPowerDampedDivisorDensity 1).re / 2)) := by
  have h := (tendsto_pmShiftedExponentCovariance_div_parameter.sub
    tendsto_pmPowerDampedDivisorVariance_div_parameter).div_const (2 : ℝ)
  have hl : Tendsto (fun ε : ℝ =>
      (pmShiftedExponentCovariance ε / ε - pmPowerDampedDivisorVariance ε / ε) / 2)
      (𝓝[>] 0) (𝓝 (1 / 4 - (pmPowerDampedDivisorDensity 1).re / 2)) := by
    convert h using 2
    ring
  refine hl.congr fun ε => ?_
  dsimp only [pmActivePredictableMartingaleDrift]
  ring

/-- **Exact Small-Damping Rate of the Inactive Predictable Martingale Drift
(`tendsto_neg_half_pmShiftedExponentCovariance_div_parameter`):**
As `ε → 0⁺`, `(-pmShiftedExponentCovariance ε / 2) / ε` converges to
`-(1 - (pmPowerDampedDivisorDensity 1).re) / 2`:
`Tendsto (fun ε : ℝ => (-pmShiftedExponentCovariance ε / 2) / ε) (𝓝[>] 0) (𝓝 (-(1 - (pmPowerDampedDivisorDensity 1).re) / 2))`. -/
theorem tendsto_neg_half_pmShiftedExponentCovariance_div_parameter :
    Tendsto (fun ε : ℝ => (-pmShiftedExponentCovariance ε / 2) / ε)
      (𝓝[>] 0) (𝓝 (-(1 - (pmPowerDampedDivisorDensity 1).re) / 2)) := by
  have h := (tendsto_pmShiftedExponentCovariance_div_parameter.neg).div_const (2 : ℝ)
  convert! h using 1
  ext ε
  ring

end
end GaloisForLFunctions.BezoutValuationIncidence

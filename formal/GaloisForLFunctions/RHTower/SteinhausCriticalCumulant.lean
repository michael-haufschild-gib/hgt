import GaloisForLFunctions.RHTower.SteinhausSuperConstant
import GaloisForLFunctions.RHTower.SteinhausCumulantTaylor
import GaloisForLFunctions.HTGeometry.IntegralLogCesaro

/-!
# The critical cumulant

At the square-integrability threshold `α = 1/2` the fixed integrand of the scaling identity is
`h(u) = log I₀(u^{−1/2}/2)`, whose tail is exactly `1/(16u)`: indeed `log I₀(x) ∼ x²/4` and
`x = u^{−1/2}/2` gives `u·h(u) → 1/16`.  The logarithmic Cesàro theorem then turns the truncated
integral into `(1/16) log R`, and the scaling identity `Λ_{1/2}(λ) = λ² ∫₀^{λ^{−2}} h` gives the
card's `(20)`:

`Λ_{1/2}(λ)/(λ² log(1/λ)) → 1/8`.
-/

open MeasureTheory Filter Topology Set

namespace HTGeometry

noncomputable section

/-- The critical integrand, truncated below `1` so that it is globally continuous. -/
def truncCritIntegrand (u : ℝ) : ℝ := steinhausLogLaplace (weightProfile (1 / 2) (max u 1))

theorem continuous_truncCritIntegrand : Continuous truncCritIntegrand := by
  have hrpow : ContinuousOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (Ici (1 : ℝ)) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      have : (1 : ℝ) ≤ x := hx
      linarith
    exact (Real.continuousAt_rpow_const x _ (Or.inl hx0)).continuousWithinAt
  have hmax : Continuous fun u : ℝ => max u 1 := continuous_id.max continuous_const
  have hcomp : Continuous fun u : ℝ => (max u 1) ^ (-(1 / 2 : ℝ)) :=
    hrpow.comp_continuous hmax fun u => le_max_right u 1
  have hprof : Continuous fun u : ℝ => weightProfile (1 / 2) (max u 1) := by
    have : (fun u : ℝ => weightProfile (1 / 2) (max u 1))
        = fun u : ℝ => (1 - 1 / 2 : ℝ) * (max u 1) ^ (-(1 / 2 : ℝ)) := rfl
    rw [this]
    exact continuous_const.mul hcomp
  exact continuous_steinhausLogLaplace.comp hprof

/-- The critical profile at scale `u`. -/
theorem weightProfile_half (u : ℝ) : weightProfile (1 / 2) u = u ^ (-(1 / 2 : ℝ)) / 2 := by
  rw [weightProfile]
  ring

/-- **The exact tail of the critical integrand:** `u·h(u) → 1/16`. -/
theorem tendsto_mul_truncCritIntegrand :
    Tendsto (fun u : ℝ => u * truncCritIntegrand u) atTop (𝓝 (1 / 16)) := by
  set ψ : ℝ → ℝ := fun u : ℝ => u ^ (-(1 / 2 : ℝ)) / 2 with hψ
  have hψ0 : Tendsto ψ atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := (1 / 2 : ℝ)) (by norm_num)
    simpa [hψ] using h.div_const 2
  have hψne : Tendsto ψ atTop (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hψ0 ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have : (0 : ℝ) < u ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hu _
    simp only [hψ, mem_compl_iff, mem_singleton_iff]
    positivity
  have hratio := tendsto_steinhausLogLaplace_div_sq.comp hψne
  have hscaled : Tendsto (fun u : ℝ => steinhausLogLaplace (ψ u) / (ψ u) ^ 2 / 4)
      atTop (𝓝 (1 / 16)) := by
    have h4 := hratio.div_const 4
    rw [show (1 : ℝ) / 4 / 4 = 1 / 16 by norm_num] at h4
    simpa [Function.comp_def] using h4
  refine Tendsto.congr' ?_ hscaled
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hmax : max u 1 = u := max_eq_left hu
  have hsq : (ψ u) ^ 2 = 1 / (4 * u) := by
    rw [hψ]
    have h1 : (u ^ (-(1 / 2 : ℝ)) / 2) ^ 2 = (u ^ (-(1 / 2 : ℝ))) ^ 2 / 4 := by ring
    rw [h1, ← Real.rpow_natCast (u ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hu0.le]
    norm_num
    rw [Real.rpow_neg_one]
    field_simp
  have hprof : weightProfile (1 / 2) (max u 1) = ψ u := by
    rw [hmax, weightProfile_half, hψ]
  rw [truncCritIntegrand, hprof, hsq]
  field_simp


/-- The logarithmic average of the critical integrand. -/
theorem tendsto_truncCrit_logAverage :
    Tendsto (fun R : ℝ => (∫ u in (1 : ℝ)..R, truncCritIntegrand u) / Real.log R)
      atTop (𝓝 (1 / 16)) :=
  tendsto_logAverage_atTop_of_tendsto continuous_truncCritIntegrand
    tendsto_mul_truncCritIntegrand

/-- Above `1` the truncation is invisible. -/
theorem intervalIntegral_truncCrit_eq {R : ℝ} (hR : 1 ≤ R) :
    (∫ u in (1 : ℝ)..R, truncCritIntegrand u)
      = ∫ u in (1 : ℝ)..R, steinhausLogLaplace (weightProfile (1 / 2) u) := by
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hR, mem_Icc] at hu
  rw [truncCritIntegrand, max_eq_left hu.1]

/-- The critical tail integral grows logarithmically with rate `1/16`. -/
theorem tendsto_rvTailIntegral_div_log :
    Tendsto (fun R : ℝ => rvTailIntegral (1 / 2) R / Real.log R) atTop (𝓝 (1 / 16)) := by
  have hhead : IntervalIntegrable
      (fun u : ℝ => steinhausLogLaplace (weightProfile (1 / 2) u)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integrableOn_profileCumulant_Ioc (by norm_num)
  have hconst : Tendsto
      (fun R : ℝ => (∫ u in (0 : ℝ)..1, steinhausLogLaplace (weightProfile (1 / 2) u))
        / Real.log R) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop _
  have hsum := hconst.add tendsto_truncCrit_logAverage
  rw [zero_add] at hsum
  refine Tendsto.congr' ?_ hsum
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have hcontOn : ContinuousOn
      (fun u : ℝ => steinhausLogLaplace (weightProfile (1 / 2) u)) (Ici (1 : ℝ)) := by
    refine ContinuousOn.congr continuous_truncCritIntegrand.continuousOn fun u hu => ?_
    rw [truncCritIntegrand, max_eq_left hu]
  have hsub : uIcc (1 : ℝ) R ⊆ Ici (1 : ℝ) := by
    rw [uIcc_of_le hR]
    exact Icc_subset_Ici_self
  have htail : IntervalIntegrable
      (fun u : ℝ => steinhausLogLaplace (weightProfile (1 / 2) u)) volume 1 R :=
    (hcontOn.mono hsub).intervalIntegrable
  rw [rvTailIntegral, ← intervalIntegral.integral_add_adjacent_intervals hhead htail,
    intervalIntegral_truncCrit_eq hR]
  ring


/-- **The critical cumulant asymptotic**, the card's `(20)`:
`Λ_{1/2}(λ)/(λ² log(1/λ)) → 1/8`. -/
theorem tendsto_rvCumulant_crit :
    Tendsto (fun lam : ℝ => rvCumulant (1 / 2) lam / (lam ^ 2 * Real.log (1 / lam)))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 8)) := by
  have hinv : Tendsto (fun lam : ℝ => lam ^ (-(1 / (1 / 2 : ℝ)))) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_rpow_neg_inv_atTop (by norm_num)
  have hcomp := tendsto_rvTailIntegral_div_log.comp hinv
  have htwo := hcomp.const_mul (2 : ℝ)
  rw [show (2 : ℝ) * (1 / 16) = 1 / 8 by norm_num] at htwo
  refine Tendsto.congr' ?_ htwo
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  have hlam0 : (0 : ℝ) < lam := hlam
  have hexp : (1 : ℝ) / (1 / 2 : ℝ) = 2 := by norm_num
  have hid := rvCumulant_eq_rpow_mul_tail (α := (1 / 2 : ℝ)) (by norm_num) hlam0
  rw [hexp] at hid
  have hpow2 : lam ^ (2 : ℝ) = lam ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hpow2] at hid
  have hlogR : Real.log (lam ^ (-(2 : ℝ))) = -2 * Real.log lam := by
    rw [Real.log_rpow hlam0]
  have hlog1 : Real.log (1 / lam) = -Real.log lam := by
    rw [one_div, Real.log_inv]
  rw [Function.comp_apply, hexp, hid, hlogR, hlog1]
  rcases eq_or_ne (Real.log lam) 0 with hz | hz
  · rw [hz]
    simp
  · have hne : lam ^ 2 ≠ 0 := by positivity
    field_simp

end

end HTGeometry

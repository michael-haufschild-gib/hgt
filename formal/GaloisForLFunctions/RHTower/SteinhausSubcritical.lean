import GaloisForLFunctions.RHTower.SteinhausCumulantTaylor

/-!
# The sub-critical regime of the cumulant

For `α < 1/2` the profile is square integrable, so dominated convergence turns the pointwise
`log I₀(λ w)/λ² → w²/4` into `Λ_α(λ)/λ² → (1/4)∫₀¹ w_α²`.  This is the card's `(18)`.
-/

open MeasureTheory Set Filter Topology

namespace HTGeometry

noncomputable section

theorem weightProfile_sq_eq {α : ℝ} {v : ℝ} (hv : 0 < v) :
    weightProfile α v ^ 2 = (1 - α) ^ 2 * v ^ (-(2 * α)) := by
  rw [weightProfile, mul_pow, ← Real.rpow_natCast (v ^ (-α)) 2, ← Real.rpow_mul hv.le]
  congr 2
  push_cast
  ring

theorem intervalIntegrable_weightProfile_sq {α : ℝ} (hα : α < 1 / 2) :
    IntervalIntegrable (fun v : ℝ => weightProfile α v ^ 2) volume 0 1 := by
  have hbase : IntervalIntegrable (fun v : ℝ => v ^ (-(2 * α))) volume 0 1 := by
    refine intervalIntegral.intervalIntegrable_rpow' ?_
    linarith
  have hmain := hbase.const_mul ((1 - α) ^ 2)
  constructor
  · refine (hmain.1).congr_fun_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact (weightProfile_sq_eq hv.1).symm
  · have hempty : Set.Ioc (1 : ℝ) 0 = ∅ := Set.Ioc_eq_empty (by norm_num)
    rw [IntegrableOn, hempty]
    simp

/-- The rescaled integrand of the cumulant. -/
def rvQuadIntegrand (α lam v : ℝ) : ℝ := steinhausLogLaplace (lam * weightProfile α v) / lam ^ 2

theorem rvQuadIntegrand_bound {α : ℝ} (hα : α < 1) {lam : ℝ} (hlam : lam ≠ 0) (v : ℝ)
    (hv : 0 ≤ v) : |rvQuadIntegrand α lam v| ≤ weightProfile α v ^ 2 / 2 := by
  have hw : 0 ≤ weightProfile α v := weightProfile_nonneg hα hv
  have hnn : 0 ≤ steinhausLogLaplace (lam * weightProfile α v) :=
    steinhausLogLaplace_nonneg _
  have hup := steinhausLogLaplace_le_sq (lam * weightProfile α v)
  have hlam2 : (0 : ℝ) < lam ^ 2 := by positivity
  rw [rvQuadIntegrand, abs_div, abs_of_nonneg hnn,
    abs_of_nonneg (le_of_lt hlam2), div_le_div_iff₀ hlam2 (by norm_num)]
  nlinarith [hup, hlam2, hnn]

/-- **The pointwise sub-critical limit.** -/
theorem tendsto_rvQuadIntegrand {α : ℝ} (hα : α < 1) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun lam : ℝ => rvQuadIntegrand α lam v) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (weightProfile α v ^ 2 / 4)) := by
  have hw : 0 < weightProfile α v := weightProfile_pos hα hv
  have hmap : Tendsto (fun lam : ℝ => lam * weightProfile α v)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun lam : ℝ => lam * weightProfile α v) (nhds 0)
          (nhds (0 * weightProfile α v)) := (continuous_id.mul continuous_const).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with lam hlam
      have hlam0 : 0 < lam := hlam
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      positivity
  have hcomp := tendsto_steinhausLogLaplace_div_sq.comp hmap
  have hscaled := hcomp.const_mul (weightProfile α v ^ 2)
  have hval : weightProfile α v ^ 2 * (1 / 4) = weightProfile α v ^ 2 / 4 := by ring
  rw [hval] at hscaled
  refine hscaled.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  have hlam0 : 0 < lam := hlam
  rw [rvQuadIntegrand, Function.comp_apply]
  field_simp

end

end HTGeometry

import GaloisForLFunctions.HTGeometry.SteinhausWeightProfile

/-!
# The exact scaling identity of the regular-variation cumulant

The profile `w_α(v) = (1−α)v^{−α}` is homogeneous of degree `−α`, so the tilt parameter can be
absorbed entirely into the length of the integration interval:

`Λ_α(λ) = λ^{1/α} ∫₀^{λ^{−1/α}} log I₀(w_α(u)) du`   for `0 < α < 1`, `λ > 0`.

The substitution is the linear map `v = λ^{1/α} u`, under which `λ w_α(λ^{1/α} u) = w_α(u)`
identically.  Every small-tilt asymptotic of the cumulant is therefore a large-interval asymptotic
of the *fixed* integrand `log I₀(w_α(·))`, with no `λ` left inside the integral.
-/

open MeasureTheory Set Filter Topology

namespace HTGeometry

noncomputable section

/-- The tail integral of the fixed profile cumulant integrand. -/
def rvTailIntegral (α R : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..R, steinhausLogLaplace (weightProfile α u)

/-- The scaling that absorbs the tilt: `λ · w_α(λ^{1/α} u) = w_α(u)`. -/
theorem mul_weightProfile_rpow {α : ℝ} (hα0 : 0 < α) {lam : ℝ} (hlam : 0 < lam) {u : ℝ}
    (hu : 0 ≤ u) : lam * weightProfile α (lam ^ (1 / α) * u) = weightProfile α u := by
  have hc0 : (0 : ℝ) < lam ^ (1 / α) := Real.rpow_pos_of_pos hlam _
  rw [weightProfile, weightProfile, Real.mul_rpow hc0.le hu]
  have hcpow : (lam ^ (1 / α)) ^ (-α) = lam⁻¹ := by
    rw [← Real.rpow_mul hlam.le]
    rw [show 1 / α * -α = -1 by field_simp]
    exact Real.rpow_neg_one lam
  rw [hcpow]
  field_simp

/-- **The scaling identity.** -/
theorem rvCumulant_eq_rpow_mul_tail {α : ℝ} (hα0 : 0 < α) {lam : ℝ} (hlam : 0 < lam) :
    rvCumulant α lam = lam ^ (1 / α) * rvTailIntegral α (lam ^ (-(1 / α))) := by
  set c : ℝ := lam ^ (1 / α) with hc
  have hc0 : (0 : ℝ) < c := Real.rpow_pos_of_pos hlam _
  set R : ℝ := lam ^ (-(1 / α)) with hR
  have hR0 : (0 : ℝ) < R := Real.rpow_pos_of_pos hlam _
  have hcR : c * R = 1 := by
    rw [hc, hR, ← Real.rpow_add hlam]
    simp
  have hsub := intervalIntegral.smul_integral_comp_mul_left
    (fun v : ℝ => steinhausLogLaplace (lam * weightProfile α v)) c (a := 0) (b := R)
  rw [mul_zero, hcR] at hsub
  have hcongr : (∫ u in (0 : ℝ)..R, steinhausLogLaplace (lam * weightProfile α (c * u)))
      = rvTailIntegral α R := by
    refine intervalIntegral.integral_congr ?_
    intro u hu
    rw [uIcc_of_le hR0.le, mem_Icc] at hu
    simp only []
    rw [hc, mul_weightProfile_rpow hα0 hlam hu.1]
  rw [hcongr] at hsub
  rw [rvCumulant, ← hsub, smul_eq_mul]

/-- The reciprocal power tends to infinity with the tilt going to zero. -/
theorem tendsto_rpow_neg_inv_atTop {α : ℝ} (hα0 : 0 < α) :
    Tendsto (fun lam : ℝ => lam ^ (-(1 / α))) (𝓝[>] (0 : ℝ)) atTop := by
  have hk : (0 : ℝ) < 1 / α := by positivity
  have hcont : ContinuousAt (fun x : ℝ => x ^ (1 / α)) 0 :=
    Real.continuousAt_rpow_const 0 _ (Or.inr hk.le)
  have h0 : Tendsto (fun lam : ℝ => lam ^ (1 / α)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
      rwa [Real.zero_rpow hk.ne'] at h
    · filter_upwards [self_mem_nhdsWithin] with lam hlam
      exact Real.rpow_pos_of_pos hlam _
  have hinv := tendsto_inv_nhdsGT_zero.comp h0
  refine Tendsto.congr' ?_ hinv
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  have hlam0 : (0 : ℝ) < lam := hlam
  rw [Function.comp_apply, ← Real.rpow_neg hlam0.le]


end

end HTGeometry

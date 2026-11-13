import GaloisForLFunctions.HTGeometry.PoissonMeasureUniqueness

/-!
# Local vanishing of Poisson representing mass

Integrating the kernel over a collar of an angular interval captures a fixed
fraction of that interval's mass. Dominated radial convergence then removes
the mass wherever the radial values are bounded and tend almost everywhere to zero.
-/

open Complex MeasureTheory Metric Filter Topology Set

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem radialPoisson_bounds {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (t θ : ℝ) :
    0 ≤ poissonKernel 0 (circleMap 0 r θ) (circleMap 0 1 t) ∧
      poissonKernel 0 (circleMap 0 r θ) (circleMap 0 1 t) ≤
        (1 - r ^ 2) / (1 - r) ^ 2 := by
  have hn : ‖circleMap 0 r θ‖ = r := by
    rw [norm_circleMap_zero, abs_of_nonneg hr]
  refine ⟨poissonKernel_circleMap_one_nonneg (by rw [hn]; exact hr1) t, ?_⟩
  simpa only [hn] using poissonKernel_circleMap_one_le
    (w := circleMap 0 r θ) (by rw [hn]; exact hr1) t

private theorem integrable_radialPoisson_prod
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Integrable (fun p : ℝ × ℝ =>
      poissonKernel 0 (circleMap 0 r p.2) (circleMap 0 1 p.1)) (μ.prod ν) := by
  have hc := (continuous_poissonKernel_circleMap_two hr hr1).comp
    (f := fun p : ℝ × ℝ => (p.2, p.1))
    (continuous_snd.prodMk continuous_fst)
  refine Integrable.of_bound hc.aestronglyMeasurable ((1 - r ^ 2) / (1 - r) ^ 2) ?_
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (radialPoisson_bounds hr hr1 p.1 p.2).1]
  exact (radialPoisson_bounds hr hr1 p.1 p.2).2

private theorem radialPoisson_lower {r t θ : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hθ : θ ∈ Icc (t - (1 - r)) (t + (1 - r))) :
    (1 + r) / (4 * (1 - r)) ≤ poissonKernel 0 (circleMap 0 r θ) (circleMap 0 1 t) := by
  have hd : |t - θ| ≤ 1 - r := by
    rw [abs_le]
    exact ⟨by linarith only [hθ.2], by linarith only [hθ.1]⟩
  have hh := le_poissonKernel_of_close hr hr1 t θ
    ((norm_circleMap_sub_circleMap_le t θ).trans hd)
  simpa only [circleMap, zero_add, ofReal_one, one_mul] using hh

private theorem integral_radialPoisson_lower_constant {r : ℝ} (hr1 : r < 1) (t : ℝ) :
    (∫ _θ in Icc (t - (1 - r)) (t + (1 - r)),
      (1 + r) / (4 * (1 - r))) = (1 + r) / 2 := by
  have hδ : 0 < 1 - r := sub_pos.mpr hr1
  rw [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith only [hδ]),
    smul_eq_mul]
  field_simp [ne_of_gt hδ]
  ring

/-- An angular interval of radius `1-r` captures at least half a unit of kernel mass. -/
private theorem radialPoisson_integral_ge_half {α β η r t : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hcollar : 1 - r ≤ η)
    (ht : t ∈ Icc α β) :
    (1 / 2 : ℝ) ≤ ∫ θ in Icc (α - η) (β + η),
      poissonKernel 0 (circleMap 0 r θ) (circleMap 0 1 t) := by
    let K : ℝ → ℝ := fun θ => poissonKernel 0 (circleMap 0 r θ) (circleMap 0 1 t)
    have hpair : Continuous (fun θ : ℝ => (θ, t)) :=
      continuous_id.prodMk continuous_const
    have hct : Continuous K := (continuous_poissonKernel_circleMap_two hr hr1).comp
      (f := fun θ : ℝ => (θ, t)) hpair
    have hsmall : (1 + r) / 2 ≤
        ∫ θ in Icc (t - (1 - r)) (t + (1 - r)), K θ := by
      have hconst : IntegrableOn (fun _θ : ℝ => (1 + r) / (4 * (1 - r)))
          (Icc (t - (1 - r)) (t + (1 - r))) volume :=
        integrableOn_const (ne_of_lt measure_Icc_lt_top)
      have hkernel : IntegrableOn K (Icc (t - (1 - r)) (t + (1 - r))) volume :=
        hct.continuousOn.integrableOn_Icc
      have hm := setIntegral_mono_on hconst hkernel
        measurableSet_Icc (fun _ hθ => radialPoisson_lower hr hr1 hθ)
      rwa [integral_radialPoisson_lower_constant hr1 t] at hm
    have hsub : Icc (t - (1 - r)) (t + (1 - r)) ⊆ Icc (α - η) (β + η) := by
      intro θ hθ
      exact ⟨by linarith only [ht.1, hθ.1, hcollar],
        by linarith only [ht.2, hθ.2, hcollar]⟩
    have hbig : IntegrableOn K (Icc (α - η) (β + η)) volume :=
      hct.continuousOn.integrableOn_Icc
    have hb := setIntegral_mono_set hbig
      (ae_of_all _ fun θ => (radialPoisson_bounds hr hr1 t θ).1) hsub.eventuallyLE
    exact (show (1 / 2 : ℝ) ≤ (1 + r) / 2 by linarith only [hr]).trans
      (hsmall.trans hb)

/-- A collar of an arc captures a fixed fraction of the Poisson mass of that arc.
The estimate uses one radius, with its boundary distance smaller than the collar. -/
theorem measureReal_Icc_le_two_mul_radial_integral
    {ν : Measure ℝ} [IsFiniteMeasure ν] {u : ℂ → ℝ}
    (hrep : ∀ w ∈ ball (0 : ℂ) 1,
      ∫ t, poissonKernel 0 w (circleMap 0 1 t) ∂ν = u w)
    {α β η r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hcollar : 1 - r ≤ η) :
    ν.real (Icc α β) ≤
      2 * ∫ θ in Icc (α - η) (β + η), u (circleMap 0 r θ) := by
  let K : ℝ → ℝ → ℝ := fun t θ =>
    poissonKernel 0 (circleMap 0 r θ) (circleMap 0 1 t)
  have hmem (θ : ℝ) : circleMap 0 r θ ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr] using hr1
  have hint := integrable_radialPoisson_prod (ν.restrict (Icc α β))
    (volume.restrict (Icc (α - η) (β + η))) hr hr1
  have hleft : ν.real (Icc α β) / 2 ≤
      ∫ t in Icc α β, (∫ θ in Icc (α - η) (β + η), K t θ) ∂ν := by
    have hm := integral_mono_ae (integrable_const (1 / 2 : ℝ))
      hint.integral_prod_left (by
        filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
        exact radialPoisson_integral_ge_half hr hr1 hcollar ht)
    simpa only [integral_const, smul_eq_mul, Measure.real, K,
      Measure.restrict_apply MeasurableSet.univ, univ_inter, div_eq_mul_inv, one_mul] using hm
  have hfull (θ : ℝ) : Integrable (fun t => K t θ) ν :=
    (unitPoissonTest (w := circleMap 0 r θ) (by simpa only [mem_ball, dist_zero_right]
      using (hmem θ))).integrable ν
  have hu : Integrable (fun θ => u (circleMap 0 r θ))
      (volume.restrict (Icc (α - η) (β + η))) := by
    have hi := integrable_radialPoisson_prod ν
      (volume.restrict (Icc (α - η) (β + η))) hr hr1
    have hii : Integrable (fun θ => ∫ t, K t θ ∂ν)
        (volume.restrict (Icc (α - η) (β + η))) := hi.integral_prod_right
    simpa only [K, hrep _ (hmem _)] using hii
  have hright : (∫ θ in Icc (α - η) (β + η), ∫ t in Icc α β, K t θ ∂ν) ≤
      ∫ θ in Icc (α - η) (β + η), u (circleMap 0 r θ) := by
    refine integral_mono_ae hint.integral_prod_right hu (ae_of_all _ fun θ => ?_)
    have hh := setIntegral_le_integral (s := Icc α β) (hfull θ)
      (ae_of_all _ fun t => (radialPoisson_bounds hr hr1 t θ).1)
    simpa only [K, hrep _ (hmem _)] using hh
  rw [integral_integral_swap hint] at hleft
  have hh := hleft.trans hright
  linarith only [hh]

/-- Bounded radial values that tend to zero almost everywhere remove the representing
mass on a smaller arc. No uniform boundary convergence is required. -/
theorem measureReal_Icc_eq_zero_of_bounded_radial_ae_vanishing
    {ν : Measure ℝ} [IsFiniteMeasure ν] {u : ℂ → ℝ}
    (hrep : ∀ w ∈ ball (0 : ℂ) 1,
      ∫ t, poissonKernel 0 w (circleMap 0 1 t) ∂ν = u w)
    (hu : ContinuousOn u (ball (0 : ℂ) 1))
    {α β η : ℝ} (hη : 0 < η)
    {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n < 1)
    (ht : Tendsto r atTop (𝓝 1)) {M : ℝ}
    (hbound : ∀ n, ∀ θ ∈ Icc (α - η) (β + η),
      ‖u (circleMap 0 (r n) θ)‖ ≤ M)
    (hzero : ∀ᵐ θ ∂volume.restrict (Icc (α - η) (β + η)),
      Tendsto (fun n => u (circleMap 0 (r n) θ)) atTop (𝓝 0)) :
    ν.real (Icc α β) = 0 := by
  have hc (n : ℕ) : ContinuousOn (fun θ => u (circleMap 0 (r n) θ))
      (Icc (α - η) (β + η)) := by
    apply hu.comp (continuous_circleMap 0 (r n)).continuousOn
    intro θ _
    rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg (hr n)]
    exact hr1 n
  have hi : Tendsto
      (fun n => ∫ θ in Icc (α - η) (β + η), u (circleMap 0 (r n) θ))
      atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (fun _θ : ℝ => M)
      (fun n => (hc n).aestronglyMeasurable measurableSet_Icc)
      (integrable_const M)
      (fun n => by
        filter_upwards [self_mem_ae_restrict measurableSet_Icc] with θ hθ
        exact hbound n θ hθ) hzero
  have hd : Tendsto (fun n => 1 - r n) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub ht
  have hlarge : ∀ᶠ n in atTop, 1 - r n ≤ η :=
    (hd.eventually (gt_mem_nhds hη)).mono fun _ hn => hn.le
  have hle : ν.real (Icc α β) ≤ 0 := by
    have htwo : Tendsto
        (fun n => 2 * ∫ θ in Icc (α - η) (β + η), u (circleMap 0 (r n) θ))
        atTop (𝓝 (0 : ℝ)) := by simpa only [mul_zero] using hi.const_mul 2
    exact le_of_tendsto_of_tendsto tendsto_const_nhds htwo
      (hlarge.mono fun n hn => measureReal_Icc_le_two_mul_radial_integral
        hrep (hr n) (hr1 n) hn)
  exact le_antisymm hle measureReal_nonneg

#print axioms measureReal_Icc_le_two_mul_radial_integral
#print axioms measureReal_Icc_eq_zero_of_bounded_radial_ae_vanishing

end
end GaloisForLFunctions.HTGeometry

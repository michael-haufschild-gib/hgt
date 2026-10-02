import GaloisForLFunctions.RHTower.MobiusDivisorCriticalSourceAutocorrelation
import GaloisForLFunctions.HTGeometry.BochnerLaplaceHolomorphy

/-!
# Absolute admission of the actual correlation transform

The literal source is continuous, bounded and integrable. Its complete
correlation is continuous and integrable, so its unilateral Laplace
transform is continuous on the closed right half-plane and holomorphic
inside. No exponential moment at a negative real frequency is assumed.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower

theorem criticalAbelLogProfile_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    criticalAbelLogProfile t = 0 := by
  have hx : Real.exp t ≤ 1 := by simpa using Real.exp_le_exp.mpr ht
  simp only [criticalAbelLogProfile, criticalContinuousAbel_eq_zero_le_one hx, mul_zero]

theorem continuous_criticalAbelLogProfile : Continuous criticalAbelLogProfile := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  let T : ℝ := max 0 t + 1
  have hT : 0 ≤ T := by dsimp [T]; linarith [le_max_left (0 : ℝ) t]
  have htT : t < T := by dsimp [T]; linarith [le_max_right (0 : ℝ) t]
  have hz : ContinuousOn criticalAbelLogProfile (Iic (0 : ℝ)) :=
    (continuousOn_congr (fun y hy => criticalAbelLogProfile_zero_of_nonpos hy)).mpr
      continuousOn_const
  have hc := hz.union_of_isClosed (continuousOn_criticalAbelLogProfile hT)
    isClosed_Iic isClosed_Icc
  have hsub : Iio T ⊆ Iic (0 : ℝ) ∪ Icc 0 T := by
    intro y hy
    by_cases hy0 : y ≤ 0
    · exact Or.inl hy0
    · exact Or.inr ⟨(lt_of_not_ge hy0).le, hy.le⟩
  exact (hc t (hsub htT)).continuousAt
    (Filter.mem_of_superset (Iio_mem_nhds htT) hsub)

theorem integrable_criticalAbelLogProfile : Integrable criticalAbelLogProfile := by
  have hi : IntegrableOn criticalAbelLogProfile (Ioi (0 : ℝ)) := by
    apply integrableOn_criticalAbelLogProfile_quadratic.norm.mono'
      measurable_criticalAbelLogProfile.aestronglyMeasurable.restrict
    filter_upwards with t
    simp only [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 1 + t ^ (2 : ℕ))]
    nlinarith [abs_nonneg (criticalAbelLogProfile t), sq_nonneg t]
  have hfun : (Ioi (0 : ℝ)).indicator criticalAbelLogProfile = criticalAbelLogProfile := by
    funext t
    by_cases ht : 0 < t
    · simp [ht]
    · simp [ht, criticalAbelLogProfile_zero_of_nonpos (le_of_not_gt ht)]
  rw [← hfun]
  exact (integrable_indicator_iff measurableSet_Ioi).mpr hi

theorem criticalAbelLogProfile_uniform_bound (t : ℝ) :
    |criticalAbelLogProfile t| ≤
      ∫ u in Ioi (0 : ℝ), |criticalAbelLogVelocity u| := by
  by_cases ht : 0 ≤ t
  · rw [criticalAbelLogProfile_eq_velocity_tail ht, abs_neg]
    calc
      _ ≤ ∫ u in Ioi t, |criticalAbelLogVelocity u| := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := volume.restrict (Ioi t)) criticalAbelLogVelocity
      _ ≤ _ := by
        apply setIntegral_mono_set integrableOn_criticalAbelLogVelocity.norm
        · exact Filter.Eventually.of_forall (fun _ => abs_nonneg _)
        · exact Filter.Eventually.of_forall (fun _ hx => (Ioi_subset_Ioi ht) hx)
  · rw [criticalAbelLogProfile_zero_of_nonpos (le_of_not_ge ht), abs_zero]
    exact integral_nonneg (fun _ => abs_nonneg _)

theorem integrable_criticalAbelLogProfile_lag_pair :
    Integrable (fun z : ℝ × ℝ =>
      criticalAbelLogProfile (z.2 + z.1) * criticalAbelLogProfile z.2)
      (volume.prod volume) := by
  have h := (measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)).integrable_comp_of_integrable
    (integrable_criticalAbelLogProfile.mul_prod integrable_criticalAbelLogProfile)
  apply h.congr
  filter_upwards with z
  dsimp only [Function.comp_apply]
  rw [add_comm z.1 z.2]

theorem integrable_criticalAbelLogAutocorrelation : Integrable criticalAbelLogAutocorrelation :=
  integrable_criticalAbelLogProfile_lag_pair.integral_prod_left

theorem continuous_criticalAbelLogAutocorrelation : Continuous criticalAbelLogAutocorrelation := by
  apply continuous_of_dominated
    (bound := fun t => (∫ u in Ioi (0 : ℝ), |criticalAbelLogVelocity u|) *
      |criticalAbelLogProfile t|)
  · intro u
    exact (((continuous_criticalAbelLogProfile.comp (continuous_id.add_const u)).mul
      continuous_criticalAbelLogProfile).aestronglyMeasurable)
  · intro u
    filter_upwards with t
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (criticalAbelLogProfile_uniform_bound (t + u)) (abs_nonneg _)
  · exact integrable_criticalAbelLogProfile.norm.const_mul _
  · filter_upwards with t
    exact (continuous_criticalAbelLogProfile.comp (continuous_const.add continuous_id)).mul
      continuous_const

private theorem continuousOn_laplace_closedRight {f : ℝ → ℂ} (hf : Integrable f) :
    ContinuousOn (bochnerLaplaceRay f) {s : ℂ | 0 ≤ s.re} := by
  apply continuousOn_of_dominated (bound := fun t => ‖f t‖)
  · intro s _
    exact (((show Continuous (expRay s) by unfold expRay; fun_prop).aestronglyMeasurable).smul
      hf.aestronglyMeasurable).restrict
  · intro s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h := expRay_smul_norm_le f 0 s hs t ht.le
    simpa [expRay] using h
  · exact hf.norm.integrableOn
  · filter_upwards with t
    exact (show Continuous (fun s : ℂ => expRay s t • f t) by
      unfold expRay
      fun_prop).continuousOn

/-- Unilateral transform of the actual complete-source autocorrelation. -/
def criticalAbelCorrelationLaplace (s : ℂ) : ℂ :=
  bochnerLaplaceRay (fun u => (criticalAbelLogAutocorrelation u : ℂ)) s

/-- Unilateral transform of the actual Abel logarithmic source. -/
def criticalAbelProfileLaplace (s : ℂ) : ℂ :=
  bochnerLaplaceRay (fun t => (criticalAbelLogProfile t : ℂ)) s

theorem continuousOn_criticalAbelCorrelationLaplace :
    ContinuousOn criticalAbelCorrelationLaplace {s : ℂ | 0 ≤ s.re} :=
  continuousOn_laplace_closedRight integrable_criticalAbelLogAutocorrelation.ofReal

theorem continuousOn_criticalAbelProfileLaplace :
    ContinuousOn criticalAbelProfileLaplace {s : ℂ | 0 ≤ s.re} :=
  continuousOn_laplace_closedRight integrable_criticalAbelLogProfile.ofReal

theorem differentiableOn_criticalAbelCorrelationLaplace :
    DifferentiableOn ℂ criticalAbelCorrelationLaplace {s : ℂ | 0 < s.re} := by
  intro s hs
  apply (bochnerLaplaceRay_differentiableAt
    (integrable_criticalAbelLogAutocorrelation.ofReal (𝕜 := ℂ)).aestronglyMeasurable
    (c := 0) _ s hs).differentiableWithinAt
  convert (integrable_criticalAbelLogAutocorrelation.ofReal (𝕜 := ℂ)).integrableOn
    (s := Ioi (0 : ℝ)) using 1
  simp [expRay]

end RHTower

import GaloisForLFunctions.HTGeometry.EinastoRadialGravity

/-!
# Information-curvature scaling for the regular Einasto source

Applies the inverse-cube information ansatz of arXiv:2608.06941v1, equations
(7) and (12), to the enclosed mass and regular lapse of arXiv:2608.23600v1.
The source is actual enclosed information, proportional to the radial mass
integral. Its spherical-lapse curvature expression is continuous at the
center, strictly decreasing at positive radii, and tends to zero at infinity.

The central value gives an exact necessary and sufficient condition for a
uniform curvature ceiling. The mean enclosed density strictly exceeds local
boundary density; this proves the sign of the actual curvature derivative.
These are statements about the existing lapse expression, without a newly
constructed spacetime connection or any assumption of the physical ansatz.
-/

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def einastoInformationCurvature (d l a r : ℝ) : ℝ := 2 * einastoCore d l a r

def einastoEnclosedInformation (c d l a r : ℝ) : ℝ := exp c * einastoMass d l a r

theorem einastoDensity_strictAntiOn (d l a : ℝ) : StrictAntiOn (einastoDensity d l a) (Ici 0) := by
  intro x hx y hy hxy
  unfold einastoDensity
  apply mul_lt_mul_of_pos_left _ (exp_pos d)
  apply exp_lt_exp.mpr
  apply neg_lt_neg
  exact rpow_lt_rpow (div_nonneg hx (exp_pos l).le)
    ((div_lt_div_iff_of_pos_right (exp_pos l)).mpr hxy) (exp_pos (-a))

theorem einastoCore_pos (d l a t : ℝ) : 0 < einastoCore d l a (exp t) := by
  unfold einastoCore
  apply mul_pos (by positivity)
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact ((continuous_id.pow 2).mul ((einastoDensity_continuous d l a).comp
      (continuous_const.mul continuous_id))).intervalIntegrable 0 1
  · intro u hu
    exact mul_pos (sq_pos_of_pos hu.1) (einastoDensity_pos d l a (exp t * u))
  · norm_num

/-- Mean enclosed density strictly exceeds the local boundary density. -/
theorem einastoCore_local_density_strict (d l a t : ℝ) :
    4 * Real.pi * einastoDensity d l a (exp t) / 3 < einastoCore d l a (exp t) := by
  have hf : Continuous (fun u : ℝ => u ^ 2 * einastoDensity d l a (exp t * u)) :=
    (continuous_id.pow 2).mul ((einastoDensity_continuous d l a).comp (continuous_const.mul continuous_id))
  have hg : Continuous (fun u : ℝ => u ^ 2 * einastoDensity d l a (exp t)) :=
    (continuous_id.pow 2).mul continuous_const
  have hpos : 0 < ∫ u in (0 : ℝ)..1,
      (u ^ 2 * einastoDensity d l a (exp t * u) - u ^ 2 * einastoDensity d l a (exp t)) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on ((hf.sub hg).intervalIntegrable 0 1)
    · intro u hu
      apply sub_pos.mpr
      apply mul_lt_mul_of_pos_left _ (sq_pos_of_pos hu.1)
      exact einastoDensity_strictAntiOn d l a (mem_Ici.mpr (mul_nonneg (exp_pos t).le hu.1.le)) (mem_Ici.mpr (exp_pos t).le)
        (by nlinarith [exp_pos t, mul_pos (exp_pos t) (sub_pos.mpr hu.2)])
    · norm_num
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable 0 1) (hg.intervalIntegrable 0 1),
    intervalIntegral.integral_mul_const, integral_pow] at hpos
  norm_num at hpos
  have h := mul_lt_mul_of_pos_left hpos (by positivity : 0 < 4 * Real.pi)
  unfold einastoCore
  nlinarith

theorem einastoCore_strictAnti (d l a : ℝ) : StrictAnti (fun t => einastoCore d l a (exp t)) := by
  intro s t hst
  have hc (v : ℝ) : Continuous (fun u : ℝ => u ^ 2 * einastoDensity d l a (exp v * u)) :=
    (continuous_id.pow 2).mul ((einastoDensity_continuous d l a).comp (continuous_const.mul continuous_id))
  have hi := intervalIntegral.intervalIntegral_pos_of_pos_on
    (((hc s).sub (hc t)).intervalIntegrable 0 1) (fun u (hu : u ∈ Ioo (0 : ℝ) 1) => ?_) (by norm_num : (0 : ℝ) < 1)
  · change 0 < ∫ u in (0 : ℝ)..1,
      (u ^ 2 * einastoDensity d l a (exp s * u) - u ^ 2 * einastoDensity d l a (exp t * u)) at hi
    rw [intervalIntegral.integral_sub ((hc s).intervalIntegrable 0 1) ((hc t).intervalIntegrable 0 1)] at hi
    exact mul_lt_mul_of_pos_left (sub_pos.mp hi) (by positivity : 0 < 4 * Real.pi)
  · apply sub_pos.mpr
    apply mul_lt_mul_of_pos_left _ (sq_pos_of_pos hu.1)
    exact einastoDensity_strictAntiOn d l a (mem_Ici.mpr (mul_nonneg (exp_pos s).le hu.1.le)) (mem_Ici.mpr (mul_nonneg (exp_pos t).le hu.1.le))
      (mul_lt_mul_of_pos_right (exp_lt_exp.mpr hst) hu.1)

theorem einastoInformationCurvature_metric (d l a t : ℝ) :
    einastoInformationCurvature d l a (exp t) =
      (1 - einastoMetric d l a (exp t)) / exp t ^ 2 := by
  rw [einastoInformationCurvature, einastoMetric_core]
  field_simp
  ring

/-- An inverse-cube law becomes regular when its source is actual enclosed information. -/
theorem einastoInformationCurvature_scaling (c d l a t : ℝ) :
    einastoInformationCurvature d l a (exp t) =
      2 * exp (-c) * einastoEnclosedInformation c d l a (exp t) / exp t ^ 3 := by
  rw [einastoEnclosedInformation, einastoMass_core, einastoInformationCurvature, exp_neg]
  field_simp

theorem einastoInformationCurvature_continuous (d l a : ℝ) : Continuous (einastoInformationCurvature d l a) :=
  continuous_const.mul (einastoCore_continuous d l a)

theorem einastoInformationCurvature_core (d l a : ℝ) :
    einastoInformationCurvature d l a 0 = 8 * Real.pi * exp d / 3 := by
  rw [einastoInformationCurvature, einastoCore_zero]
  ring

theorem einastoInformationCurvature_strictAnti (d l a : ℝ) :
    StrictAnti (fun t => einastoInformationCurvature d l a (exp t)) := by
  intro s t hst
  exact mul_lt_mul_of_pos_left (einastoCore_strictAnti d l a hst) (by norm_num : (0 : ℝ) < 2)

theorem einastoInformationCurvature_derivative (d l a t : ℝ) :
    HasDerivAt (einastoInformationCurvature d l a)
      ((8 * Real.pi * einastoDensity d l a (exp t) - 3 * einastoInformationCurvature d l a (exp t)) /
        exp t) (exp t) := by
  have h := ((einastoMass_derivative d l a (exp t)).const_mul 2).div
    ((hasDerivAt_id (exp t)).pow 3) (pow_ne_zero 3 (exp_ne_zero t))
  have hd : HasDerivAt (fun r => 2 * einastoMass d l a r / r ^ 3)
      ((8 * Real.pi * einastoDensity d l a (exp t) - 3 * einastoInformationCurvature d l a (exp t)) /
        exp t) (exp t) := by
    apply h.congr_deriv
    dsimp
    rw [einastoMass_core, einastoInformationCurvature]
    field_simp
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  rw [einastoMass_core, einastoInformationCurvature]
  field_simp

theorem einastoInformationCurvature_derivative_neg (d l a t : ℝ) :
    deriv (einastoInformationCurvature d l a) (exp t) < 0 := by
  rw [(einastoInformationCurvature_derivative d l a t).deriv]
  apply div_neg_of_neg_of_pos _ (exp_pos t)
  have h := einastoCore_local_density_strict d l a t
  unfold einastoInformationCurvature
  linarith

theorem einastoInformationCurvature_zero_at_infinity (d l a : ℝ) :
    Tendsto (fun t => einastoInformationCurvature d l a (exp t)) atTop (𝓝 0) := by
  have hm := (einastoMass_total d l a).comp tendsto_exp_atTop
  have hr : Tendsto (fun t : ℝ => exp t ^ 3) atTop atTop := by
    simpa only [Function.comp_def, id_eq, show (3 : ℝ) = (3 : ℕ) by norm_num, exp_nat_mul] using tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3))
  have h := (hm.const_mul 2).div_atTop hr
  have heq : (fun t => einastoInformationCurvature d l a (exp t)) =
      (fun t => 2 * einastoMass d l a (exp t) / exp t ^ 3) := by
    funext t
    rw [einastoMass_core, einastoInformationCurvature]
    field_simp
  rw [heq]
  exact h

theorem einastoInformationCurvature_core_limit (d l a : ℝ) :
    Tendsto (einastoInformationCurvature d l a) (𝓝 0) (𝓝 (8 * Real.pi * exp d / 3)) := by
  simpa only [einastoInformationCurvature_core] using
    (einastoInformationCurvature_continuous d l a).continuousAt.tendsto (x := 0)

/-- Every positive radius lies strictly below the finite central curvature. -/
theorem einastoInformationCurvature_global_bounds (d l a t : ℝ) :
    0 < einastoInformationCurvature d l a (exp t) ∧
      einastoInformationCurvature d l a (exp t) < 8 * Real.pi * exp d / 3 := by
  refine ⟨mul_pos (by norm_num) (einastoCore_pos d l a t), ?_⟩
  have hf : Continuous (fun u : ℝ => u ^ 2 * einastoDensity d l a (exp t * u)) :=
    (continuous_id.pow 2).mul ((einastoDensity_continuous d l a).comp (continuous_const.mul continuous_id))
  have hg : Continuous (fun u : ℝ => u ^ 2 * exp d) := (continuous_id.pow 2).mul continuous_const
  have hi : 0 < ∫ u in (0 : ℝ)..1, (u ^ 2 * exp d - u ^ 2 * einastoDensity d l a (exp t * u)) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on ((hg.sub hf).intervalIntegrable 0 1)
    · intro u hu
      apply sub_pos.mpr
      apply mul_lt_mul_of_pos_left _ (sq_pos_of_pos hu.1)
      rw [← einastoDensity_zero d l a]
      exact einastoDensity_strictAntiOn d l a (mem_Ici.mpr le_rfl)
        (mem_Ici.mpr (mul_nonneg (exp_pos t).le hu.1.le)) (mul_pos (exp_pos t) hu.1)
    · norm_num
  rw [intervalIntegral.integral_sub (hg.intervalIntegrable 0 1) (hf.intervalIntegrable 0 1),
    intervalIntegral.integral_mul_const, integral_pow] at hi
  norm_num at hi
  have h := mul_lt_mul_of_pos_left hi (by positivity : 0 < 8 * Real.pi)
  unfold einastoInformationCurvature einastoCore
  nlinarith

theorem einastoEnclosedInformation_derivative (c d l a r : ℝ) :
    HasDerivAt (einastoEnclosedInformation c d l a)
      (4 * Real.pi * exp c * r ^ 2 * einastoDensity d l a r) r := by
  exact ((einastoMass_derivative d l a r).const_mul (exp c)).congr_deriv (by ring)

/-- A ceiling holds at every positive radius exactly when it holds at the center. -/
theorem einastoInformationCurvature_global_cap_iff (d l a ell : ℝ) :
    (∀ t, einastoInformationCurvature d l a (exp t) ≤ exp (-2 * ell)) ↔
      8 * Real.pi * exp d / 3 ≤ exp (-2 * ell) := by
  constructor
  · intro h
    exact le_of_tendsto' ((einastoInformationCurvature_core_limit d l a).comp tendsto_exp_atBot) h
  · intro h t
    exact (einastoInformationCurvature_global_bounds d l a t).2.le.trans h

end GaloisForLFunctions.HTGeometry

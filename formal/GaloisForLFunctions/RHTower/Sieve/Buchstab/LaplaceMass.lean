import GaloisForLFunctions.RHTower.Sieve.Buchstab.GlobalDelay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Laplace mass of the real Buchstab profile

Boundedness makes the Laplace transform differentiable on the positive
ray. Rescaling the integration variable shows that its residue at zero
is precisely the common limit of the real cells.
-/

namespace RHTower.Sieve.Buchstab
open Set MeasureTheory Filter Topology
noncomputable section

def laplaceMass (s : ℝ) : ℝ := ∫ t in Ioi (0:ℝ), buchstab t * Real.exp (-s*t)

theorem laplace_integrable {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t => buchstab t * Real.exp (-s*t)) (Ioi (0:ℝ)) := by
  refine (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mono'
    ((measurable_buchstab.mul (by fun_prop)).aestronglyMeasurable) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (buchstab_mem_unit t).1 (Real.exp_pos _).le)]
  simpa using mul_le_mul_of_nonneg_right (buchstab_mem_unit t).2 (Real.exp_pos (-s*t)).le

/-- The transform is squeezed between zero and the transform of the constant upper bound. -/
theorem laplaceMass_bounds (s : Ioi (0:ℝ)) : laplaceMass s ∈ Icc 0 s.val⁻¹ := by
  constructor
  · exact integral_nonneg fun t => mul_nonneg (buchstab_mem_unit t).1 (Real.exp_pos _).le
  · have h := integral_mono (laplace_integrable s.property) (integrableOn_exp_mul_Ioi
      (neg_lt_zero.mpr s.property) 0) (fun t => show buchstab t * Real.exp (-s.val*t) ≤
        Real.exp (-s.val*t) by simpa using mul_le_mul_of_nonneg_right (buchstab_mem_unit t).2
          (Real.exp_pos (-s.val*t)).le)
    simpa [laplaceMass,integral_exp_mul_Ioi (neg_lt_zero.mpr s.property),one_div] using h

theorem tendsto_laplaceMass_atTop : Tendsto laplaceMass atTop (𝓝 0) := by
  apply squeeze_zero' _ _ tendsto_inv_atTop_zero
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
    exact (laplaceMass_bounds ⟨s,hs⟩).1
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
    exact (laplaceMass_bounds ⟨s,hs⟩).2

theorem linearWeight_integrable {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => t*Real.exp (-s*t)) (Ioi (0:ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := s)
    (by norm_num) le_rfl hs
  simpa [Real.rpow_one] using h

/-- Parameter differentiation inserts the first moment of the profile. -/
theorem hasDerivAt_laplaceMass (s : Ioi (0:ℝ)) :
    HasDerivAt laplaceMass (∫ t in Ioi (0:ℝ), -(t*buchstab t*Real.exp (-s.val*t))) s.val := by
  have hs : 0 < s.val := s.property
  have hh : 0 < s.val/2 := half_pos hs
  let f := fun (z t : ℝ) => buchstab t * Real.exp (-z*t)
  let df := fun (z t : ℝ) => -(t * buchstab t * Real.exp (-z*t))
  let b := fun t : ℝ => t*Real.exp (-(s.val/2)*t)
  have hi : IntegrableOn b (Ioi (0:ℝ)) := linearWeight_integrable hh
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := f) (F' := df)
    (μ := volume.restrict (Ioi (0:ℝ))) (bound := b) (Ioi_mem_nhds (half_lt_self hs))
    (Eventually.of_forall fun z => (measurable_buchstab.mul (by fun_prop)).aestronglyMeasurable)
    (laplace_integrable hs) ((measurable_id.mul measurable_buchstab |>.mul (by fun_prop)).neg.aestronglyMeasurable)
    _ hi _).2
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0:ℝ)))] with t ht z hz
    have ht0 : 0 ≤ t := le_of_lt ht
    have h₁ := mul_le_mul_of_nonneg_left (buchstab_mem_unit t).2 ht0
    have h₂ : Real.exp (-z*t) ≤ Real.exp (-(s.val/2)*t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (le_of_lt hz)) ht0)
    simp only [df,b,Real.norm_eq_abs,abs_neg,abs_of_nonneg (mul_nonneg
      (mul_nonneg ht0 (buchstab_mem_unit t).1) (Real.exp_pos _).le)]
    exact mul_le_mul (by simpa using h₁) h₂ (Real.exp_pos _).le ht0
  · filter_upwards with t z _
    have h := (((hasDerivAt_id z).neg.mul_const t).exp).const_mul (buchstab t)
    exact h.congr_deriv (by dsimp [df]; ring)

/-- Abelian identification of the residue, independent of the special-function formula. -/
theorem tendsto_scaled_laplaceMass :
    Tendsto (fun s => s * laplaceMass s) (𝓝[>] 0) (𝓝 enclosureLimit) := by
  let F := fun (s t : ℝ) => buchstab (s⁻¹*t) * Real.exp (-t)
  have hd : Tendsto (fun s => ∫ t in Ioi (0:ℝ), F s t) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0:ℝ), enclosureLimit * Real.exp (-t))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => Real.exp (-t))
    · exact Eventually.of_forall fun s => ((measurable_buchstab.comp (by fun_prop)).mul
        (by fun_prop)).aestronglyMeasurable
    · exact Eventually.of_forall fun s => Eventually.of_forall fun t => by
        dsimp [F]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (buchstab_mem_unit _).1 (Real.exp_pos _).le)]
        simpa using mul_le_mul_of_nonneg_right (buchstab_mem_unit (s⁻¹*t)).2 (Real.exp_pos (-t)).le
    · simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0
    · filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0:ℝ)))] with t ht
      exact (tendsto_buchstab_atTop.comp (tendsto_inv_nhdsGT_zero.atTop_mul_const ht)).mul_const _
  have h1 : (∫ t in Ioi (0:ℝ), Real.exp (-t)) = 1 := by
    simpa using integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0
  rw [integral_const_mul,h1,mul_one] at hd
  refine hd.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hp : 0 < s := hs
  have h := integral_comp_mul_left_Ioi (fun t => buchstab t * Real.exp (-s*t)) 0 (inv_pos.mpr hp)
  rw [mul_zero,inv_inv,smul_eq_mul] at h
  apply Eq.trans _ h
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  change buchstab (s⁻¹*t) * Real.exp (-t) = buchstab (s⁻¹*t) * Real.exp (-s*(s⁻¹*t))
  rw [show -s*(s⁻¹*t) = -t by field_simp [hp.ne']]

#print axioms hasDerivAt_laplaceMass
#print axioms tendsto_scaled_laplaceMass

end
end RHTower.Sieve.Buchstab

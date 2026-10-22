import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceOnsetJets

/-! The derivative of the fixed smooth source onset has its genuine Laplace transform. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMModularCore GaloisForLFunctions.HTGeometry
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem onset_weight (v w : ℂ) (u : ℝ) :
    Complex.exp (-w*(u:ℂ))*timeOnset v u =
      (Real.smoothTransition u:ℂ)*Complex.exp ((v-w)*(u:ℂ)) := by
  unfold timeOnset
  rw [mul_left_comm,← Complex.exp_add]
  congr 2
  ring

private theorem onsetFirst_weight (v w : ℂ) (u : ℝ) :
    Complex.exp (-w*(u:ℂ))*timeOnsetFirst v u =
      ((deriv Real.smoothTransition u:ℝ):ℂ)*Complex.exp ((v-w)*(u:ℂ))+
        v*((Real.smoothTransition u:ℂ)*Complex.exp ((v-w)*(u:ℂ))) := by
  unfold timeOnsetFirst
  rw [mul_left_comm,← Complex.exp_add]
  rw [show -w*(u:ℂ)+v*(u:ℂ)=(v-w)*(u:ℂ) by ring]
  ring

theorem timeOnset_integrable (v w : ℂ) (hw : v.re < w.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-w*(u:ℂ))*timeOnset v u) (Ioi 0) := by
  simpa only [onset_weight] using onsetTransform_integrable v w hw

theorem timeOnset_laplace (v w : ℂ) :
    (∫ u in Ioi (0:ℝ), Complex.exp (-w*(u:ℂ))*timeOnset v u) = onsetTransform v w := by
  simp only [onset_weight,onsetTransform]

theorem timeOnsetFirst_integrable (v w : ℂ) (hw : v.re < w.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-w*(u:ℂ))*timeOnsetFirst v u) (Ioi 0) := by
  have hE := integrableOn_exp_mul_complex_Ioi (a := v-w) (by simpa using sub_neg.mpr hw) 0
  obtain ⟨Λ,hΛ,hb⟩ := exists_bound_deriv_smoothTransition
  have hD : IntegrableOn (fun u : ℝ => ((deriv Real.smoothTransition u:ℝ):ℂ)*
      Complex.exp ((v-w)*(u:ℂ))) (Ioi 0) := by
    apply (hE.norm.const_mul Λ).mono' (by
      exact ((Complex.continuous_ofReal.comp continuous_deriv_smoothTransition).mul
        (by fun_prop)).aestronglyMeasurable)
    filter_upwards [] with u
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hb u) (norm_nonneg _)
  convert! hD.add ((onsetTransform_integrable v w hw).const_mul v) using 1
  ext u
  exact onsetFirst_weight v w u

/-- The surviving frequency factor differentiates the actual fixed onset, including its transition derivative. -/
theorem timeOnsetFirst_laplace (v w : ℂ) (hw : v.re < w.re) :
    (∫ u in Ioi (0:ℝ), Complex.exp (-w*(u:ℂ))*timeOnsetFirst v u) = w*onsetTransform v w := by
  let f := fun u : ℝ => Complex.exp (-w*(u:ℂ))*timeOnset v u
  have hd (u : ℝ) : HasDerivAt f
      (Complex.exp (-w*(u:ℂ))*timeOnsetFirst v u-
        w*(Complex.exp (-w*(u:ℂ))*timeOnset v u)) u := by
    have hE := ((hasDerivAt_id u).ofReal_comp.const_mul (-w)).cexp
    apply (hE.mul (timeOnset_hasDerivAt v u)).congr_deriv
    simp only [Complex.ofReal_one,mul_one,id_eq]
    ring
  have hi := (timeOnsetFirst_integrable v w hw).sub ((timeOnset_integrable v w hw).const_mul w)
  have hlim : Tendsto f atTop (𝓝 0) := by
    have hE : Tendsto (fun u : ℝ => Complex.exp ((v-w)*(u:ℂ))) atTop (𝓝 0) := by
      simpa [Complex.tendsto_exp_nhds_zero_iff] using
        tendsto_const_nhds.neg_mul_atTop (show (v-w).re < 0 by simpa using sub_neg.mpr hw) tendsto_id
    apply hE.congr'
    filter_upwards [eventually_ge_atTop (1:ℝ)] with u hu
    change Complex.exp ((v-w)*(u:ℂ)) = Complex.exp (-w*(u:ℂ))*timeOnset v u
    rw [onset_weight,Real.smoothTransition.one_of_one_le hu]
    simp
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' (fun u (_ : u ∈ Ici (0:ℝ)) => hd u) hi hlim
  rw [integral_sub (timeOnsetFirst_integrable v w hw) ((timeOnset_integrable v w hw).const_mul w),
    integral_const_mul,timeOnset_laplace] at he
  have hf : f 0 = 0 := by simp [f,timeOnset_zero_of_nonpos v le_rfl]
  rw [hf,sub_zero] at he
  exact sub_eq_zero.mp he

end
end RHTower.D4BMJointSource

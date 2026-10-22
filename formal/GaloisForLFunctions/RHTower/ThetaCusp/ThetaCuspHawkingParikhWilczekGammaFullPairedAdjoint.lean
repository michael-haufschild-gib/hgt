import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaAdjointGainTransposition

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology
noncomputable section

private def pwGammaPairedTail (d : ℝ) : ℂ := ∫h in Ioi d, ((Real.exp (-h)/h:ℝ):ℂ)

private theorem pwGammaPairedTail_real_integrable {d : ℝ} (hd : 0<d) :
    IntegrableOn (fun h : ℝ => Real.exp (-h)/h) (Ioi d) := by
  apply ((integrableOn_exp_neg_Ioi d).div_const d).mono'
    (show Measurable (fun h : ℝ => Real.exp (-h)/h) by fun_prop).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  have hh0 := hd.trans hh
  rw [Real.norm_of_nonneg (by positivity : 0≤Real.exp (-h)/h)]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hd hh.le

private theorem pwGammaPairedTail_integrable {d : ℝ} (hd : 0<d) :
    IntegrableOn (fun h : ℝ => ((Real.exp (-h)/h:ℝ):ℂ)) (Ioi d) :=
  (pwGammaPairedTail_real_integrable hd).ofReal

private theorem pwGammaPaired_forward_point (z v : ℂ) (x h : ℝ) :
    pwGammaMobiusForwardPairKernel z v (x,h) = pwGammaMobiusForwardGainDensity z v x (x+h)-
      pwGammaMobiusReversiblePairDensity z v x*((Real.exp (-h)/h:ℝ):ℂ) := by
  unfold pwGammaMobiusForwardPairKernel pwGammaMobiusForwardResponse
    pwGammaMobiusForwardGainDensity pwGammaForwardJumpRate pwGammaMobiusReversiblePairDensity
  dsimp only
  rw [add_sub_cancel_left]
  push_cast
  ring

private theorem pwGammaPaired_forward_section (z v : ℂ) {x d : ℝ} (hx : 0<x) (hd : 0<d) :
    (∫h in Ioi d, pwGammaMobiusForwardPairKernel z v (x,h)) =
      (∫h in Ioi d, pwGammaMobiusForwardGainDensity z v x (x+h))-
        pwGammaMobiusReversiblePairDensity z v x*pwGammaPairedTail d := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun h _ => pwGammaPaired_forward_point z v x h),
    integral_sub (pwGammaMobiusForwardGainDensity_section_integrable z v hd hx)
      ((pwGammaPairedTail_integrable hd).const_mul (pwGammaMobiusReversiblePairDensity z v x)),
    integral_const_mul]
  rfl

private theorem pwGammaPaired_forward_cutoff (z v : ℂ) {d : ℝ} (hd : 0<d) :
    (∫x in Ioi (0:ℝ), ∫h in Ioi d, pwGammaMobiusForwardPairKernel z v (x,h)) =
      (∫x in Ioi (0:ℝ), ∫h in Ioi d, pwGammaMobiusForwardGainDensity z v x (x+h))-
      (∫x in Ioi (0:ℝ), pwGammaMobiusReversiblePairDensity z v x)*pwGammaPairedTail d := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => pwGammaPaired_forward_section z v hx hd),
    integral_sub (pwGammaMobiusForwardGainDensity_outer_admission z v hd).1
      ((pwGammaMobiusReversiblePairDensity_integrable z v).mul_const (pwGammaPairedTail d)),
    integral_mul_const]

private theorem pwGammaPaired_backward_gain_section (z v : ℂ) {x a : ℝ} (hx : 0<x) (ha : 0<a) :
    (pwGammaReversibleDensity x:ℂ)*(pwGammaMobiusTilt v x/pwGammaRaySource x)*
      (∫h in Ioi a, ((Real.exp (-h)/h:ℝ):ℂ)*(starRingEnd ℂ)
        (pwGammaMobiusTilt z (1/(1/x+h))/pwGammaRaySource (1/(1/x+h)))) =
      (∫h in Ioi a, pwGammaMobiusAdjointResponseKernel z v (x,h))+
        pwGammaMobiusReversiblePairDensity z v x*pwGammaPairedTail a := by
  have hr : IntegrableOn (fun h => (starRingEnd ℂ) (pwGammaMobiusReciprocalResponse z (1/x) h))
      (Ioi a) := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp
        ((pwGammaMobiusReciprocalResponse_integrable z (show 0<1/x by positivity)).mono_set (Ioi_subset_Ioi ha.le))
  rw [setIntegral_congr_fun measurableSet_Ioi (fun h _ => pwGammaMobiusBackwardGain_decomposition z x h),
    integral_add hr ((pwGammaPairedTail_integrable ha).mul_const
      ((starRingEnd ℂ) (pwGammaMobiusTilt z x/pwGammaRaySource x))),integral_mul_const]
  unfold pwGammaMobiusAdjointResponseKernel pwGammaMobiusReversiblePairDensity pwGammaPairedTail
  dsimp only
  rw [integral_const_mul]
  ring

private theorem pwGammaPaired_tail_contact {x d : ℝ} (hx : 0<x) (hd : 0<d) (hdx : d<x) :
    pwGammaPairedTail (pwGammaAdjointCutoffLower x d) =
      (pwGammaAdjointCutoffContact x d:ℂ)+pwGammaPairedTail d := by
  have ht := intervalIntegral.integral_interval_add_Ioi
    (pwGammaPairedTail_real_integrable (pwGammaAdjointCutoffLower_pos hx hd hdx))
    (pwGammaPairedTail_real_integrable hd)
  unfold pwGammaPairedTail
  rw [integral_complex_ofReal,integral_complex_ofReal]
  exact_mod_cast ht.symm

private theorem pwGammaPaired_transported_section (z v : ℂ) {x d : ℝ} (hx : 0<x) (hd : 0<d) (hdx : d<x) :
    (pwGammaReversibleDensity x:ℂ)*(pwGammaMobiusTilt v x/pwGammaRaySource x)*
      (∫h in Ioi (pwGammaAdjointCutoffLower x d), ((Real.exp (-h)/h:ℝ):ℂ)*(starRingEnd ℂ)
        (pwGammaMobiusTilt z (1/(1/x+h))/pwGammaRaySource (1/(1/x+h)))) =
      (∫h in Ioi d, pwGammaMobiusAdjointResponseKernel z v (x,h))+
      (∫h in (pwGammaAdjointCutoffLower x d)..d, pwGammaMobiusAdjointResponseKernel z v (x,h))+
      pwGammaMobiusReversiblePairDensity z v x*(pwGammaAdjointCutoffContact x d:ℂ)+
      pwGammaMobiusReversiblePairDensity z v x*pwGammaPairedTail d := by
  have ha := pwGammaAdjointCutoffLower_pos hx hd hdx
  have hi := pwGammaMobiusAdjointResponseKernel_section_integrable z v hx
  have ht := intervalIntegral.integral_interval_add_Ioi
    (hi.mono_set (Ioi_subset_Ioi ha.le)) (hi.mono_set (Ioi_subset_Ioi hd.le))
  rw [pwGammaPaired_backward_gain_section z v hx ha,pwGammaPaired_tail_contact hx hd hdx,← ht]
  ring

theorem pwGammaMobiusPaired_original_cutoff_identity (z v : ℂ) {d : ℝ} (hd : 0<d) (hd1 : d≤1) :
    (∫x in Ioi (0:ℝ), ∫h in Ioi d, pwGammaMobiusForwardPairKernel z v (x,h)) =
      (∫x in Ioi d, ∫h in Ioi d, pwGammaMobiusAdjointResponseKernel z v (x,h))+
      (∫x in Ioi d, ∫h in (pwGammaAdjointCutoffLower x d)..d,
        pwGammaMobiusAdjointResponseKernel z v (x,h))+
      ((∫x in Ioi d, pwGammaMobiusReversiblePairDensity z v x*(pwGammaAdjointCutoffContact x d:ℂ))-
        pwGammaAdjointEmptyIncomingLoss (pwGammaMobiusReversiblePairDensity z v) d) := by
  have hR := (pwGammaMobiusAdjointResponseKernel_cutoff_admission z v hd).1
  have hE := pwGammaMobiusAdjointResponseKernel_mismatch_integrable z v hd
  have hC := (pwGammaMobiusReversiblePairDensity_contact_admission z v hd hd1).1
  have hP := pwGammaMobiusReversiblePairDensity_integrable z v
  have hPd : IntegrableOn (pwGammaMobiusReversiblePairDensity z v) (Ioi d) :=
    hP.mono_set (Ioi_subset_Ioi hd.le)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hP hPd
  rw [pwGammaPaired_forward_cutoff z v hd,pwGammaMobiusForwardGainDensity_full_transposition z v hd]
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x hx => pwGammaPaired_transported_section z v (hd.trans hx) hd hx)]
  have hRE := integral_add hR hE
  have hREC := integral_add (hR.add hE) hC
  have hALL := integral_add ((hR.add hE).add hC) (hPd.mul_const (pwGammaPairedTail d))
  simp only [Pi.add_apply] at hRE hREC hALL
  rw [hALL,hREC,hRE,integral_mul_const]
  unfold pwGammaAdjointEmptyIncomingLoss
  rw [← hsplit]
  unfold pwGammaPairedTail
  rw [integral_complex_ofReal]
  ring


/-- Full original-source paired adjoint, retaining the logarithmic contact. -/
theorem pwGammaMobiusPaired_original_adjoint (z v : ℂ) :
    (∫x in Ioi (0:ℝ), (pwGammaReversibleDensity x:ℂ)*
      (starRingEnd ℂ) (pwGammaMobiusTilt z x/pwGammaRaySource x)*
      (pwGammaMobiusTiltCurrent v x/pwGammaRaySource x)) =
      (∫x in Ioi (0:ℝ), ∫h in Ioi (0:ℝ), pwGammaMobiusAdjointResponseKernel z v (x,h))+
      (∫x in Ioi (0:ℝ), pwGammaMobiusReversiblePairDensity z v x*(2*Real.log x:ℝ)) := by
  have hA := pwGammaMobiusForwardPairKernel_cutoff_tendsto z v
  have hR := ((pwGammaMobiusAdjointResponseKernel_native_tendsto z v).add
    (pwGammaMobiusAdjointResponseKernel_mismatch_tendsto z v)).add
    (pwGammaMobiusReversiblePairDensity_original_contact_tendsto z v)
  simp only [add_zero] at hR
  have hd : Tendsto (fun d : ℝ => d) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have he : (fun d =>
      (∫x in Ioi d, ∫h in Ioi d, pwGammaMobiusAdjointResponseKernel z v (x,h))+
      (∫x in Ioi d, ∫h in (pwGammaAdjointCutoffLower x d)..d, pwGammaMobiusAdjointResponseKernel z v (x,h))+
      ((∫x in Ioi d, pwGammaMobiusReversiblePairDensity z v x*(pwGammaAdjointCutoffContact x d:ℂ))-
        pwGammaAdjointEmptyIncomingLoss (pwGammaMobiusReversiblePairDensity z v) d)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun d => ∫x in Ioi (0:ℝ), ∫h in Ioi d, pwGammaMobiusForwardPairKernel z v (x,h)) := by
    filter_upwards [self_mem_nhdsWithin,hd.eventually (gt_mem_nhds (show (0:ℝ)<1 by positivity))] with d hd0 hd1
    exact (pwGammaMobiusPaired_original_cutoff_identity z v hd0 hd1.le).symm
  exact tendsto_nhds_unique hA (hR.congr' he)

/-- Both sides are the complete original arithmetic currents, with no cutoff or balance premise. -/
theorem pwGammaMobiusPaired_original_current_adjoint (z v : ℂ) :
    (∫x in Ioi (0:ℝ), (pwGammaReversibleDensity x:ℂ)*
      (starRingEnd ℂ) (pwGammaMobiusTilt z x/pwGammaRaySource x)*
      (pwGammaMobiusTiltCurrent v x/pwGammaRaySource x)) =
      (∫x in Ioi (0:ℝ), (pwGammaReversibleDensity x:ℂ)*(pwGammaMobiusTilt v x/pwGammaRaySource x)*
        (starRingEnd ℂ) (pwGammaMobiusSameSourceCurrent z (1/x)/pwGammaRaySource (1/x)))+
      (∫x in Ioi (0:ℝ), pwGammaMobiusReversiblePairDensity z v x*(2*Real.log x:ℝ)) := by
  rw [pwGammaMobiusPaired_original_adjoint z v]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : 0<x := hx
  dsimp only
  rw [pwGammaMobiusAdjointResponseKernel_ray_eq,pwGammaMobiusReciprocalResponse_integral_eq z
    (show 0<1/x by positivity)]

theorem pwGammaMobiusPaired_original_current_admission (z v : ℂ) :
    IntegrableOn (fun x => (pwGammaReversibleDensity x:ℂ)*
      (starRingEnd ℂ) (pwGammaMobiusTilt z x/pwGammaRaySource x)*
      (pwGammaMobiusTiltCurrent v x/pwGammaRaySource x)) (Ioi 0) ∧
    IntegrableOn (fun x => (pwGammaReversibleDensity x:ℂ)*(pwGammaMobiusTilt v x/pwGammaRaySource x)*
      (starRingEnd ℂ) (pwGammaMobiusSameSourceCurrent z (1/x)/pwGammaRaySource (1/x))) (Ioi 0) ∧
    IntegrableOn (fun x => pwGammaMobiusReversiblePairDensity z v x*(2*Real.log x:ℝ)) (Ioi 0) := by
  refine ⟨pwGammaMobiusForwardPair_original_integrable z v,?_,?_⟩
  · apply (pwGammaMobiusAdjoint_original_response_integrable z v).congr_fun _ measurableSet_Ioi
    intro x hx
    have hx0 : 0<x := hx
    dsimp only
    rw [pwGammaMobiusReciprocalResponse_integral_eq z (show 0<1/x by positivity)]
  · exact (pwGammaMobiusReversiblePairDensity_contact_admission z v zero_lt_one le_rfl).2.2.2

end
end RHTower

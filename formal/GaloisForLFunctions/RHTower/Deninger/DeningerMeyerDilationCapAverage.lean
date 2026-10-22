import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerDilationAverage
import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonMellin
import GaloisForLFunctions.RHTower.Deninger.DeningerCommutatorExactKernel

/-! # Dilation averages stay in the actual Meyer cap

All-weight averaging preserves both radial endpoint conditions. Its Mellin
transform is the product of the logarithmic source transform and the
original cap transform. These are actual Schwartz averages.
-/

open Complex MeasureTheory Set Filter Topology SchwartzMap
open scoped FourierTransform

namespace RHTower
noncomputable section

theorem deningerMeyerDilationAverage_apply (h : DeningerMeyerStrongLogTarget)
    (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deningerMeyerDilationAverage h f x = ∫ t, h.val t*f (Real.exp (-t)*x) := by
  simp [deningerMeyerDilationAverage, deningerMeyerDilationAverageProfile,
    deningerMeyerDilationKernel]

private theorem dilation_mass_integrable (h : DeningerMeyerStrongLogTarget)
    (f : 𝓢(ℝ, ℂ)) :
    Integrable (fun p : ℝ × ℝ => h.val p.1*f (Real.exp (-p.1)*p.2))
      (volume.prod volume) := by
  have hc : Continuous (fun p : ℝ × ℝ => h.val p.1*f (Real.exp (-p.1)*p.2)) :=
    (h.property.smooth.continuous.comp continuous_fst).mul (f.continuous.comp (by fun_prop))
  refine (integrable_prod_iff hc.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · exact Eventually.of_forall fun t =>
      (f.integrable.comp_mul_left' (Real.exp_ne_zero (-t))).const_mul (h.val t)
  · have he : (fun t : ℝ => ∫ x : ℝ, ‖h.val t*f (Real.exp (-t)*x)‖) =
        fun t => (Real.exp t*‖h.val t‖)*(∫ x : ℝ, ‖f x‖) := by
      funext t
      simp_rw [norm_mul]
      rw [integral_const_mul,
        Measure.integral_comp_mul_left (fun x : ℝ => ‖f x‖) (Real.exp (-t))]
      simp only [Real.exp_neg, inv_inv, abs_of_pos (Real.exp_pos _), smul_eq_mul]
      ring
    rw [he]
    simpa only [one_mul] using
      (deningerMeyer_expWeight_integrable h 1).mul_const (∫ x : ℝ, ‖f x‖)

/-- All-weight averaging preserves the two exact endpoint cancellations. -/
theorem deningerMeyerDilationAverage_mem_cap (h : DeningerMeyerStrongLogTarget)
    (f : DeningerMeyerCap) : deningerMeyerDilationAverage h f.val ∈ DeningerMeyerCap := by
  obtain ⟨he, hzero, hfour⟩ := (deningerMeyerCap_mem_iff f.val).mp f.property
  refine (deningerMeyerCap_mem_iff _).mpr ⟨?_, ?_, ?_⟩
  · intro x
    simp only [deningerMeyerDilationAverage_apply, mul_neg, he]
  · simp [deningerMeyerDilationAverage_apply, hzero]
  · change 𝓕 ((deningerMeyerDilationAverage h f.val : 𝓢(ℝ, ℂ)) : ℝ → ℂ) 0 = 0
    rw [deningerFourier_at_zero]
    simp_rw [deningerMeyerDilationAverage_apply]
    rw [← integral_integral_swap (dilation_mass_integrable h f.val)]
    have hmass : (∫ x : ℝ, f.val x) = 0 := by
      change 𝓕 (f.val : ℝ → ℂ) 0 = 0 at hfour
      rwa [deningerFourier_at_zero] at hfour
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun t => by
      change (∫ x : ℝ, h.val t*f.val (Real.exp (-t)*x)) = 0
      rw [integral_const_mul, Measure.integral_comp_mul_left, hmass, smul_zero, mul_zero]

/-- An actual cap, formed by averaging genuine physical dilations. -/
def deningerMeyerDilationCapAverage (h : DeningerMeyerStrongLogTarget)
    (f : DeningerMeyerCap) : DeningerMeyerCap :=
  ⟨deningerMeyerDilationAverage h f.val, deningerMeyerDilationAverage_mem_cap h f⟩

private theorem dilation_mellin_integrable (h : DeningerMeyerStrongLogTarget)
    (f : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun p : ℝ × ℝ => (p.2 : ℂ)^(s-1)*
      (h.val p.1*f (Real.exp (-p.1)*p.2)))
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hpow := Complex.continuous_ofReal_cpow_const (y := s-1)
    (by simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr hs)
  have hc : Continuous (fun p : ℝ × ℝ => (p.2 : ℂ)^(s-1)*
      (h.val p.1*f (Real.exp (-p.1)*p.2))) :=
    (hpow.comp continuous_snd).mul
      ((h.property.smooth.continuous.comp continuous_fst).mul (f.continuous.comp (by fun_prop)))
  refine (integrable_prod_iff hc.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · filter_upwards with t
    have hi := ((MellinConvergent.comp_mul_left (Real.exp_pos (-t))).mpr
      (mellinConvergent_schwartz f (by linarith : 0 < s.re))).const_mul (h.val t)
    apply hi.congr
    filter_upwards with x
    change h.val t*((x:ℂ)^(s-1)*f (Real.exp (-t)*x)) =
      (x:ℂ)^(s-1)*(h.val t*f (Real.exp (-t)*x))
    ring
  · have he : (fun t : ℝ => ∫ x in Ioi (0:ℝ),
        ‖(x:ℂ)^(s-1)*(h.val t*f (Real.exp (-t)*x))‖) =
        fun t => (Real.exp (s.re*t)*‖h.val t‖)*
          (∫ x in Ioi (0:ℝ), x^(s.re-1)*‖f x‖) := by
      funext t
      have hpt : ∀ x ∈ Ioi (0:ℝ),
          ‖(x:ℂ)^(s-1)*(h.val t*f (Real.exp (-t)*x))‖ =
            ‖h.val t‖*(x^(s.re-1)*‖f (Real.exp (-t)*x)‖) := by
        intro x hx
        rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
        simp only [Complex.sub_re, Complex.one_re]
        ring
      rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
        integral_mellinNorm_comp_mul f (by linarith : 0 < s.re) (Real.exp_pos (-t)),
        Real.rpow_def_of_pos (Real.exp_pos (-t)), Real.log_exp]
      rw [show -t * -s.re = s.re*t by ring]
      ring
    rw [he]
    exact (deningerMeyer_expWeight_integrable h s.re).mul_const _

/-- Exact Mellin multiplication for physical dilation averages. -/
theorem deningerMeyerDilationAverage_mellin
    (h : DeningerMeyerStrongLogTarget) (f : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 1 < s.re) :
    mellin (deningerMeyerDilationAverage h f) s =
      deningerMeyerStrongLogMellin h s * mellin f s := by
  change (∫ x in Ioi (0:ℝ), (x:ℂ)^(s-1)*deningerMeyerDilationAverage h f x) = _
  simp_rw [deningerMeyerDilationAverage_apply, ← integral_const_mul]
  rw [← integral_integral_swap (dilation_mellin_integrable h f hs)]
  have he (t : ℝ) : (Real.exp (-t) : ℂ)^(-s) = Complex.exp (s*t) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
      ← Complex.ofReal_log (Real.exp_pos (-t)).le, Real.log_exp]
    congr 1
    push_cast
    ring
  have hint (t : ℝ) : (∫ x in Ioi (0:ℝ),
      (x:ℂ)^(s-1)*(h.val t*f (Real.exp (-t)*x))) =
        (Complex.exp (s*t)*h.val t)*mellin f s := by
    calc (∫ x in Ioi (0:ℝ), (x:ℂ)^(s-1)*(h.val t*f (Real.exp (-t)*x)))
        = h.val t*mellin (fun x => f (Real.exp (-t)*x)) s := by
          rw [mellin, ← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with x
          simp only [smul_eq_mul]
          ring
      _ = _ := by
        rw [mellin_comp_mul_left _ _ (Real.exp_pos (-t)), he, smul_eq_mul]
        ring
  simp_rw [hint]
  rw [integral_mul_const]
  simp [deningerMeyerStrongLogMellin, deningerMeyerStrongLogMellinJet]

end
end RHTower

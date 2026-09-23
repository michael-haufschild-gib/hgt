import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusSameSourceKernel
import Mathlib.Analysis.Calculus.MeanValue

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology
noncomputable section

private theorem pwGammaFlat_exp_neg_bound (k : ℕ) {y : ℝ} (hy : 0<y) :
    Real.exp (-y) ≤ (k.factorial:ℝ)/y^k := by
  have hf : (0:ℝ)<k.factorial := by positivity
  have hb := Real.pow_div_factorial_le_exp y hy.le k
  rw [Real.exp_neg]
  apply (le_div_iff₀ (pow_pos hy k)).mpr
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ (Real.exp_pos y)).mpr
    (by simpa only [mul_comm] using (div_le_iff₀ hf).mp hb)

theorem pwGammaReciprocalExp_hasDerivAt {a v : ℝ} (hv : 0<v) :
    HasDerivAt (fun u : ℝ => Real.exp (-a/u))
      ((a/v^(2 : ℕ))*Real.exp (-a/v)) v := by
  have hd : HasDerivAt (fun u : ℝ => -a/u) (a/v^(2 : ℕ)) v := by
    simpa only [div_eq_mul_inv, neg_mul, mul_neg, neg_neg] using
      (hasDerivAt_inv hv.ne').const_mul (-a)
  simpa only [mul_comm] using hd.exp

theorem pwGammaReciprocalExp_derivative_bound (k : ℕ) {a v : ℝ}
    (ha : 0<a) (hv : 0<v) :
    (a/v^(2 : ℕ))*Real.exp (-a/v) ≤ (((k+2).factorial:ℝ)/a^(k+1))*v^k := by
  have he := pwGammaFlat_exp_neg_bound (k+2) (div_pos ha hv)
  calc
    _ ≤ (a/v^(2 : ℕ))*(((k+2).factorial:ℝ)/(a/v)^(k+2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [neg_div] using he
    _ = _ := by
      rw [div_pow, pow_add, pow_succ]
      field_simp; ring

/-- The complete difference is controlled without a reciprocal endpoint loss. -/
theorem pwGammaReciprocalTranslationKernel_flat_bound (k : ℕ) {a v h : ℝ}
    (ha : 0<a) (hv : 0<v) (hh : 0<h) :
    pwGammaReciprocalTranslationKernel a v h ≤
      (((k+2).factorial:ℝ)/a^(k+1))*Real.exp (-h)*(v+h)^k := by
  let C : ℝ := ((k+2).factorial:ℝ)/a^(k+1)
  have hC : 0≤C := by dsimp [C]; positivity
  have hd : ∀ u ∈ Icc v (v+h), HasDerivWithinAt (fun u : ℝ => Real.exp (-a/u))
      ((a/u^(2 : ℕ))*Real.exp (-a/u)) (Icc v (v+h)) u := by
    intro u hu
    exact (pwGammaReciprocalExp_hasDerivAt (hv.trans_le hu.1)).hasDerivWithinAt
  have hb : ∀ u ∈ Icc v (v+h), ‖(a/u^(2 : ℕ))*Real.exp (-a/u)‖ ≤ C*(v+h)^k := by
    intro u hu
    have hu0 := hv.trans_le hu.1
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ C*u^k := pwGammaReciprocalExp_derivative_bound k ha hu0
      _ ≤ C*(v+h)^k := by gcongr; exact hu.2
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc v (v+h))
    (show v ∈ Icc v (v+h) from ⟨le_rfl, by linarith⟩)
    (show v+h ∈ Icc v (v+h) from ⟨by linarith, le_rfl⟩)
  have hm' : |Real.exp (-a/(v+h))-Real.exp (-a/v)| ≤ C*(v+h)^k*h := by
    simpa only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hh] using hm
  have hdif := (le_abs_self (Real.exp (-a/(v+h))-Real.exp (-a/v))).trans hm'
  calc
    _ = Real.exp (-h)*((Real.exp (-a/(v+h))-Real.exp (-a/v))/h) := by
      rw [pwGammaReciprocalTranslationKernel]
      ring
    _ ≤ Real.exp (-h)*(C*(v+h)^k) :=
      mul_le_mul_of_nonneg_left ((div_le_iff₀ hh).mpr hdif) (Real.exp_pos _).le
    _ = _ := by dsimp [C]; ring

/-- Actual right-endpoint kernel; the written original formula at v=0 is different. -/
def pwGammaReciprocalEndpointKernel (a h : ℝ) : ℝ := Real.exp (-h-a/h)/h

theorem pwGammaReciprocalEndpointKernel_pos (a : ℝ) {h : ℝ} (hh : 0<h) :
    0<pwGammaReciprocalEndpointKernel a h := div_pos (Real.exp_pos _) hh

theorem pwGammaReciprocalEndpointKernel_bound (k : ℕ) {a h : ℝ}
    (ha : 0<a) (hh : 0<h) :
    pwGammaReciprocalEndpointKernel a h ≤
      (((k+1).factorial:ℝ)/a^(k+1))*Real.exp (-h)*h^k := by
  have he := pwGammaFlat_exp_neg_bound (k+1) (div_pos ha hh)
  calc
    _ = Real.exp (-h)*Real.exp (-a/h)/h := by
      rw [pwGammaReciprocalEndpointKernel, sub_eq_add_neg, Real.exp_add, neg_div]
    _ ≤ Real.exp (-h)*(((k+1).factorial:ℝ)/(a/h)^(k+1))/h := by
      gcongr
      simpa only [neg_div] using he
    _ = _ := by rw [div_pow, pow_succ]; field_simp; ring

private theorem pwGammaFlat_exp_tendsto_zero {a : ℝ} (ha : 0<a) :
    Tendsto (fun v : ℝ => Real.exp (-a/v)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hv : Tendsto (fun v : ℝ => v) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun v : ℝ => v/a) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Pi.div_def, zero_div] using hv.div_const a
  apply squeeze_zero' (Eventually.of_forall fun v => (Real.exp_pos _).le) _ ht
  filter_upwards [self_mem_nhdsWithin] with v hv0
  have he := pwGammaFlat_exp_neg_bound 1 (div_pos ha hv0)
  simpa only [neg_div, Nat.factorial_one, Nat.cast_one, pow_one, one_div_div] using he

theorem pwGammaReciprocalTranslationKernel_tendsto_endpoint {a h : ℝ}
    (ha : 0<a) (hh : 0<h) :
    Tendsto (fun v : ℝ => pwGammaReciprocalTranslationKernel a v h)
      (𝓝[>] (0:ℝ)) (𝓝 (pwGammaReciprocalEndpointKernel a h)) := by
  have hv : Tendsto (fun v : ℝ => v) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun v : ℝ => -a/(v+h)) (𝓝[>] (0:ℝ)) (𝓝 (-a/h)) := by
    simpa only [Pi.div_def, zero_add] using
      tendsto_const_nhds.div (hv.add_const h) (by simpa only [zero_add] using hh.ne')
  have he : Tendsto (fun v : ℝ => Real.exp (-a/(v+h))) (𝓝[>] (0:ℝ))
      (𝓝 (Real.exp (-a/h))) := (Real.continuous_exp.tendsto _).comp ht
  have hz := pwGammaFlat_exp_tendsto_zero ha
  have hr := ((he.sub hz).const_mul (Real.exp (-h))).div_const h
  change Tendsto (fun v : ℝ => Real.exp (-h)*(Real.exp (-a/(v+h))-Real.exp (-a/v))/h)
    (𝓝[>] (0:ℝ)) (𝓝 (Real.exp (-h-a/h)/h))
  simpa only [Pi.div_def, sub_eq_add_neg, Real.exp_add, neg_div, neg_zero, add_zero] using hr

theorem pwGammaReciprocalEndpointKernel_integrable {a : ℝ} (ha : 0<a) :
    IntegrableOn (pwGammaReciprocalEndpointKernel a) (Ioi 0) := by
  have hm : Measurable (pwGammaReciprocalEndpointKernel a) := by
    unfold pwGammaReciprocalEndpointKernel
    fun_prop
  apply Integrable.mono' ((integrableOn_exp_neg_Ioi 0).const_mul (1/a))
    hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  rw [Real.norm_of_nonneg (pwGammaReciprocalEndpointKernel_pos a hh).le]
  simpa only [Nat.zero_add, Nat.factorial_one, Nat.cast_one, pow_one, pow_zero, mul_one]
    using pwGammaReciprocalEndpointKernel_bound 0 ha hh

theorem pwGammaReciprocalEndpointKernel_integral_pos {a : ℝ} (ha : 0<a) :
    0 < ∫ h in Ioi (0 : ℝ), pwGammaReciprocalEndpointKernel a h := by
  have hp : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] pwGammaReciprocalEndpointKernel a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    exact (pwGammaReciprocalEndpointKernel_pos a hh).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hp (pwGammaReciprocalEndpointKernel_integrable ha)]
  have hs : Function.support (pwGammaReciprocalEndpointKernel a) ∩ Ioi (0 : ℝ) = Ioi 0 := by
    apply inter_eq_right.mpr
    intro h hh
    exact (pwGammaReciprocalEndpointKernel_pos a hh).ne'
  rw [hs]
  simp

/-- Convergence of the original source kernels in the actual integral norm. -/
theorem pwGammaReciprocalTranslationKernel_tendsto_endpoint_L1 {a : ℝ} (ha : 0<a) :
    Tendsto (fun v : ℝ => ∫ h in Ioi (0 : ℝ),
      ‖pwGammaReciprocalTranslationKernel a v h-pwGammaReciprocalEndpointKernel a h‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let C : ℝ := (2).factorial/a+1/a
  have hmeas : ∀ᶠ v : ℝ in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun h => ‖pwGammaReciprocalTranslationKernel a v h-pwGammaReciprocalEndpointKernel a h‖)
      (volume.restrict (Ioi 0)) := by
    apply Eventually.of_forall
    intro v
    have hm : Measurable (fun h =>
        ‖pwGammaReciprocalTranslationKernel a v h-pwGammaReciprocalEndpointKernel a h‖) := by
      unfold pwGammaReciprocalTranslationKernel pwGammaReciprocalEndpointKernel
      fun_prop
    exact hm.aestronglyMeasurable
  have hb : ∀ᶠ v : ℝ in 𝓝[>] (0 : ℝ), ∀ᵐ h ∂volume.restrict (Ioi (0 : ℝ)),
      ‖‖pwGammaReciprocalTranslationKernel a v h-pwGammaReciprocalEndpointKernel a h‖‖ ≤
        C*Real.exp (-h) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    rw [norm_norm]
    calc
      _ ≤ ‖pwGammaReciprocalTranslationKernel a v h‖+‖pwGammaReciprocalEndpointKernel a h‖ :=
        norm_sub_le _ _
      _ = pwGammaReciprocalTranslationKernel a v h+pwGammaReciprocalEndpointKernel a h := by
        rw [Real.norm_of_nonneg (pwGammaReciprocalTranslationKernel_nonneg ha.le hv hh),
          Real.norm_of_nonneg (pwGammaReciprocalEndpointKernel_pos a hh).le]
      _ ≤ ((2).factorial:ℝ)/a*Real.exp (-h)+(1/a)*Real.exp (-h) := by
        apply add_le_add
        · simpa only [Nat.zero_add, pow_one, pow_zero, mul_one] using
            pwGammaReciprocalTranslationKernel_flat_bound 0 ha hv hh
        · simpa only [Nat.zero_add, Nat.factorial_one, Nat.cast_one, pow_one, pow_zero, mul_one]
            using pwGammaReciprocalEndpointKernel_bound 0 ha hh
      _ = _ := by dsimp [C]; ring
  have hl : ∀ᵐ h ∂volume.restrict (Ioi (0 : ℝ)), Tendsto (fun v : ℝ =>
      ‖pwGammaReciprocalTranslationKernel a v h-pwGammaReciprocalEndpointKernel a h‖)
      (𝓝[>] (0 : ℝ)) (𝓝 ((fun _ : ℝ => (0:ℝ)) h)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    simpa only [sub_self, norm_zero] using
      ((pwGammaReciprocalTranslationKernel_tendsto_endpoint ha hh).sub_const
        (pwGammaReciprocalEndpointKernel a h)).norm
  have ht := tendsto_integral_filter_of_dominated_convergence
    (fun h => C*Real.exp (-h)) hmeas hb ((integrableOn_exp_neg_Ioi 0).const_mul C) hl
  simpa only [integral_zero] using ht

theorem pwGammaReciprocalTranslationKernel_tendsto_endpoint_integral {a : ℝ} (ha : 0<a) :
    Tendsto (fun v : ℝ => ∫ h in Ioi (0 : ℝ), pwGammaReciprocalTranslationKernel a v h)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ h in Ioi (0 : ℝ), pwGammaReciprocalEndpointKernel a h)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun h => ((2).factorial:ℝ)/a*Real.exp (-h))
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact (pwGammaReciprocalTranslationKernel_integrable ha.le hv).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with v hv
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    rw [Real.norm_of_nonneg (pwGammaReciprocalTranslationKernel_nonneg ha.le hv hh)]
    simpa only [Nat.zero_add, pow_one, pow_zero, mul_one] using
      pwGammaReciprocalTranslationKernel_flat_bound 0 ha hv hh
  · exact (integrableOn_exp_neg_Ioi 0).const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    exact pwGammaReciprocalTranslationKernel_tendsto_endpoint ha hh

private theorem pwGammaFlat_exp_moment_integrable (k : ℕ) :
    IntegrableOn (fun h : ℝ => h^k*Real.exp (-h)) (Ioi 0) := by
  have he := Real.GammaIntegral_convergent (s := (k : ℝ)+1) (by positivity)
  apply IntegrableOn.congr_fun he _ measurableSet_Ioi
  intro h hh
  change Real.exp (-h)*h^((k : ℝ)+1-1) = h^k*Real.exp (-h)
  rw [add_sub_cancel_right, Real.rpow_natCast]
  ring

theorem pwGammaFlatShiftedMoment_integrable (k : ℕ) :
    IntegrableOn (fun h : ℝ => Real.exp (-h)*(1+h)^k) (Ioi 0) := by
  have hi := ((integrableOn_exp_neg_Ioi 0).add
    (pwGammaFlat_exp_moment_integrable k)).const_mul ((2:ℝ)^(k-1))
  have hm : Measurable (fun h : ℝ => Real.exp (-h)*(1+h)^k) := by fun_prop
  apply Integrable.mono' hi hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  have hh0 : 0<h := hh
  rw [Real.norm_of_nonneg (by positivity)]
  have hb := add_pow_le (show (0:ℝ)≤1 by positivity) hh.le k
  calc
    _ ≤ Real.exp (-h)*((2:ℝ)^(k-1)*(1^k+h^k)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by simp only [one_pow, Pi.add_apply]; ring

theorem pwGammaReciprocalTranslationKernel_integral_flat_bound (k : ℕ) {a v : ℝ}
    (ha : 0<a) (hv : 0<v) (hv1 : v≤1) :
    (∫ h in Ioi (0 : ℝ), pwGammaReciprocalTranslationKernel a v h) ≤
      (((k+2).factorial:ℝ)/a^(k+1))*(∫ h in Ioi (0 : ℝ), Real.exp (-h)*(1+h)^k) := by
  rw [← integral_const_mul]
  apply setIntegral_mono_on (pwGammaReciprocalTranslationKernel_integrable ha.le hv)
    ((pwGammaFlatShiftedMoment_integrable k).const_mul _) measurableSet_Ioi
  intro h hh
  have hh0 : 0<h := hh
  calc
    _ ≤ (((k+2).factorial:ℝ)/a^(k+1))*Real.exp (-h)*(v+h)^k :=
      pwGammaReciprocalTranslationKernel_flat_bound k ha hv hh
    _ ≤ (((k+2).factorial:ℝ)/a^(k+1))*Real.exp (-h)*(1+h)^k := by gcongr
    _ = _ := by ring

theorem pwGammaReciprocalEndpointKernel_integral_flat_bound (k : ℕ) {a : ℝ}
    (ha : 0<a) :
    (∫ h in Ioi (0 : ℝ), pwGammaReciprocalEndpointKernel a h) ≤
      (((k+1).factorial:ℝ)/a^(k+1))*(∫ h in Ioi (0 : ℝ), Real.exp (-h)*(1+h)^k) := by
  rw [← integral_const_mul]
  apply setIntegral_mono_on (pwGammaReciprocalEndpointKernel_integrable ha)
    ((pwGammaFlatShiftedMoment_integrable k).const_mul _) measurableSet_Ioi
  intro h hh
  have hh0 : 0<h := hh
  calc
    _ ≤ (((k+1).factorial:ℝ)/a^(k+1))*Real.exp (-h)*h^k :=
      pwGammaReciprocalEndpointKernel_bound k ha hh
    _ ≤ (((k+1).factorial:ℝ)/a^(k+1))*Real.exp (-h)*(1+h)^k := by gcongr; linarith
    _ = _ := by ring


end
end RHTower

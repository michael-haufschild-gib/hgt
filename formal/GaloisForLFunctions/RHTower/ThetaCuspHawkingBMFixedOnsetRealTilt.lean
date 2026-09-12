import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOnsetPulseTransform

/-! Nonvanishing of the prescribed onset at large real tilts, with its original pulse retained. -/
namespace RHTower.D4BMModularCore
open Complex Set Filter Topology MeasureTheory intervalIntegral
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

private theorem transitionPulse_mass (a b : ℝ) :
    (∫ u in a..b, deriv Real.smoothTransition u) =
      Real.smoothTransition b-Real.smoothTransition a := by
  apply integral_deriv_eq_sub
  · intro u _
    exact ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)) u
  · exact continuous_deriv_smoothTransition.intervalIntegrable a b

private theorem terminal_phase (y : ℝ) :
    ∃ a : ℝ, 0<a ∧ a<1 ∧ ∀ u ∈ Icc a 1, 1/2 ≤ Real.cos (y*(u-1)) := by
  have hc : ContinuousAt (fun u : ℝ => Real.cos (y*(u-1))) 1 := by fun_prop
  have he : ∀ᶠ u : ℝ in 𝓝 1, 1/2 < Real.cos (y*(u-1)) :=
    hc.eventually (eventually_gt_nhds (by norm_num))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp he
  let d := min (δ/2) (1/2)
  have hd : 0<d := lt_min (half_pos hδ) (by norm_num)
  have hdδ : d<δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨1-d,by dsimp only [d]; linarith [min_le_right (δ/2) (1/2)],by linarith,?_⟩
  intro u hu
  have hdist : dist u 1 < δ := by
    rw [Real.dist_eq,abs_of_nonpos (by linarith [hu.2])]
    linarith [hu.1]
  exact (hball hdist).le

private theorem pulse_phase_lower (a b x y : ℝ)
    (ha : 0≤a) (hab : a≤b) (hb : b≤1) (hx : 0≤x)
    (hc : ∀ u ∈ Icc a 1, 1/2 ≤ Real.cos (y*(u-1))) :
    -Real.exp (x*a)+(1-Real.smoothTransition b)*Real.exp (x*b)/2 ≤
      ∫ u in (0:ℝ)..1,
        deriv Real.smoothTransition u*Real.exp (x*u)*Real.cos (y*(u-1)) := by
  let f := fun u : ℝ => deriv Real.smoothTransition u*Real.exp (x*u)*Real.cos (y*(u-1))
  have hp : ∀ u, 0≤deriv Real.smoothTransition u :=
    fun _ => Real.smoothTransition.monotone.deriv_nonneg
  have hf : Continuous f := by
    exact (continuous_deriv_smoothTransition.mul (by fun_prop)).mul (by fun_prop)
  have hleft : -Real.exp (x*a) ≤ ∫ u in (0:ℝ)..a, f u := by
    have h := integral_mono_on (μ := volume) ha
      ((continuous_deriv_smoothTransition.mul continuous_const).intervalIntegrable 0 a)
      (hf.intervalIntegrable 0 a)
      (show ∀ u ∈ Icc (0:ℝ) a,
        deriv Real.smoothTransition u*(-Real.exp (x*a)) ≤ f u from by
        intro u hu
        have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hx)
        have hs := Real.neg_one_le_cos (y*(u-1))
        have h1 := mul_le_mul_of_nonneg_left he (hp u)
        have h2 := mul_le_mul_of_nonneg_left hs
          (mul_nonneg (hp u) (Real.exp_pos (x*u)).le)
        dsimp only [f]
        nlinarith only [h1,h2])
    change (∫ u in (0:ℝ)..a, deriv Real.smoothTransition u*(-Real.exp (x*a))) ≤
      ∫ u in (0:ℝ)..a, f u at h
    rw [intervalIntegral.integral_mul_const,transitionPulse_mass,Real.smoothTransition.zero,sub_zero] at h
    have hmass := mul_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one a))
      (Real.exp_pos (x*a)).le
    nlinarith only [h,hmass]
  have hmid : 0≤∫ u in a..b, f u := by
    apply integral_nonneg hab
    intro u hu
    exact mul_nonneg (mul_nonneg (hp u) (Real.exp_pos (x*u)).le)
      (le_trans (by norm_num) (hc u ⟨hu.1,hu.2.trans hb⟩))
  have hright : (1-Real.smoothTransition b)*Real.exp (x*b)/2 ≤ ∫ u in b..1, f u := by
    have h := integral_mono_on (μ := volume) hb
      ((continuous_deriv_smoothTransition.mul continuous_const).intervalIntegrable b 1)
      (hf.intervalIntegrable b 1)
      (show ∀ u ∈ Icc b 1,
        deriv Real.smoothTransition u*(Real.exp (x*b)/2) ≤ f u from by
        intro u hu
        have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.1 hx)
        have h1 := mul_le_mul_of_nonneg_left he (hp u)
        have h2 := mul_le_mul_of_nonneg_left (hc u ⟨hab.trans hu.1,hu.2⟩)
          (mul_nonneg (hp u) (Real.exp_pos (x*u)).le)
        dsimp only [f]
        nlinarith only [h1,h2])
    change (∫ u in b..1, deriv Real.smoothTransition u*(Real.exp (x*b)/2)) ≤
      ∫ u in b..1, f u at h
    rw [intervalIntegral.integral_mul_const,transitionPulse_mass,Real.smoothTransition.one] at h
    nlinarith only [h]
  have hsplit := integral_add_adjacent_intervals (μ := volume) (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a b)
  have hsplit' := integral_add_adjacent_intervals (μ := volume) (hf.intervalIntegrable 0 b) (hf.intervalIntegrable b 1)
  change _ ≤ ∫ u in (0:ℝ)..1, f u
  linarith only [hleft,hmid,hright,hsplit,hsplit']

/-- The original pulse has strictly positive rotated real part for every sufficiently large
real tilt, at each fixed imaginary frequency. The duration is unchanged. -/
theorem onsetPulse_phase_integral_eventually_pos (y : ℝ) :
    ∃ R : ℝ, 0≤R ∧ ∀ x : ℝ, R≤x →
      0 < ∫ u in (0:ℝ)..1,
        deriv Real.smoothTransition u*Real.exp (x*u)*Real.cos (y*(u-1)) := by
  obtain ⟨a,ha0,ha1,hphase⟩ := terminal_phase y
  let b := (a+1)/2
  have hab : a<b := by dsimp only [b]; linarith
  have hb1 : b<1 := by dsimp only [b]; linarith
  let c := 1-Real.smoothTransition b
  have hc : 0<c := sub_pos.mpr (Real.smoothTransition.lt_one_of_lt_one hb1)
  have hδ : 0<b-a := sub_pos.mpr hab
  let R := max 0 ((Real.log (2/c)+1)/(b-a))
  refine ⟨R,le_max_left _ _,?_⟩
  intro x hx
  have hx0 : 0≤x := (le_max_left _ _).trans hx
  have hlog : Real.log (2/c)<x*(b-a) := by
    have h := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hx)
    linarith
  have he : 2/c < Real.exp (x*(b-a)) := by
    rw [← Real.exp_log (div_pos (by norm_num) hc),Real.exp_lt_exp]
    exact hlog
  have hcprod : 2<c*Real.exp (x*(b-a)) := by simpa only [mul_comm] using (div_lt_iff₀ hc).mp he
  have hexp : Real.exp (x*b)=Real.exp (x*a)*Real.exp (x*(b-a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hgap : 0 < -Real.exp (x*a)+c*Real.exp (x*b)/2 := by
    rw [hexp]
    have h := mul_pos (Real.exp_pos (x*a)) (sub_pos.mpr hcprod)
    nlinarith only [h]
  exact lt_of_lt_of_le hgap (pulse_phase_lower a b x y ha0.le hab.le hb1.le hx0 hphase)

/-- Rotating by the actual endpoint phase identifies the retained positive integral. -/
theorem onsetPulseTransform_rotated_re (x y : ℝ) :
    (Complex.exp (-I*(y:ℂ))*onsetPulseTransform ((x:ℂ)+I*(y:ℂ))).re =
      ∫ u in (0:ℝ)..1,
        deriv Real.smoothTransition u*Real.exp (x*u)*Real.cos (y*(u-1)) := by
  let f := fun u : ℝ => ((deriv Real.smoothTransition u:ℝ):ℂ)*
    Complex.exp (((x*u:ℝ):ℂ)+I*((y*(u-1):ℝ):ℂ))
  have hf : Continuous f :=
    (Complex.continuous_ofReal.comp continuous_deriv_smoothTransition).mul (by fun_prop)
  have he : Complex.exp (-I*(y:ℂ))*onsetPulseTransform ((x:ℂ)+I*(y:ℂ)) =
      ∫ u in (0:ℝ)..1, f u := by
    unfold onsetPulseTransform
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro u _
    dsimp only [f]
    rw [mul_left_comm,← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he]
  have hr := Complex.reCLM.intervalIntegral_comp_comm (hf.intervalIntegrable 0 1 (μ := volume))
  change (∫ u in (0:ℝ)..1, (f u).re) = (∫ u in (0:ℝ)..1, f u).re at hr
  rw [← hr]
  apply integral_congr
  intro u _
  dsimp only [f]
  simp [Complex.mul_re,Complex.mul_im,Complex.exp_re,mul_assoc]

/-- At every fixed imaginary frequency the original unit-duration pulse survives all
sufficiently large real tilts. -/
theorem onsetPulseTransform_large_re_ne_zero (y : ℝ) :
    ∃ R : ℝ, 0≤R ∧ ∀ x : ℝ, R≤x → onsetPulseTransform ((x:ℂ)+I*(y:ℂ)) ≠ 0 := by
  obtain ⟨R,hR,hpos⟩ := onsetPulse_phase_integral_eventually_pos y
  refine ⟨R,hR,fun x hx hz => ?_⟩
  have hp := hpos x hx
  rw [← onsetPulseTransform_rotated_re,hz,mul_zero,Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

/-- The actual overtone spacing preserves the fixed pulse and eventually avoids its zeros. -/
theorem onsetPulseTransform_overtone_eventually_ne_zero (z : ℂ) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n → onsetPulseTransform (z+2*(n:ℂ)) ≠ 0 := by
  obtain ⟨R,_,hR⟩ := onsetPulseTransform_large_re_ne_zero z.im
  obtain ⟨N,hN⟩ := exists_nat_gt ((R-z.re)/2)
  refine ⟨N,fun n hn => ?_⟩
  have hnn : (N:ℝ)≤n := by exact_mod_cast hn
  have hx : R≤z.re+2*(n:ℝ) := by linarith
  have he : (((z.re+2*(n:ℝ):ℝ):ℂ)+I*(z.im:ℂ))=z+2*(n:ℂ) := by
    apply Complex.ext <;> simp
  simpa only [he] using hR (z.re+2*(n:ℝ)) hx

end
end RHTower.D4BMModularCore

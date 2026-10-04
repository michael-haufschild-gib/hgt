import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeTail

/-!
# The actual PM boundary kernel and its negative jet

Zero mass, the first signed logarithmic moment, and the absolute second
moment control the moving kernel directly. Prime-convolution identification
and complete signed energy compensation are separate obligations.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

private theorem pmk_measurable (ε : ℝ) : Measurable (pmPowerDampedBoundaryWeight ε) :=
  ((measurable_id.pow_const _).complex_ofReal).mul
    ((measurable_pmPowerDampedFermiSource ε).comp (measurable_const.div measurable_id))

private theorem pmk_second_moment {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    IntegrableOn (fun x => ‖pmPowerDampedBoundaryWeight ε x‖*Real.log x^2)
      (Ioi (1 : ℝ)) := by
  apply (integrableOn_pmPowerDampedFermiSource_boundary_log_sq hε hεhalf).mono'
    (((pmk_measurable ε).norm.mul (Real.measurable_log.pow_const 2)).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  change ‖‖pmPowerDampedBoundaryWeight ε x‖*Real.log x^2‖ ≤
    ‖pmPowerDampedFermiSource ε (1/x)‖*x^(ε-2)*(1+Real.log x^2)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)),
    pmPowerDampedBoundaryWeight,norm_mul,
    Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  have hc : 0 ≤ x^(ε-2)*‖pmPowerDampedFermiSource ε (1/x)‖ := by positivity
  nlinarith

private theorem pmk_real_log_integrable {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    IntegrableOn (fun x => (pmPowerDampedBoundaryWeight ε x).re*Real.log x)
      (Ioi (1 : ℝ)) := by
  have h : IntegrableOn (fun x =>
      (pmPowerDampedBoundaryWeight ε x*(Real.log x : ℂ)).re) (Ioi (1 : ℝ)) :=
    (integrableOn_pmPowerDampedBoundaryWeight_log hε hεhalf).re
  exact h.congr_fun (fun x _ => by
    simp only [Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero]) measurableSet_Ioi

private theorem pmk_real_log_integral {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    (∫ x in Ioi (1 : ℝ),(pmPowerDampedBoundaryWeight ε x).re*Real.log x) =
      -(pmPowerDampedBoundaryJet ε).re := by
  have h := integral_re (integrableOn_pmPowerDampedBoundaryWeight_log hε hεhalf)
  rw [pmPowerDampedBoundaryWeight_log_integral hε hεhalf] at h
  simpa only [RCLike.re_eq_complex_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero,Complex.neg_re] using h

/-- Finite centered-kernel estimate for the literal boundary source. -/
theorem pmPowerDampedBoundaryWeight_kernel_error {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∃ C ≥ 0, ∀ᶠ H : ℝ in atTop, ∀ L : ℝ, 2*Real.log H ≤ L →
      |L^2*(∫ x in Ioc (1 : ℝ) H,
        (pmPowerDampedBoundaryWeight ε x).re/(L-Real.log x))+
        (pmPowerDampedBoundaryJet ε).re| ≤
        C*(L/Real.log H^3+1/Real.log H+1/L) := by
  obtain ⟨C,hC,he⟩ := pmPowerDampedBoundaryWeight_mass_tail_bound hε hεhalf
  let w := pmPowerDampedBoundaryWeight ε
  let r : ℝ → ℝ := fun x => (w x).re
  let m : ℝ → ℝ := fun x => ‖w x‖*Real.log x^2
  let M : ℝ := ∫ x in Ioi (1 : ℝ),m x
  have hm : IntegrableOn m (Ioi (1 : ℝ)) := pmk_second_moment hε hεhalf
  have hm0 (x : ℝ) : 0 ≤ m x := by dsimp [m]; positivity
  have hM : 0 ≤ M := integral_nonneg hm0
  have hw : IntegrableOn w (Ioi (1 : ℝ)) :=
    integrableOn_pmPowerDampedBoundaryWeight hε hεhalf
  have hr : IntegrableOn r (Ioi (1 : ℝ)) := hw.re
  have hrlog : IntegrableOn (fun x => r x*Real.log x) (Ioi (1 : ℝ)) :=
    pmk_real_log_integrable hε hεhalf
  refine ⟨C+2*M,by positivity,?_⟩
  filter_upwards [he,eventually_gt_atTop (1 : ℝ)] with H htail hH
  intro L hL
  have hlH : 0 < Real.log H := Real.log_pos hH
  have hL0 : 0 < L := by linarith
  have hden (x : ℝ) (hx : x ∈ Ioc (1 : ℝ) H) : L/2 ≤ L-Real.log x := by
    have hh := Real.log_le_log (zero_lt_one.trans hx.1) hx.2
    linarith
  have hden0 (x : ℝ) (hx : x ∈ Ioc (1 : ℝ) H) : 0 < L-Real.log x :=
    (by positivity : 0 < L/2).trans_le (hden x hx)
  have htailw : IntegrableOn w (Ioi H) := hw.mono_set (Ioi_subset_Ioi hH.le)
  have hmass : |∫ x in Ioc (1 : ℝ) H,r x| ≤ C/Real.log H^3 := by
    have hs := intervalIntegral.integral_interval_add_Ioi hw htailw
    rw [intervalIntegral.integral_of_le hH.le,
      pmPowerDampedBoundaryWeight_integral hε hεhalf] at hs
    have hz : (∫ x in Ioc (1 : ℝ) H,w x) = -(∫ x in Ioi H,w x) := by
      linear_combination hs
    have hh := integral_re (hw.mono_set (s := Ioc (1 : ℝ) H) Ioc_subset_Ioi_self)
    change (∫ x in Ioc (1 : ℝ) H,r x) = (∫ x in Ioc (1 : ℝ) H,w x).re at hh
    rw [hh,hz,Complex.neg_re,abs_neg]
    exact (Complex.abs_re_le_norm _).trans htail
  have htailm : (∫ x in Ioi H,m x) ≤ M :=
    setIntegral_mono_set hm (Eventually.of_forall hm0)
      (Eventually.of_forall (Ioi_subset_Ioi hH.le))
  have hheadm : (∫ x in Ioc (1 : ℝ) H,m x) ≤ M :=
    setIntegral_mono_set hm (Eventually.of_forall hm0)
      (Eventually.of_forall Ioc_subset_Ioi_self)
  have hlogtail : |∫ x in Ioi H,r x*Real.log x| ≤ M/Real.log H := by
    have hb := norm_integral_le_of_norm_le
      ((hm.mono_set (Ioi_subset_Ioi hH.le)).div_const (Real.log H))
      (f := fun x => r x*Real.log x) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx1 : 1 < x := hH.trans hx
        have hlx : 0 < Real.log x := Real.log_pos hx1
        have hlog := Real.log_le_log (by linarith : 0 < H) hx.le
        rw [Real.norm_eq_abs,abs_mul,abs_of_pos hlx]
        apply (le_div_iff₀ hlH).mpr
        dsimp [m,r]
        calc
          _ ≤ ‖w x‖*Real.log x*Real.log H :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) hlx.le) hlH.le
          _ ≤ ‖w x‖*Real.log x*Real.log x :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
          _ = _ := by ring)
    rw [integral_div,Real.norm_eq_abs] at hb
    exact hb.trans (div_le_div_of_nonneg_right htailm hlH.le)
  let e : ℝ → ℝ := fun x => r x*Real.log x^2/(L-Real.log x)
  have he_bound (x : ℝ) (hx : x ∈ Ioc (1 : ℝ) H) : ‖e x‖ ≤ (2/L)*m x := by
    have hd := hden0 x hx
    have hi : 1/(L-Real.log x) ≤ 2/L := by
      calc
        _ ≤ 1/(L/2) := one_div_le_one_div_of_le (by positivity) (hden x hx)
        _ = _ := by ring
    dsimp [e,m,r]
    rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg (Real.log x)),abs_of_pos hd]
    calc
      _ ≤ (‖w x‖*Real.log x^2)/(L-Real.log x) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (sq_nonneg _)) hd.le
      _ = (1/(L-Real.log x))*(‖w x‖*Real.log x^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hi (by positivity)
  have he_meas : Measurable e :=
    (((pmk_measurable ε).re.mul (Real.measurable_log.pow_const 2)).div
      (measurable_const.sub Real.measurable_log))
  have hei : IntegrableOn e (Ioc (1 : ℝ) H) :=
    ((hm.mono_set Ioc_subset_Ioi_self).const_mul (2/L)).mono'
      he_meas.aestronglyMeasurable.restrict (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact he_bound x hx)
  have herr : |∫ x in Ioc (1 : ℝ) H,e x| ≤ 2*M/L := by
    have hb := norm_integral_le_of_norm_le
      ((hm.mono_set Ioc_subset_Ioi_self).const_mul (2/L)) (f := e) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact he_bound x hx)
    rw [integral_const_mul,Real.norm_eq_abs] at hb
    calc
      _ ≤ (2/L)*(∫ x in Ioc (1 : ℝ) H,m x) := hb
      _ ≤ (2/L)*M := mul_le_mul_of_nonneg_left hheadm (by positivity)
      _ = _ := by ring
  have hdecomp : L^2*(∫ x in Ioc (1 : ℝ) H,r x/(L-Real.log x)) =
      L*(∫ x in Ioc (1 : ℝ) H,r x)+
      (∫ x in Ioc (1 : ℝ) H,r x*Real.log x)+∫ x in Ioc (1 : ℝ) H,e x := by
    rw [← integral_const_mul]
    calc
      _ = ∫ x in Ioc (1 : ℝ) H,(L*r x+r x*Real.log x)+e x := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        dsimp [e]
        field_simp [(hden0 x hx).ne']
        ring
      _ = _ := by
        have hiadd : IntegrableOn (fun x => L*r x+r x*Real.log x) (Ioc (1 : ℝ) H) :=
          ((hr.mono_set Ioc_subset_Ioi_self).const_mul L).add
            (hrlog.mono_set Ioc_subset_Ioi_self)
        rw [integral_add hiadd hei,
          integral_add ((hr.mono_set Ioc_subset_Ioi_self).const_mul L)
            (hrlog.mono_set Ioc_subset_Ioi_self),integral_const_mul]
  have hlogsplit := intervalIntegral.integral_interval_add_Ioi hrlog
    (hrlog.mono_set (Ioi_subset_Ioi hH.le))
  rw [intervalIntegral.integral_of_le hH.le,
    pmk_real_log_integral hε hεhalf] at hlogsplit
  have hidentity : L^2*(∫ x in Ioc (1 : ℝ) H,r x/(L-Real.log x))+
      (pmPowerDampedBoundaryJet ε).re =
      L*(∫ x in Ioc (1 : ℝ) H,r x)-
      (∫ x in Ioi H,r x*Real.log x)+∫ x in Ioc (1 : ℝ) H,e x := by
    linarith
  change |L^2*(∫ x in Ioc (1 : ℝ) H,r x/(L-Real.log x))+
      (pmPowerDampedBoundaryJet ε).re| ≤ _
  rw [hidentity]
  have hmassL : |L*(∫ x in Ioc (1 : ℝ) H,r x)| ≤ C*L/Real.log H^3 := by
    rw [abs_mul,abs_of_pos hL0]
    calc
      _ ≤ L*(C/Real.log H^3) := mul_le_mul_of_nonneg_left hmass hL0.le
      _ = _ := by ring
  calc
    _ ≤ (|L*(∫ x in Ioc (1 : ℝ) H,r x)|+|∫ x in Ioi H,r x*Real.log x|)+
        |∫ x in Ioc (1 : ℝ) H,e x| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ C*L/Real.log H^3+M/Real.log H+2*M/L :=
      add_le_add (add_le_add hmassL hlogtail) herr
    _ ≤ (C+2*M)*(L/Real.log H^3+1/Real.log H+1/L) := by
      have h1 : 0 ≤ L/Real.log H^3 := by positivity
      have h2 : 0 ≤ 1/Real.log H := by positivity
      have h3 : 0 ≤ 1/L := by positivity
      calc
        _ = C*(L/Real.log H^3)+M*(1/Real.log H)+(2*M)*(1/L) := by ring
        _ ≤ (C+2*M)*(L/Real.log H^3)+(C+2*M)*(1/Real.log H)+(C+2*M)*(1/L) :=
          add_le_add (add_le_add
            (mul_le_mul_of_nonneg_right (by linarith) h1)
            (mul_le_mul_of_nonneg_right (by linarith) h2))
            (mul_le_mul_of_nonneg_right (by linarith) h3)
        _ = _ := by ring

/-- The moving boundary kernel converges to the negative actual-source jet. -/
theorem tendsto_pmPowerDampedBoundaryWeight_kernel {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    Tendsto (fun s : ℝ => s^10*(∫ x in Ioc (1 : ℝ) (Real.exp (s^2)),
      (pmPowerDampedBoundaryWeight ε x).re/(s^5-Real.log x))) atTop
      (𝓝 (-(pmPowerDampedBoundaryJet ε).re)) := by
  obtain ⟨C,hC,he⟩ := pmPowerDampedBoundaryWeight_kernel_error hε hεhalf
  have hH : Tendsto (fun s : ℝ => Real.exp (s^2)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
  have h1 : Tendsto (fun s : ℝ => 1/s) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 0))
  have h2 : Tendsto (fun s : ℝ => 1/s^2) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)))
  have h5 : Tendsto (fun s : ℝ => 1/s^5) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop (α := ℝ) (by norm_num : (5 : ℕ) ≠ 0)))
  have hb : Tendsto (fun s : ℝ => C*(1/s+1/s^2+1/s^5)) atTop (𝓝 0) := by
    simpa using ((h1.add h2).add h5).const_mul C
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  filter_upwards [hH.eventually he,eventually_ge_atTop (2 : ℝ)] with s hs hs2
  have hs0 : 0 < s := by linarith
  have hsq1 : 1 ≤ s^2 := by nlinarith
  have hcube : 2 ≤ s^3 := by
    have hh := mul_le_mul_of_nonneg_left hsq1 hs0.le
    nlinarith
  have hL : 2*Real.log (Real.exp (s^2)) ≤ s^5 := by
    rw [Real.log_exp]
    calc
      _ ≤ s^3*s^2 := mul_le_mul_of_nonneg_right hcube (sq_nonneg s)
      _ = _ := by ring
  have hh := hs (s^5) hL
  rw [Real.log_exp] at hh
  have hpow : (s^5)^2 = s^10 := by ring
  have hquot : s^5/(s^2)^3 = 1/s := by field_simp
  rw [hpow,hquot] at hh
  simpa only [Real.norm_eq_abs,sub_neg_eq_add] using hh

end RHTower

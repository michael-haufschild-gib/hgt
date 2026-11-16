import GaloisForLFunctions.HTGeometry.Analysis.LinearCumulativeLaplaceBound

/-!
# Vanishing terminal averages and Laplace decay

A logarithmic gain over linear cumulative mass forces its average to vanish.
For square mass, truncation converts a local small bound into a global
cumulative bound; weighted Cauchy–Schwarz controls the short transform.
The complementary transform is exponentially small. Thus the Laplace
transform is little-o of the reciprocal real parameter.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.HTGeometry

/-- A logarithmic gain over linear mass forces the terminal average to vanish. -/
theorem terminal_average_tendsto_zero_of_log_bound {m : ℝ → ℝ} {C : ℝ}
    (hm : ∀ h : ℝ, 0 < h → 0 ≤ m h)
    (hb : ∀ h : ℝ, 0 < h → h ≤ 1 → Real.log (2/h)*m h ≤ C*h) :
    Tendsto (fun h : ℝ => m h/h) (𝓝[>] 0) (𝓝 0) := by
  have hdiv : Tendsto (fun h : ℝ => 2/h) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using
      (tendsto_inv_nhdsGT_zero.const_mul_atTop (show (0:ℝ)<2 by norm_num))
  have hlog : Tendsto (fun h : ℝ => Real.log (2/h)) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp hdiv
  have hzero : Tendsto (fun h : ℝ => C/Real.log (2/h)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hlog).const_mul C
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h ≤ 1 :=
    ((eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds).mono
      fun _ h => h.le
  apply squeeze_zero' (hpos.mono fun h hh => div_nonneg (hm h hh) hh.le) _ hzero
  filter_upwards [hpos,hsmall] with h hh h1
  have hl : 0 < Real.log (2/h) := Real.log_pos ((lt_div_iff₀ hh).mpr (by linarith only [h1]))
  apply (le_div_iff₀ hl).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hh).mpr
  simpa only [mul_comm] using hb h hh h1

private theorem integrable_mul_exp_halfline {f : ℝ → ℝ} (hf : Integrable f)
    (hs : ∀ u, 0 ≤ u → f u = 0) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun u => f u * Real.exp (t*u)) := by
  refine hf.norm.mono' (hf.aestronglyMeasurable.mul (by fun_prop)) ?_
  exact Eventually.of_forall fun u => by
    rcases le_or_gt 0 u with hu | hu
    · simp only [hs u hu, zero_mul, norm_zero, le_refl]
    · rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ht hu.le))

/-- A local cumulative square bound gives a reciprocal term and an exponentially small tail. -/
theorem abs_laplace_le_of_local_terminal_square_mass
    {f : ℝ → ℝ} (hm : Measurable f) (hf : Integrable f)
    (hf2 : Integrable (fun u => f u^2)) (hs : ∀ u, 0 ≤ u → f u = 0)
    {ε δ t : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (ht : 0 < t)
    (hb : ∀ h : ℝ, 0 < h → h ≤ δ → (∫ u in Ioo (-h) 0, f u^2) ≤ ε*h) :
    |∫ u, f u * Real.exp (t*u)| ≤ Real.sqrt ε/t +
      (∫ u, |f u|) * Real.exp (-δ*t) := by
  let short : ℝ → ℝ := (Ioo (-δ) 0).indicator f
  let tail : ℝ → ℝ := (Iic (-δ)).indicator f
  have hsm : Measurable short := hm.indicator measurableSet_Ioo
  have hsi : Integrable short := hf.indicator measurableSet_Ioo
  have hti : Integrable tail := hf.indicator measurableSet_Iic
  have hss : ∀ u, 0 ≤ u → short u = 0 := by
    intro u hu
    exact indicator_of_notMem (show u ∉ Ioo (-δ) 0 from fun hu' => not_lt_of_ge hu hu'.2) f
  have hts : ∀ u, 0 ≤ u → tail u = 0 := by
    intro u hu
    exact indicator_of_notMem (show u ∉ Iic (-δ) from by
      intro hu'; change u ≤ -δ at hu'; linarith only [hu,hu',hδ]) f
  have hsq : (fun u => short u^2) = (Ioo (-δ) 0).indicator (fun u => f u^2) := by
    funext u
    by_cases hu : u ∈ Ioo (-δ) 0 <;> simp [short,hu]
  have hsi2 : Integrable (fun u => short u^2) := by
    rw [hsq]
    exact hf2.indicator measurableSet_Ioo
  have hsb : ∀ h : ℝ, 0 < h → (∫ u in Ioo (-h) 0, short u^2) ≤ ε*h := by
    intro h hh
    by_cases hhd : h ≤ δ
    · have he : (∫ u in Ioo (-h) 0, short u^2) = ∫ u in Ioo (-h) 0,f u^2 := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro u hu
        change ((Ioo (-δ) 0).indicator f u)^2 = f u^2
        rw [indicator_of_mem (show u ∈ Ioo (-δ) 0 from ⟨by linarith only [hu.1,hhd],hu.2⟩)]
      rw [he]
      exact hb h hh hhd
    · calc
        _ ≤ ∫ u, short u^2 := setIntegral_le_integral hsi2
          (Eventually.of_forall fun u => sq_nonneg _)
        _ = ∫ u in Ioo (-δ) 0,f u^2 := by rw [hsq,integral_indicator measurableSet_Ioo]
        _ ≤ ε*δ := hb δ hδ le_rfl
        _ ≤ ε*h := mul_le_mul_of_nonneg_left (not_le.mp hhd).le hε
  have hshort : |∫ u,short u*Real.exp (t*u)| ≤ Real.sqrt ε/t := by
    have he : (fun u => short u*Real.exp (t*u)) =
        (Iio 0).indicator (fun u => short u*Real.exp (t*u)) := by
      funext u
      by_cases hu : u < 0
      · rw [indicator_of_mem (show u ∈ Iio (0:ℝ) from hu)]
      · rw [indicator_of_notMem (show u ∉ Iio (0:ℝ) from hu),
          hss u (le_of_not_gt hu),zero_mul]
    calc
      _ = |∫ u in Iio 0,short u*Real.exp (t*u)| := by
        congr 1
        conv_lhs => rw [he,integral_indicator measurableSet_Iio]
      _ ≤ _ := abs_integral_exp_mul_Iio_le_of_terminal_square_mass hsm hsi2.restrict hε hsb ht
  have htail : |∫ u,tail u*Real.exp (t*u)| ≤ (∫ u,|f u|)*Real.exp (-δ*t) := by
    rw [← integral_mul_const]
    change ‖∫ u,tail u*Real.exp (t*u)‖ ≤ _
    apply norm_integral_le_of_norm_le ((hf.norm).mul_const (Real.exp (-δ*t)))
    refine Eventually.of_forall fun u => ?_
    by_cases hu : u ≤ -δ
    · change ‖(Iic (-δ)).indicator f u*Real.exp (t*u)‖ ≤ _
      rw [indicator_of_mem (show u ∈ Iic (-δ) from hu),norm_mul,
        Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        nlinarith only [mul_le_mul_of_nonneg_left hu ht.le])) (abs_nonneg _)
    · change ‖(Iic (-δ)).indicator f u*Real.exp (t*u)‖ ≤ _
      rw [indicator_of_notMem (show u ∉ Iic (-δ) from hu),zero_mul,norm_zero]
      positivity
  have hsplit : f = fun u => short u+tail u := by
    funext u
    rcases le_or_gt u (-δ) with hu | hu
    · have hnot : u ∉ Ioo (-δ) 0 := fun hu' => not_lt_of_ge hu hu'.1
      simp only [short,tail,indicator_of_notMem hnot,
        indicator_of_mem (show u ∈ Iic (-δ) from hu),zero_add]
    · have hnot : u ∉ Iic (-δ) := not_le.mpr hu
      by_cases hu0 : u < 0
      · simp only [short,tail,indicator_of_mem (show u ∈ Ioo (-δ) 0 from ⟨hu,hu0⟩),
          indicator_of_notMem hnot,add_zero]
      · have hnot' : u ∉ Ioo (-δ) 0 := fun hu' => hu0 hu'.2
        simp only [short,tail,indicator_of_notMem hnot',indicator_of_notMem hnot,
          hs u (le_of_not_gt hu0),zero_add]
  have he : (fun u => f u*Real.exp (t*u)) =
      fun u => short u*Real.exp (t*u)+tail u*Real.exp (t*u) := by
    funext u
    conv_lhs => rw [hsplit]
    exact add_mul _ _ _
  rw [he,integral_add (integrable_mul_exp_halfline hsi hss ht.le)
    (integrable_mul_exp_halfline hti hts ht.le)]
  exact (abs_add_le _ _).trans (add_le_add hshort htail)

/-- Vanishing terminal average square mass forces the Laplace transform to be little-o of `1/t`. -/
theorem tendsto_mul_laplace_of_vanishing_terminal_square_average
    {f : ℝ → ℝ} (hm : Measurable f) (hf : Integrable f)
    (hf2 : Integrable (fun u => f u^2)) (hs : ∀ u, 0 ≤ u → f u = 0)
    (hmean : Tendsto (fun h : ℝ => (∫ u in Ioo (-h) 0,f u^2)/h)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun t : ℝ => t*|∫ u,f u*Real.exp (t*u)|) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε2 : 0 < ε/2 := half_pos hε
  have hsmall := hmean.eventually_lt_const (sq_pos_of_pos hε2)
  obtain ⟨d,hd,hdbound⟩ := Metric.mem_nhdsWithin_iff.mp hsmall
  let δ : ℝ := d/2
  have hδ : 0 < δ := half_pos hd
  have hb : ∀ h : ℝ, 0 < h → h ≤ δ →
      (∫ u in Ioo (-h) 0,f u^2) ≤ (ε/2)^2*h := by
    intro h hh hhδ
    have hdist : dist h (0:ℝ) < d := by
      rw [Real.dist_eq,sub_zero,abs_of_pos hh]
      dsimp only [δ] at hhδ
      linarith only [hhδ,hd]
    have hb := hdbound ⟨hdist,hh⟩
    exact ((div_lt_iff₀ hh).mp hb).le
  have htail : Tendsto (fun t : ℝ => t*((∫ u,|f u|)*Real.exp (-δ*t))) atTop (𝓝 0) := by
    have hp : Tendsto (fun t : ℝ => (δ*t)*Real.exp (-(δ*t))) atTop (𝓝 0) := by
      simpa only [pow_one,Function.comp_def,id_eq] using
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
          (tendsto_id.const_mul_atTop hδ)
    have hh := hp.const_mul ((∫ u,|f u|)/δ)
    simp only [mul_zero] at hh
    apply hh.congr
    intro t
    rw [neg_mul]
    field_simp
  have hsqrt : Real.sqrt ((ε/2)^2) = ε/2 := by
    rw [Real.sqrt_sq_eq_abs,abs_of_pos hε2]
  filter_upwards [htail.eventually_lt_const hε2,eventually_gt_atTop (0:ℝ)] with t htail ht
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (mul_nonneg ht.le (abs_nonneg _))]
  have hb' := mul_le_mul_of_nonneg_left
    (abs_laplace_le_of_local_terminal_square_mass hm hf hf2 hs (sq_nonneg _) hδ ht hb) ht.le
  rw [hsqrt] at hb'
  have he : t*(ε/2/t+(∫ u,|f u|)*Real.exp (-δ*t)) =
      ε/2+t*((∫ u,|f u|)*Real.exp (-δ*t)) := by field_simp
  rw [he] at hb'
  linarith only [hb',htail]

end GaloisForLFunctions.HTGeometry

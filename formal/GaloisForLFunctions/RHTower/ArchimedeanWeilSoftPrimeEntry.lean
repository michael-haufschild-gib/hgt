import GaloisForLFunctions.RHTower.ArchimedeanWeilSupportRefinement

/-!
# Log-soft prime entry: end-window mass is paid for by the archimedean translation defect

A prime power `p^k` enters the restricted Weil form on the aperture `S` exactly when
`S ≥ k log p`, through the correlation `g(k log p) = ⟨f, T_{k log p} f⟩`, which only sees the mass
of `f` in the two end windows of length `S − k log p` of its support.  This file proves that such
end-window mass is controlled by the archimedean translation defect
`D(u) = ½‖f − T_u f‖²` on the range of shifts `u` beyond the window length: for `f` vanishing beyond
`b`, the translate `T_u f` carries the window mass out of the support, so
`∫_{b−u}^{b} f² ≤ ‖f − T_u f‖²`.  Combined with the singularity `K(u) ≥ 1/(2u)` of the archimedean
Weil weight on `(0, 1/10]`, the end-window mass `M_ε` satisfies

`M_ε · log(1/(10ε)) ≤ 4 ∫_ε^{1/10} D(u) K(u) du`,

so concentrating mass in an end window of length `ε` costs archimedean energy of order
`log(1/ε)`.  This is the mechanism by which the entry of a prime is *soft*: its term is bounded by
a vanishing multiple of the archimedean singular energy as the aperture crosses the threshold.
All statements are unconditional; the only hypotheses are the measurability and square
integrability of the test function and its vanishing beyond the endpoint.
-/

open MeasureTheory Set intervalIntegral

namespace RHTower.ArchimedeanKernel

/-- The archimedean translation defect `D(u) = ½ ∫ (f(x) − f(x − u))² dx`. -/
noncomputable def weilTranslationDefect (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  (1 / 2) * ∫ x, (f x - f (x - u)) ^ (2 : ℕ)

/-- The mass of `f` in the end window of length `ε` below `b`. -/
noncomputable def weilEndWindowMass (f : ℝ → ℝ) (b ε : ℝ) : ℝ :=
  ∫ x in Ioc (b - ε) b, f x ^ (2 : ℕ)

theorem integrable_sub_translate_sq {f : ℝ → ℝ} (hm : Measurable f)
    (hf : Integrable (fun x => f x ^ (2 : ℕ))) (u : ℝ) :
    Integrable (fun x => (f x - f (x - u)) ^ (2 : ℕ)) := by
  have h1 : Integrable (fun x => f (x - u) ^ (2 : ℕ)) := hf.comp_sub_right u
  have h2 : Integrable (fun x => 2 * f x ^ (2 : ℕ) + 2 * f (x - u) ^ (2 : ℕ)) :=
    (hf.const_mul 2).add (h1.const_mul 2)
  refine h2.mono' ?_ ?_
  · exact ((hm.sub (hm.comp (measurable_sub_const u))).pow_const 2).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (f x + f (x - u))]

theorem weilTranslationDefect_nonneg {f : ℝ → ℝ} (u : ℝ) : 0 ≤ weilTranslationDefect f u := by
  unfold weilTranslationDefect
  exact mul_nonneg (by norm_num) (integral_nonneg fun x => sq_nonneg _)

/-- **End-window mass is carried out by the translate.**  If `f` vanishes beyond `b`, the mass of
`f` in the window `(b − u, b]` is bounded by the squared translation defect at shift `u`. -/
theorem weilEndWindowMass_le_sub_translate_sq {f : ℝ → ℝ} (hm : Measurable f)
    (hf : Integrable (fun x => f x ^ (2 : ℕ))) {b : ℝ} (hb : ∀ x, b < x → f x = 0) {u : ℝ}
    (hu : 0 < u) :
    weilEndWindowMass f b u ≤ ∫ x, (f x - f (x - u)) ^ (2 : ℕ) := by
  unfold weilEndWindowMass
  have h1 : ∫ x in Ioc (b - u) b, f x ^ (2 : ℕ) = ∫ y in Ioc b (b + u), f (y - u) ^ (2 : ℕ) := by
    rw [← integral_of_le (by linarith), ← integral_of_le (by linarith),
      integral_comp_sub_right (fun x => f x ^ (2 : ℕ)) u]
    rw [add_sub_cancel_right]
  have h2 : ∫ y in Ioc b (b + u), f (y - u) ^ (2 : ℕ) = ∫ y in Ioc b (b + u), (f y - f (y - u)) ^ (2 : ℕ) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
    rw [hb y hy.1, zero_sub, neg_sq]
  rw [h1, h2]
  exact setIntegral_le_integral (integrable_sub_translate_sq hm hf u)
    (Filter.Eventually.of_forall fun y => sq_nonneg _)

/-- Window mass is monotone in the window length. -/
theorem weilEndWindowMass_mono {f : ℝ → ℝ} (hf : Integrable (fun x => f x ^ (2 : ℕ))) (b : ℝ)
    {ε u : ℝ} (hεu : ε ≤ u) :
    weilEndWindowMass f b ε ≤ weilEndWindowMass f b u := by
  unfold weilEndWindowMass
  refine setIntegral_mono_set hf.integrableOn (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (Filter.Eventually.of_forall ?_)
  intro x hx
  exact ⟨by linarith [hx.1], hx.2⟩

/-- **The archimedean weight dominates `1/(2u)` on `(0, 1/10]`.** -/
theorem inv_two_mul_le_weilKernel {u : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 10) :
    1 / (2 * u) ≤ weilKernel u := by
  have hP : 0 < Real.exp (-u / 2) * (1 - Real.exp (-2 * u)) / 2 :=
    div_pos (mul_pos (Real.exp_pos _) (one_sub_exp_neg_two_mul_pos hu)) two_pos
  have hmul := weilKernel_mul_pos_eq hu
  have hN : 1 / 2 ≤ Real.exp (-3 * u) + Real.exp (-2 * u) - 1 := by
    have h3 := Real.one_sub_le_exp_neg (3 * u)
    have h2 := Real.one_sub_le_exp_neg (2 * u)
    rw [show -3 * u = -(3 * u) by ring, show -2 * u = -(2 * u) by ring]
    linarith
  have hPle : Real.exp (-u / 2) * (1 - Real.exp (-2 * u)) / 2 ≤ u := by
    have hexp1 : Real.exp (-u / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hexp2 : 1 - Real.exp (-2 * u) ≤ 2 * u := by
      have := Real.one_sub_le_exp_neg (2 * u)
      rw [show -2 * u = -(2 * u) by ring]
      linarith
    have h0 : 0 ≤ 1 - Real.exp (-2 * u) := (one_sub_exp_neg_two_mul_pos hu).le
    calc Real.exp (-u / 2) * (1 - Real.exp (-2 * u)) / 2
        ≤ 1 * (2 * u) / 2 := by gcongr
      _ = u := by ring
  have hK : weilKernel u = (Real.exp (-3 * u) + Real.exp (-2 * u) - 1) /
      (Real.exp (-u / 2) * (1 - Real.exp (-2 * u)) / 2) := by
    rw [eq_div_iff hP.ne']
    exact hmul
  rw [hK, le_div_iff₀ hP]
  calc 1 / (2 * u) * (Real.exp (-u / 2) * (1 - Real.exp (-2 * u)) / 2)
      ≤ 1 / (2 * u) * u := by gcongr
    _ = 1 / 2 := by field_simp
    _ ≤ _ := hN

/-- **Pointwise log-soft law.**  For shifts `u ∈ [ε, 1/10]`, the weighted translation defect at
`u` dominates the end-window mass of length `ε` divided by `4u`. -/
theorem weilEndWindowMass_div_le_defect_mul_kernel {f : ℝ → ℝ} (hm : Measurable f)
    (hf : Integrable (fun x => f x ^ (2 : ℕ))) {b : ℝ} (hb : ∀ x, b < x → f x = 0) {ε u : ℝ}
    (hε : 0 < ε) (hεu : ε ≤ u) (hu : u ≤ 1 / 10) :
    weilEndWindowMass f b ε / (4 * u) ≤ weilTranslationDefect f u * weilKernel u := by
  have hu0 : 0 < u := lt_of_lt_of_le hε hεu
  have hM : weilEndWindowMass f b ε ≤ 2 * weilTranslationDefect f u := by
    calc weilEndWindowMass f b ε ≤ weilEndWindowMass f b u := weilEndWindowMass_mono hf b hεu
      _ ≤ ∫ x, (f x - f (x - u)) ^ (2 : ℕ) := weilEndWindowMass_le_sub_translate_sq hm hf hb hu0
      _ = 2 * weilTranslationDefect f u := by unfold weilTranslationDefect; ring
  have hK := inv_two_mul_le_weilKernel hu0 hu
  have hD := weilTranslationDefect_nonneg (f := f) u
  have hMnn : 0 ≤ weilEndWindowMass f b ε := by
    unfold weilEndWindowMass
    exact setIntegral_nonneg measurableSet_Ioc fun x _ => sq_nonneg _
  calc weilEndWindowMass f b ε / (4 * u)
      = (weilEndWindowMass f b ε / 2) * (1 / (2 * u)) := by field_simp; ring
    _ ≤ weilTranslationDefect f u * weilKernel u := by
        gcongr
        linarith

/-- **Integrated log-soft law.**  Mass in an end window of length `ε ≤ 1/10` costs archimedean
energy of order `log(1/(10ε))`. -/
theorem weilEndWindowMass_mul_log_le_integral {f : ℝ → ℝ} (hm : Measurable f)
    (hf : Integrable (fun x => f x ^ (2 : ℕ))) {b : ℝ} (hb : ∀ x, b < x → f x = 0) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hDK : IntervalIntegrable (fun u => weilTranslationDefect f u * weilKernel u) volume ε
      (1 / 10)) :
    weilEndWindowMass f b ε * Real.log (1 / (10 * ε)) ≤
      4 * ∫ u in ε..(1 / 10), weilTranslationDefect f u * weilKernel u := by
  set M := weilEndWindowMass f b ε with hMdef
  have hlow : IntervalIntegrable (fun u => M / (4 * u)) volume ε (1 / 10) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const (continuousOn_const.mul continuousOn_id) ?_
    intro u hu
    rw [uIcc_of_le hε'] at hu
    have : 0 < u := lt_of_lt_of_le hε hu.1
    positivity
  have hmono : ∫ u in ε..(1 / 10), M / (4 * u) ≤
      ∫ u in ε..(1 / 10), weilTranslationDefect f u * weilKernel u := by
    refine integral_mono_on hε' hlow hDK fun u hu => ?_
    exact weilEndWindowMass_div_le_defect_mul_kernel hm hf hb hε hu.1 hu.2
  have hval : ∫ u in ε..(1 / 10), M / (4 * u) = (M / 4) * Real.log (1 / (10 * ε)) := by
    have : (fun u : ℝ => M / (4 * u)) = fun u => (M / 4) * u⁻¹ := by
      funext u
      field_simp
    rw [this, intervalIntegral.integral_const_mul, integral_inv_of_pos hε (by norm_num)]
    congr 2
    field_simp
  rw [hval] at hmono
  linarith

end RHTower.ArchimedeanKernel

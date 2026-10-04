import GaloisForLFunctions.HTGeometry.GoldenRuleSincIntegral

/-!
# The kernel `(1 - cos x)/x²`, inversion substitution and finite Abel summation

The kernel `k(x) = (1 - cos x)/x² = 2 sin²(x/2)/x²` is nonnegative, bounded by `1/2` and by
`2/x²`, and has total mass `π` on the line (the sinc-square normalization at frequency `1/2`),
hence mass `π/2` on the half-line, with tails `∫_{x>U} k ≤ 2/U`.  Its logarithmic moment
`k(x) log x` is absolutely integrable on `(0, ∞)`.

Two general tools accompany it: the inversion substitution `y = T/x` on a half-line,
`∫_{y ≥ a} h(y) dy = ∫_{0 < x ≤ T/a} (T/x²) h(T/x) dx`, and finite Abel summation against a
counting function, `Σ_i φ(x_i) = #S·φ(Y) + ∫_a^Y g(y)·#{i : x_i ≤ y} dy` whenever `φ' = -g`
on `[a, Y]` and every point lies in `[a, Y]`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The kernel `(1 - cos x)/x²`. -/
def oneSubCosKernel (x : ℝ) : ℝ := (1 - Real.cos x) / x ^ 2

theorem one_sub_cos_eq_two_mul_sin_sq (x : ℝ) : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  have h1 := Real.cos_sq_add_sin_sq (x / 2)
  have h2 := Real.cos_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h2
  linarith

theorem one_sub_cos_nonneg (x : ℝ) : 0 ≤ 1 - Real.cos x := by
  linarith [Real.cos_le_one x]

theorem oneSubCosKernel_nonneg (x : ℝ) : 0 ≤ oneSubCosKernel x :=
  div_nonneg (one_sub_cos_nonneg x) (sq_nonneg x)

theorem oneSubCosKernel_le_half (x : ℝ) : oneSubCosKernel x ≤ 1 / 2 := by
  unfold oneSubCosKernel
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [div_le_iff₀ (by positivity)]
    linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

theorem oneSubCosKernel_le_two_div_sq (x : ℝ) : oneSubCosKernel x ≤ 2 / x ^ 2 := by
  unfold oneSubCosKernel
  exact div_le_div_of_nonneg_right (by linarith [Real.neg_one_le_cos x]) (sq_nonneg x)

theorem oneSubCosKernel_neg (x : ℝ) : oneSubCosKernel (-x) = oneSubCosKernel x := by
  simp [oneSubCosKernel]

theorem measurable_oneSubCosKernel : Measurable oneSubCosKernel := by
  unfold oneSubCosKernel
  fun_prop

/-- `∫_ℝ (1 - cos x)/x² dx = π`. -/
theorem integral_oneSubCosKernel : ∫ x, oneSubCosKernel x = Real.pi := by
  have h := integral_sin_sq_div_sq (a := 1 / 2) (by norm_num)
  have heq : oneSubCosKernel = fun x => 2 * (Real.sin (1 / 2 * x) ^ (2 : ℕ) / x ^ (2 : ℕ)) := by
    funext x
    unfold oneSubCosKernel
    rw [one_sub_cos_eq_two_mul_sin_sq, show x / 2 = 1 / 2 * x by ring]
    ring
  rw [heq, integral_const_mul, h]
  ring

theorem integrable_oneSubCosKernel : Integrable oneSubCosKernel :=
  Integrable.of_integral_ne_zero (by rw [integral_oneSubCosKernel]; exact Real.pi_pos.ne')

/-- `∫_0^∞ (1 - cos x)/x² dx = π/2`. -/
theorem integral_Ioi_oneSubCosKernel : ∫ x in Ioi 0, oneSubCosKernel x = Real.pi / 2 := by
  have hI := intervalIntegral.integral_Iic_add_Ioi (b := 0)
    integrable_oneSubCosKernel.integrableOn integrable_oneSubCosKernel.integrableOn
  have hneg : ∫ x in Iic 0, oneSubCosKernel x = ∫ x in Ioi 0, oneSubCosKernel x := by
    have := integral_comp_neg_Iic 0 oneSubCosKernel
    simp only [oneSubCosKernel_neg, neg_zero] at this
    exact this
  rw [integral_oneSubCosKernel, hneg] at hI
  linarith

/-- Tail bound `∫_{x>U} (1 - cos x)/x² dx ≤ 2/U`. -/
theorem integral_Ioi_oneSubCosKernel_le {U : ℝ} (hU : 0 < U) :
    ∫ x in Ioi U, oneSubCosKernel x ≤ 2 / U := by
  have hint : IntegrableOn (fun x : ℝ => 2 * x ^ (-2 : ℝ)) (Ioi U) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hU).const_mul 2
  calc ∫ x in Ioi U, oneSubCosKernel x ≤ ∫ x in Ioi U, 2 * x ^ (-2 : ℝ) := by
        refine setIntegral_mono_on integrable_oneSubCosKernel.integrableOn hint measurableSet_Ioi
          fun x hx => ?_
        have hx0 : 0 < x := hU.trans hx
        rw [Real.rpow_neg hx0.le, Real.rpow_two]
        calc oneSubCosKernel x ≤ 2 / x ^ 2 := oneSubCosKernel_le_two_div_sq x
          _ = 2 * (x ^ 2)⁻¹ := by ring
    _ = 2 / U := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hU]
        rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
        field_simp

theorem integrableOn_oneSubCosKernel_mul_log :
    IntegrableOn (fun x => oneSubCosKernel x * Real.log x) (Ioi 0) := by
  have hmeas : Measurable fun x => oneSubCosKernel x * Real.log x :=
    measurable_oneSubCosKernel.mul Real.measurable_log
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hlog : IntegrableOn Real.log (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        intervalIntegral.intervalIntegrable_log'
    refine Integrable.mono' (hlog.norm.const_mul (1 / 2)) hmeas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (oneSubCosKernel_nonneg x)]
    exact mul_le_mul_of_nonneg_right (oneSubCosKernel_le_half x) (abs_nonneg _)
  · have hb : IntegrableOn (fun x : ℝ => 4 * x ^ (-3 / 2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul 4
    refine Integrable.mono' hb hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := one_pos.trans hx
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx.le
    have hlog : Real.log x ≤ 2 * x ^ (1 / 2 : ℝ) := by
      have := Real.log_le_rpow_div hx0.le (ε := 1 / 2) (by norm_num)
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (oneSubCosKernel_nonneg x), abs_of_nonneg hlog0]
    have hpow : x ^ (-3 / 2 : ℝ) = x ^ (1 / 2 : ℝ) / x ^ 2 := by
      rw [show (-3 / 2 : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub hx0, Real.rpow_two]
    rw [hpow]
    calc oneSubCosKernel x * Real.log x ≤ 2 / x ^ 2 * (2 * x ^ (1 / 2 : ℝ)) :=
          mul_le_mul (oneSubCosKernel_le_two_div_sq x) hlog hlog0 (by positivity)
      _ = 4 * (x ^ (1 / 2 : ℝ) / x ^ 2) := by ring

/-- **Inversion substitution.**  For `T, a > 0`,
`∫_{y ≥ a} h(y) dy = ∫_{0 < x ≤ T/a} (T/x²)·h(T/x) dx`. -/
theorem integral_Ici_eq_integral_Ioc_inv {T a : ℝ} (hT : 0 < T) (ha : 0 < a) (h : ℝ → ℝ) :
    ∫ y in Ici a, h y = ∫ x in Ioc 0 (T / a), T / x ^ 2 * h (T / x) := by
  have himage : (fun x : ℝ => T / x) '' Ioc 0 (T / a) = Ici a := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx0, hxa⟩, rfl⟩
      rw [mem_Ici, le_div_iff₀ hx0]
      rw [le_div_iff₀ ha] at hxa
      linarith
    · intro hy
      rw [mem_Ici] at hy
      have hy0 : 0 < y := ha.trans_le hy
      refine ⟨T / y, ⟨div_pos hT hy0, div_le_div_of_nonneg_left hT.le ha hy⟩, ?_⟩
      field_simp
  have hderiv : ∀ x ∈ Ioc (0 : ℝ) (T / a),
      HasDerivWithinAt (fun x : ℝ => T / x) (-T / x ^ 2) (Ioc 0 (T / a)) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have h := (hasDerivAt_inv hx0).const_mul T
    refine (h.congr_deriv (by field_simp)).hasDerivWithinAt.congr_of_mem
      (fun y _ => by simp [div_eq_mul_inv]) hx
  have hinj : InjOn (fun x : ℝ => T / x) (Ioc 0 (T / a)) := by
    intro x hx y hy hxy
    have hx0 : x ≠ 0 := hx.1.ne'
    have hy0 : y ≠ 0 := hy.1.ne'
    simp only at hxy
    field_simp at hxy
    nlinarith [hxy]
  rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hderiv hinj h]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  have hx0 : 0 < x := hx.1
  simp only [smul_eq_mul]
  rw [abs_div, abs_neg, abs_of_pos hT, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2)]

/-- **Finite Abel summation.**  If every point `x i` lies in `(a, Y]` and `φ' = -g` on `[a, Y]`
with `g` continuous there, then `Σ_i φ(x_i) = #S·φ(Y) + ∫_a^Y g(y)·#{i : x_i ≤ y} dy`. -/
theorem sum_eq_card_mul_add_integral_count {ι : Type*} (S : Finset ι) (x : ι → ℝ) {a Y : ℝ}
    (hx : ∀ i ∈ S, a < x i ∧ x i ≤ Y) {φ g : ℝ → ℝ}
    (hφ : ∀ y ∈ Icc a Y, HasDerivAt φ (-g y) y) (hg : ContinuousOn g (Icc a Y)) :
    ∑ i ∈ S, φ (x i) =
      S.card * φ Y + ∫ y in a..Y, g y * ((S.filter fun i => x i ≤ y).card : ℝ) := by
  classical
  have hgint : IntegrableOn g (Ioc a Y) :=
    (hg.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hone : ∀ i ∈ S, φ (x i) = φ Y + ∫ y in a..Y, (Ici (x i)).indicator g y := by
    intro i hi
    obtain ⟨hai, hiY⟩ := hx i hi
    have haY : a ≤ Y := hai.le.trans hiY
    have hsub : uIcc (x i) Y ⊆ Icc a Y := by
      rw [uIcc_of_le hiY]; exact Icc_subset_Icc hai.le le_rfl
    have hftc : ∫ y in (x i)..Y, -g y = φ Y - φ (x i) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => hφ y (hsub hy))
        ((hg.mono hsub).neg.intervalIntegrable)
    have hset : Ioc a Y ∩ Ici (x i) = Icc (x i) Y := by
      ext y
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hai.trans_le h1, h2⟩, h1⟩
    have hsplit : (∫ y in a..Y, (Ici (x i)).indicator g y) = ∫ y in (x i)..Y, g y := by
      rw [intervalIntegral.integral_of_le haY, setIntegral_indicator measurableSet_Ici, hset,
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hiY]
    rw [hsplit]
    rw [intervalIntegral.integral_neg] at hftc
    linarith
  have hsum : (∑ i ∈ S, ∫ y in a..Y, (Ici (x i)).indicator g y) =
      ∫ y in a..Y, g y * ((S.filter fun i => x i ≤ y).card : ℝ) := by
    by_cases hS : S = ∅
    · subst hS; simp
    obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.2 hS
    have haY : a ≤ Y := (hx i₀ hi₀).1.le.trans (hx i₀ hi₀).2
    rw [← intervalIntegral.integral_finsetSum]
    · congr 1
      funext y
      simp only [Set.indicator_apply, mem_Ici]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      ring
    · intro i _
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le haY]
      exact hgint.indicator measurableSet_Ici
  rw [Finset.sum_congr rfl hone, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hsum]

end GaloisForLFunctions.HTGeometry

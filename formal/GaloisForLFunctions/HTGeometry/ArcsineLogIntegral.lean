import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The logarithmic potential of the arcsine law

For `x = cos φ`,

  `∫_0^π log|cos θ - cos φ| dθ = -π log 2`,

from `cos θ - cos φ = -2 sin((θ+φ)/2) sin((θ-φ)/2)`, the `π`-periodicity of `log|sin|` and
`∫_0^π log sin = -π log 2`.  Consequently the arcsine law on `[-b, b]` has constant logarithmic
potential on its support,

  `(1/π) ∫_0^π log|b cos θ - x| dθ = log(b/2)` for `|x| ≤ b`,

and at least `log(b/2)` for every real `x`.  (`Real.log` is even, so no absolute values appear.)
-/

open MeasureTheory Set Filter intervalIntegral
open scoped Real

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem periodic_log_sin : Function.Periodic (fun u : ℝ => Real.log (Real.sin u)) π := by
  intro u
  simp only [Real.sin_add_pi, Real.log_neg_eq_log]

theorem intervalIntegrable_log_sin_affine (c d : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => Real.log (Real.sin (c * θ + d))) volume a b := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [zero_mul, zero_add]; exact intervalIntegrable_const
  · have h := (intervalIntegrable_log_sin (a := c * a + d) (b := c * b + d)).comp_add_right d
    have h2 := h.comp_mul_left (c := c)
    simp only [Function.comp_def] at h2
    convert h2 using 1 <;> field_simp <;> ring

/-- A.e. on `[0, π]` (off a countable set), `log(cos θ - cos φ)` splits into half-angle sines. -/
theorem ae_log_cos_sub_cos_eq (φ : ℝ) :
    ∀ᵐ θ ∂(volume : Measure ℝ), Real.log (Real.cos θ - Real.cos φ) =
      Real.log 2 + Real.log (Real.sin ((1 / 2) * θ + φ / 2)) +
        Real.log (Real.sin ((1 / 2) * θ + -φ / 2)) := by
  have hcount : {θ : ℝ | Real.sin ((1 / 2) * θ + φ / 2) = 0 ∨ Real.sin ((1 / 2) * θ + -φ / 2) = 0}
      ⊆ Set.range (fun n : ℤ => 2 * n * π - φ) ∪ Set.range (fun n : ℤ => 2 * n * π + φ) := by
    rintro θ (h | h)
    · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
      exact Or.inl ⟨n, by linarith⟩
    · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
      exact Or.inr ⟨n, by linarith⟩
  have hnull : volume {θ : ℝ | Real.sin ((1 / 2) * θ + φ / 2) = 0 ∨
      Real.sin ((1 / 2) * θ + -φ / 2) = 0} = 0 :=
    measure_mono_null hcount (((Set.countable_range _).union (Set.countable_range _)).measure_zero _)
  refine ae_iff.mpr (measure_mono_null (fun θ hθ => ?_) hnull)
  simp only [Set.mem_setOf_eq] at hθ ⊢
  by_contra h
  push Not at h
  apply hθ
  rw [Real.cos_sub_cos, show -2 * Real.sin ((θ + φ) / 2) * Real.sin ((θ - φ) / 2) =
      -(2 * Real.sin ((1 / 2) * θ + φ / 2) * Real.sin ((1 / 2) * θ + -φ / 2)) by ring_nf,
    Real.log_neg_eq_log, Real.log_mul (mul_ne_zero two_ne_zero h.1) h.2,
    Real.log_mul two_ne_zero h.1]

theorem intervalIntegrable_log_cos_sub_cos (φ a b : ℝ) :
    IntervalIntegrable (fun θ => Real.log (Real.cos θ - Real.cos φ)) volume a b := by
  refine (((intervalIntegrable_const (c := Real.log 2)).add
    (intervalIntegrable_log_sin_affine (1 / 2) (φ / 2) a b)).add
    (intervalIntegrable_log_sin_affine (1 / 2) (-φ / 2) a b)).congr_ae ?_
  filter_upwards [ae_restrict_of_ae (ae_log_cos_sub_cos_eq φ)] with θ hθ
  exact hθ.symm

/-- **`∫_0^π log|cos θ - cos φ| dθ = -π log 2`.** -/
theorem integral_log_cos_sub_cos (φ : ℝ) :
    ∫ θ in (0 : ℝ)..π, Real.log (Real.cos θ - Real.cos φ) = -π * Real.log 2 := by
  rw [integral_congr_ae ((ae_log_cos_sub_cos_eq φ).mono fun θ h _ => h)]
  rw [integral_add ((intervalIntegrable_const (c := Real.log 2)).add
      (intervalIntegrable_log_sin_affine _ _ _ _)) (intervalIntegrable_log_sin_affine _ _ _ _),
    integral_add (intervalIntegrable_const (c := Real.log 2)) (intervalIntegrable_log_sin_affine _ _ _ _),
    intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have h1 := integral_comp_mul_add (a := 0) (b := π) (fun u => Real.log (Real.sin u))
    (by norm_num : (1 / 2 : ℝ) ≠ 0) (φ / 2)
  have h2 := integral_comp_mul_add (a := 0) (b := π) (fun u => Real.log (Real.sin u))
    (by norm_num : (1 / 2 : ℝ) ≠ 0) (-φ / 2)
  simp only [mul_zero, zero_add, smul_eq_mul] at h1 h2
  rw [h1, h2]
  -- reflect the second window
  have hrefl : ∫ u in -φ / 2..1 / 2 * π + -φ / 2, Real.log (Real.sin u) =
      ∫ u in φ / 2 - π / 2..φ / 2, Real.log (Real.sin u) := by
    have := integral_comp_neg (a := φ / 2 - π / 2) (b := φ / 2)
      (fun u => Real.log (Real.sin u))
    simp only [Real.sin_neg, Real.log_neg_eq_log] at this
    rw [this]; congr 1 <;> ring
  have hjoin : (∫ u in φ / 2 - π / 2..φ / 2, Real.log (Real.sin u)) +
      ∫ u in φ / 2..1 / 2 * π + φ / 2, Real.log (Real.sin u) = -Real.log 2 * π := by
    have hi : ∀ a b : ℝ, IntervalIntegrable (fun u => Real.log (Real.sin u)) volume a b :=
      fun _ _ => intervalIntegrable_log_sin
    rw [integral_add_adjacent_intervals (hi _ _) (hi _ _),
      show 1 / 2 * π + φ / 2 = (φ / 2 - π / 2) + π by ring,
      periodic_log_sin.intervalIntegral_add_eq (φ / 2 - π / 2) 0, zero_add]
    exact integral_log_sin_zero_pi
  rw [hrefl]
  linarith

theorem div_mem_Icc_of_abs_le {b x : ℝ} (hb : 0 < b) (hx : |x| ≤ b) :
    -1 ≤ x / b ∧ x / b ≤ 1 := by
  rw [abs_le] at hx
  exact ⟨by rw [le_div_iff₀ hb]; linarith, by rw [div_le_one hb]; linarith⟩

/-- A.e. splitting `log|b cos θ - x| = log b + log|cos θ - cos φ|` with `cos φ = x/b`. -/
theorem ae_log_mul_cos_sub_eq {b x : ℝ} (hb : 0 < b) (hx : |x| ≤ b) :
    ∀ᵐ θ ∂(volume : Measure ℝ), Real.log (b * Real.cos θ - x) =
      Real.log b + Real.log (Real.cos θ - Real.cos (Real.arccos (x / b))) := by
  obtain ⟨h1, h2⟩ := div_mem_Icc_of_abs_le hb hx
  set φ := Real.arccos (x / b)
  have hφ : Real.cos φ = x / b := Real.cos_arccos h1 h2
  have hcount : {θ : ℝ | Real.cos θ - Real.cos φ = 0} ⊆
      Set.range (fun n : ℤ => 2 * n * π - φ) ∪ Set.range (fun n : ℤ => 2 * n * π + φ) := by
    intro θ hθ
    simp only [Set.mem_setOf_eq, Real.cos_sub_cos] at hθ
    rcases mul_eq_zero.mp hθ with h | h
    · rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
        exact Or.inl ⟨n, by linarith⟩
    · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
      exact Or.inr ⟨n, by linarith⟩
  refine ae_iff.mpr (measure_mono_null (fun θ hθ => ?_)
    (measure_mono_null hcount (((Set.countable_range _).union
      (Set.countable_range _)).measure_zero _)))
  simp only [Set.mem_setOf_eq] at hθ ⊢
  by_contra h
  apply hθ
  rw [show b * Real.cos θ - x = b * (Real.cos θ - Real.cos φ) by rw [hφ]; field_simp,
    Real.log_mul hb.ne' h]

/-- The arcsine potential on its support: `∫_0^π log|b cos θ - x| dθ = π log(b/2)` for `|x| ≤ b`. -/
theorem integral_log_mul_cos_sub_of_abs_le {b x : ℝ} (hb : 0 < b) (hx : |x| ≤ b) :
    ∫ θ in (0 : ℝ)..π, Real.log (b * Real.cos θ - x) = π * Real.log (b / 2) := by
  rw [integral_congr_ae ((ae_log_mul_cos_sub_eq hb hx).mono fun θ h _ => h),
    integral_add (intervalIntegrable_const (c := Real.log b)) (intervalIntegrable_log_cos_sub_cos _ _ _),
    intervalIntegral.integral_const, smul_eq_mul, sub_zero, integral_log_cos_sub_cos,
    Real.log_div hb.ne' two_ne_zero]
  ring

theorem intervalIntegrable_log_mul_cos_sub {b : ℝ} (hb : 0 < b) (x : ℝ) :
    IntervalIntegrable (fun θ => Real.log (b * Real.cos θ - x)) volume 0 π := by
  by_cases hx : |x| ≤ b
  · refine ((intervalIntegrable_const (c := Real.log b)).add (intervalIntegrable_log_cos_sub_cos
      (Real.arccos (x / b)) 0 π)).congr_ae (ae_restrict_of_ae ?_)
    exact (ae_log_mul_cos_sub_eq hb hx).mono fun θ h => h.symm
  · push Not at hx
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.log (by fun_prop) fun θ _ h0 => ?_
    have hc := Real.abs_cos_le_one θ
    have : |x| = b * |Real.cos θ| := by
      rw [show x = b * Real.cos θ by linarith, abs_mul, abs_of_pos hb]
    nlinarith [abs_nonneg (Real.cos θ)]

/-- **The arcsine potential is at least `log(b/2)` everywhere on the real line.** -/
theorem integral_log_mul_cos_sub_ge {b : ℝ} (hb : 0 < b) (x : ℝ) :
    π * Real.log (b / 2) ≤ ∫ θ in (0 : ℝ)..π, Real.log (b * Real.cos θ - x) := by
  by_cases hx : |x| ≤ b
  · exact (integral_log_mul_cos_sub_of_abs_le hb hx).ge
  push Not at hx
  set e : ℝ := if 0 ≤ x then b else -b with he
  have heb : |e| ≤ b := by
    by_cases h : 0 ≤ x
    · simp [he, h, abs_of_pos hb]
    · simp [he, h, abs_of_pos hb]
  rw [← integral_log_mul_cos_sub_of_abs_le hb heb]
  refine integral_mono_ae_restrict Real.pi_pos.le (intervalIntegrable_log_mul_cos_sub hb _)
    (intervalIntegrable_log_mul_cos_sub hb _) ?_
  have hnull : volume ({0, π} : Set ℝ) = 0 := (Set.toFinite _).measure_zero _
  have hne : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({0, π} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with θ hθ hθne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hθne
  have hlt1 : Real.cos θ < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ.2 (lt_of_le_of_ne hθ.1 (Ne.symm hθne.1))
    rwa [Real.cos_zero] at this
  have hgt1 : -1 < Real.cos θ := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1 le_rfl (lt_of_le_of_ne hθ.2 hθne.2)
    rwa [Real.cos_pi] at this
  rw [← Real.log_abs (b * Real.cos θ - e), ← Real.log_abs (b * Real.cos θ - x)]
  by_cases h : 0 ≤ x
  · have hxb : b < x := by rw [abs_of_nonneg h] at hx; exact hx
    simp only [he, h, if_true]
    rw [abs_of_neg (by nlinarith), abs_of_neg (by nlinarith)]
    exact Real.log_le_log (by nlinarith) (by linarith)
  · push Not at h
    have hxb : x < -b := by rw [abs_of_neg h] at hx; linarith
    simp only [he, show ¬ (0 ≤ x) by linarith, if_false]
    rw [abs_of_pos (by nlinarith), abs_of_pos (by nlinarith)]
    exact Real.log_le_log (by nlinarith) (by linarith)

end GaloisForLFunctions.HTGeometry

import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# The logarithmic potential of the arcsine law

For `x = cos φ`,

  `∫_0^π log|cos θ - cos φ| dθ = -π log 2`,

from `cos θ - cos φ = -2 sin((θ+φ)/2) sin((θ-φ)/2)`, the `π`-periodicity of `log|sin|` and
`∫_0^π log sin = -π log 2`.  Consequently the arcsine law on `[-b, b]` has constant logarithmic
potential on its support,

  `(1/π) ∫_0^π log|b cos θ - x| dθ = log(b/2)` for `|x| ≤ b`,

and at least `log(b/2)` for every real `x`; off the support, `|x| > b`, it equals
`log((|x| + √(x² - b²))/2)`, from `∫_0^π log(1 - 2q cos θ + q²) dθ = 0` for `0 ≤ q < 1` (the circle
average of `log|z - q|`).  Its `cos 2θ` moment on the support is
`∫_0^π log|b cos θ - x| cos 2θ dθ = -(π/2)(2x²/b² - 1)`, from `∫_0^π log(sin v) cos 4v dv = -π/4`.
(`Real.log` is even, so no absolute values appear.)
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

/-! ### The `cos 2θ` moment -/

theorem intervalIntegral_cos_sq_mul_cos_two :
    ∫ v in (0 : ℝ)..π, Real.cos v ^ 2 * Real.cos (2 * v) = π / 4 := by
  have h : ∀ v : ℝ, Real.cos v ^ 2 * Real.cos (2 * v) = 2 * Real.cos v ^ (2 + 2) - Real.cos v ^ 2 :=
    fun v => by rw [Real.cos_two_mul]; ring
  simp_rw [h]
  rw [integral_sub ((by fun_prop : Continuous fun v => 2 * Real.cos v ^ (2 + 2)).intervalIntegrable
    _ _) ((by fun_prop : Continuous fun v => Real.cos v ^ 2).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_cos_pow, integral_cos_sq]
  simp
  ring

/-- `∫_0^π log(sin v) cos 4v dv = -π/4`, by parts against `sin 4v/4 = sin v cos v cos 2v`. -/
theorem integral_log_sin_mul_cos_four :
    ∫ v in (0 : ℝ)..π, Real.log (Real.sin v) * Real.cos (4 * v) = -π / 4 := by
  set G : ℝ → ℝ := fun v => Real.sin v * Real.log (Real.sin v) * Real.cos v * Real.cos (2 * v)
    with hG
  have hGc : Continuous G := by
    have : Continuous fun v => Real.sin v * Real.log (Real.sin v) :=
      Real.continuous_mul_log.comp Real.continuous_sin
    exact (this.mul Real.continuous_cos).mul (by fun_prop)
  have hderiv : ∀ v ∈ Ioo 0 π, HasDerivAt G (Real.log (Real.sin v) * Real.cos (4 * v) +
      Real.cos v ^ 2 * Real.cos (2 * v)) v := by
    intro v hv
    have hs : 0 < Real.sin v := Real.sin_pos_of_pos_of_lt_pi hv.1 hv.2
    have h1 : HasDerivAt Real.sin (Real.cos v) v := Real.hasDerivAt_sin v
    have h2 : HasDerivAt (fun v => Real.log (Real.sin v)) (Real.cos v / Real.sin v) v :=
      h1.log hs.ne'
    have h3 : HasDerivAt Real.cos (-Real.sin v) v := Real.hasDerivAt_cos v
    have h4 : HasDerivAt (fun v => Real.cos (2 * v)) (-Real.sin (2 * v) * 2) v := by
      have := (Real.hasDerivAt_cos (2 * v)).comp v ((hasDerivAt_id v).const_mul 2)
      simpa [Function.comp_def] using this
    refine (((h1.mul h2).mul h3).mul h4).congr_deriv ?_
    simp only [Pi.mul_apply]
    have hcs : Real.sin v * (Real.cos v / Real.sin v) = Real.cos v := by field_simp
    rw [hcs, show 4 * v = 2 * (2 * v) by ring, Real.cos_two_mul (2 * v), Real.cos_two_mul v,
      Real.sin_two_mul v]
    have hsc := Real.sin_sq_add_cos_sq v
    linear_combination (-(Real.log (Real.sin v) * (6 * Real.cos v ^ 2 - 1))) * hsc
  have hi1 : IntervalIntegrable (fun v => Real.log (Real.sin v) * Real.cos (4 * v)) volume 0 π :=
    intervalIntegrable_log_sin.mul_continuousOn (by fun_prop)
  have hi2 : IntervalIntegrable (fun v => Real.cos v ^ 2 * Real.cos (2 * v)) volume 0 π :=
    (by fun_prop : Continuous fun v => Real.cos v ^ 2 * Real.cos (2 * v)).intervalIntegrable _ _
  have hftc := integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le hGc.continuousOn hderiv
    (hi1.add hi2)
  rw [integral_add hi1 hi2, intervalIntegral_cos_sq_mul_cos_two] at hftc
  simp only [hG, Real.sin_pi, Real.sin_zero, zero_mul, sub_zero] at hftc
  linarith

/-- `∫_0^π log(sin v) sin 4v dv = 0`, by the symmetry `v ↦ π - v`. -/
theorem integral_log_sin_mul_sin_four :
    ∫ v in (0 : ℝ)..π, Real.log (Real.sin v) * Real.sin (4 * v) = 0 := by
  have h := integral_comp_sub_left (a := 0) (b := π)
    (fun v => Real.log (Real.sin v) * Real.sin (4 * v)) π
  have hs : ∀ v : ℝ, Real.sin (4 * (π - v)) = -Real.sin (4 * v) := fun v => by
    rw [show 4 * (π - v) = ((4 : ℕ) : ℝ) * π - 4 * v by push_cast; ring, Real.sin_sub,
      Real.sin_nat_mul_pi, show ((4 : ℕ) : ℝ) * π = ((2 : ℕ) : ℝ) * (2 * π) by push_cast; ring,
      Real.cos_nat_mul_two_pi]
    ring
  simp only [Real.sin_pi_sub, hs, mul_neg, intervalIntegral.integral_neg, sub_zero, sub_self] at h
  linarith

theorem periodic_log_sin_mul_cos (φ : ℝ) :
    Function.Periodic (fun u => Real.log (Real.sin u) * Real.cos (4 * u - 2 * φ)) π := by
  intro u
  simp only [Real.sin_add_pi, Real.log_neg_eq_log]
  rw [show 4 * (u + π) - 2 * φ = (4 * u - 2 * φ) + ((2 : ℕ) : ℝ) * (2 * π) by push_cast; ring,
    Real.cos_add_nat_mul_two_pi]

/-- **`∫_0^π log|cos θ - cos φ| cos 2θ dθ = -(π/2) cos 2φ`.** -/
theorem integral_log_cos_sub_cos_mul_cos_two (φ : ℝ) :
    ∫ θ in (0 : ℝ)..π, Real.log (Real.cos θ - Real.cos φ) * Real.cos (2 * θ) =
      -(π / 2) * Real.cos (2 * φ) := by
  have hc2 : Continuous fun θ : ℝ => Real.cos (2 * θ) := by fun_prop
  have hi : ∀ (c d a b : ℝ), IntervalIntegrable
      (fun θ => Real.log (Real.sin (c * θ + d)) * Real.cos (2 * θ)) volume a b :=
    fun c d a b => (intervalIntegrable_log_sin_affine c d a b).mul_continuousOn hc2.continuousOn
  rw [intervalIntegral.integral_congr_ae ((ae_log_cos_sub_cos_eq φ).mono fun θ h _ => by
    rw [h])]
  simp only [add_mul]
  rw [integral_add ((intervalIntegrable_const.mul_continuousOn hc2.continuousOn).add (hi _ _ _ _))
      (hi _ _ _ _), integral_add (intervalIntegrable_const.mul_continuousOn hc2.continuousOn)
      (hi _ _ _ _), intervalIntegral.integral_const_mul]
  have hcos2 : ∫ θ in (0 : ℝ)..π, Real.cos (2 * θ) = 0 := by
    rw [intervalIntegral.integral_comp_mul_left (fun θ => Real.cos θ) two_ne_zero, integral_cos]
    simp [Real.sin_two_pi]
  rw [hcos2, mul_zero, zero_add]
  set f₁ : ℝ → ℝ := fun u => Real.log (Real.sin u) * Real.cos (4 * u - 2 * φ) with hf₁
  have e1 : ∫ θ in (0 : ℝ)..π, Real.log (Real.sin ((1 / 2) * θ + φ / 2)) * Real.cos (2 * θ) =
      2 * ∫ u in φ / 2..π / 2 + φ / 2, f₁ u := by
    have h := integral_comp_mul_add (a := 0) (b := π) f₁ (by norm_num : (1 / 2 : ℝ) ≠ 0) (φ / 2)
    simp only [mul_zero, zero_add, smul_eq_mul, hf₁] at h
    rw [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num, show 1 / 2 * π = π / 2 by ring] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    congr 2; ring
  have e2 : ∫ θ in (0 : ℝ)..π, Real.log (Real.sin ((1 / 2) * θ + -φ / 2)) * Real.cos (2 * θ) =
      2 * ∫ u in φ / 2 - π / 2..φ / 2, f₁ u := by
    have h := integral_comp_mul_add (a := 0) (b := π)
      (fun u => Real.log (Real.sin u) * Real.cos (4 * u + 2 * φ)) (by norm_num : (1 / 2 : ℝ) ≠ 0)
      (-φ / 2)
    simp only [mul_zero, zero_add, smul_eq_mul] at h
    rw [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num, show 1 / 2 * π = π / 2 by ring] at h
    have hrefl : ∫ u in -φ / 2..π / 2 + -φ / 2, Real.log (Real.sin u) * Real.cos (4 * u + 2 * φ) =
        ∫ u in φ / 2 - π / 2..φ / 2, f₁ u := by
      have := integral_comp_neg (a := -φ / 2) (b := π / 2 + -φ / 2) f₁
      simp only [hf₁, Real.sin_neg, Real.log_neg_eq_log] at this
      rw [show -(π / 2 + -φ / 2) = φ / 2 - π / 2 by ring, show -(-φ / 2) = φ / 2 by ring] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun u _ => ?_
      rw [show 4 * -u - 2 * φ = -(4 * u + 2 * φ) by ring, Real.cos_neg]
    rw [← hrefl, ← h]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    congr 2; ring
  have hint₁ : ∀ a b : ℝ, IntervalIntegrable f₁ volume a b := fun a b =>
    intervalIntegrable_log_sin.mul_continuousOn (by fun_prop)
  have hjoin : (∫ u in φ / 2 - π / 2..φ / 2, f₁ u) + ∫ u in φ / 2..π / 2 + φ / 2, f₁ u =
      ∫ u in (0 : ℝ)..π, f₁ u := by
    rw [integral_add_adjacent_intervals (hint₁ _ _) (hint₁ _ _),
      show π / 2 + φ / 2 = (φ / 2 - π / 2) + π by ring,
      (periodic_log_sin_mul_cos φ).intervalIntegral_add_eq (φ / 2 - π / 2) 0, zero_add]
  have hfull : ∫ u in (0 : ℝ)..π, f₁ u = -(π / 4) * Real.cos (2 * φ) := by
    have hexp : ∀ u, f₁ u = Real.cos (2 * φ) * (Real.log (Real.sin u) * Real.cos (4 * u)) +
        Real.sin (2 * φ) * (Real.log (Real.sin u) * Real.sin (4 * u)) := fun u => by
      simp only [hf₁, Real.cos_sub]; ring
    simp_rw [hexp]
    have hi1 : IntervalIntegrable (fun u => Real.log (Real.sin u) * Real.cos (4 * u)) volume 0 π :=
      intervalIntegrable_log_sin.mul_continuousOn (by fun_prop)
    have hi2 : IntervalIntegrable (fun u => Real.log (Real.sin u) * Real.sin (4 * u)) volume 0 π :=
      intervalIntegrable_log_sin.mul_continuousOn (by fun_prop)
    rw [integral_add (hi1.const_mul _) (hi2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_log_sin_mul_cos_four, integral_log_sin_mul_sin_four]
    ring
  rw [e1, e2]
  linear_combination 2 * hjoin + 2 * hfull

/-- **The `cos 2θ` moment of the arcsine potential on its support**:
`∫_0^π log|b cos θ - x| cos 2θ dθ = -(π/2)(2x²/b² - 1)` for `|x| ≤ b`. -/
theorem integral_log_mul_cos_sub_mul_cos_two {b x : ℝ} (hb : 0 < b) (hx : |x| ≤ b) :
    ∫ θ in (0 : ℝ)..π, Real.log (b * Real.cos θ - x) * Real.cos (2 * θ) =
      -(π / 2) * (2 * x ^ 2 / b ^ 2 - 1) := by
  obtain ⟨h1, h2⟩ := div_mem_Icc_of_abs_le hb hx
  have hc2 : Continuous fun θ : ℝ => Real.cos (2 * θ) := by fun_prop
  rw [intervalIntegral.integral_congr_ae ((ae_log_mul_cos_sub_eq hb hx).mono fun θ h _ => by
    rw [h])]
  simp only [add_mul]
  rw [integral_add (intervalIntegrable_const.mul_continuousOn hc2.continuousOn)
    ((intervalIntegrable_log_cos_sub_cos _ _ _).mul_continuousOn hc2.continuousOn),
    intervalIntegral.integral_const_mul, integral_log_cos_sub_cos_mul_cos_two, Real.cos_two_mul,
    Real.cos_arccos h1 h2]
  have hcos2 : ∫ θ in (0 : ℝ)..π, Real.cos (2 * θ) = 0 := by
    rw [intervalIntegral.integral_comp_mul_left (fun θ => Real.cos θ) two_ne_zero, integral_cos]
    simp [Real.sin_two_pi]
  rw [hcos2]
  field_simp
  ring

/-! ### The arcsine potential off its support -/

/-- **`∫_0^π log(1 - 2q cos θ + q²) dθ = 0`** for `0 ≤ q < 1`: the circle average of
`log|z - q|` vanishes. -/
theorem integral_log_one_sub_two_mul_cos_add_sq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∫ θ in (0 : ℝ)..π, Real.log (1 - 2 * q * Real.cos θ + q ^ 2) = 0 := by
  have hpos : ∀ θ, 0 < 1 - 2 * q * Real.cos θ + q ^ 2 := fun θ => by
    nlinarith [Real.cos_le_one θ, sq_nonneg (1 - q), mul_nonneg hq0 (sub_nonneg.mpr
      (Real.cos_le_one θ))]
  set g : ℝ → ℝ := fun θ => Real.log (1 - 2 * q * Real.cos θ + q ^ 2) with hg
  have hgc : Continuous g := Continuous.log (by fun_prop) fun θ => (hpos θ).ne'
  have hca := circleAverage_log_norm_sub_const₀ (a := (q : ℂ))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
  rw [Real.circleAverage_def, smul_eq_zero] at hca
  have hnorm : ∀ θ : ℝ, Real.log ‖circleMap 0 1 θ - (q : ℂ)‖ = g θ / 2 := fun θ => by
    rw [circleMap_zero, Complex.ofReal_one, one_mul, Complex.norm_def, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Real.log_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))]
    simp only [hg]
    congr 2
    nlinarith [Real.sin_sq_add_cos_sq θ]
  simp only [hnorm] at hca
  rcases hca with h | h
  · exact absurd h (by positivity)
  rw [intervalIntegral.integral_div] at h
  have h2π : ∫ θ in (0 : ℝ)..2 * π, g θ = 2 * ∫ θ in (0 : ℝ)..π, g θ := by
    rw [← integral_add_adjacent_intervals (b := π) (hgc.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _)]
    have hr := integral_comp_sub_left (a := π) (b := 2 * π) g (2 * π)
    have hcos : ∀ θ, g (2 * π - θ) = g θ := fun θ => by
      simp only [hg, Real.cos_two_pi_sub]
    simp only [hcos, sub_self, show 2 * π - π = π by ring] at hr
    rw [hr]; ring
  rw [h2π] at h
  linarith

/-- **The arcsine potential off its support.**  For `0 < a < x`,
`∫_0^π log(x - a cos θ) dθ = π log((x + √(x² - a²))/2)`. -/
theorem integral_log_sub_mul_cos_of_lt {a x : ℝ} (ha : 0 < a) (hax : a < x) :
    ∫ θ in (0 : ℝ)..π, Real.log (x - a * Real.cos θ) =
      π * Real.log ((x + Real.sqrt (x ^ 2 - a ^ 2)) / 2) := by
  set σ := Real.sqrt (x ^ 2 - a ^ 2) with hσ
  have hσ2 : σ ^ 2 = x ^ 2 - a ^ 2 := Real.sq_sqrt (by nlinarith)
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσx : σ < x := by nlinarith
  set q := (x - σ) / a with hq
  have hq0 : 0 < q := div_pos (by linarith) ha
  have hq1 : q < 1 := by
    rw [hq, div_lt_one ha]
    nlinarith
  have hxσ : (x - σ) * (x + σ) = a ^ 2 := by nlinarith
  have h1 : (x + σ) * q = a := by
    rw [hq]; field_simp; linear_combination hxσ
  have hfac : ∀ θ, x - a * Real.cos θ = (x + σ) / 2 * (1 - 2 * q * Real.cos θ + q ^ 2) := by
    intro θ
    calc x - a * Real.cos θ = (x + σ) / 2 - a * Real.cos θ + a * q / 2 := by
          rw [hq]; field_simp; ring
      _ = (x + σ) / 2 - ((x + σ) * q) * Real.cos θ + ((x + σ) * q) * q / 2 := by rw [h1]
      _ = (x + σ) / 2 * (1 - 2 * q * Real.cos θ + q ^ 2) := by ring
  have hpos : ∀ θ, 0 < 1 - 2 * q * Real.cos θ + q ^ 2 := fun θ => by
    nlinarith [Real.cos_le_one θ, sq_nonneg (1 - q), mul_nonneg hq0.le (sub_nonneg.mpr
      (Real.cos_le_one θ))]
  have hxσ : 0 < (x + σ) / 2 := by linarith
  have hsplit : ∀ θ, Real.log (x - a * Real.cos θ) =
      Real.log ((x + σ) / 2) + Real.log (1 - 2 * q * Real.cos θ + q ^ 2) := fun θ => by
    rw [hfac θ, Real.log_mul hxσ.ne' (hpos θ).ne']
  simp_rw [hsplit]
  rw [integral_add intervalIntegrable_const (Continuous.intervalIntegrable (Continuous.log
    (by fun_prop) fun θ => (hpos θ).ne') _ _), intervalIntegral.integral_const, smul_eq_mul,
    sub_zero, integral_log_one_sub_two_mul_cos_add_sq hq0.le hq1, add_zero]

/-- The arcsine potential off its support, for either sign of `x`:
`∫_0^π log|b cos θ - x| dθ = π log((|x| + √(x² - b²))/2)` for `|x| > b > 0`. -/
theorem integral_log_mul_cos_sub_of_lt_abs {b x : ℝ} (hb : 0 < b) (hbx : b < |x|) :
    ∫ θ in (0 : ℝ)..π, Real.log (b * Real.cos θ - x) =
      π * Real.log ((|x| + Real.sqrt (x ^ 2 - b ^ 2)) / 2) := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at hbx ⊢
    rw [← integral_log_sub_mul_cos_of_lt hb hbx]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [← Real.log_neg_eq_log, neg_sub]
  · rw [abs_of_neg h] at hbx ⊢
    rw [show x ^ 2 = (-x) ^ 2 by ring, ← integral_log_sub_mul_cos_of_lt hb hbx]
    have hr := integral_comp_sub_left (a := 0) (b := π)
      (fun θ => Real.log (-x - b * Real.cos θ)) π
    simp only [Real.cos_pi_sub, sub_zero, sub_self] at hr
    rw [← hr]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    ring_nf

end GaloisForLFunctions.HTGeometry

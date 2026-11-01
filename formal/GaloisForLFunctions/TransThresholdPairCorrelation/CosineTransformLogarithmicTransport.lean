import GaloisForLFunctions.TransThresholdPairCorrelation.SmoothWindowContinuousForm
import GaloisForLFunctions.TransThresholdPairCorrelation.CoalescentSieveAnatomyAndModelCalibration

/-!
# Decay-preserving logarithmic transport of cosine transforms

Frequency differentiation turns a cosine transform into the sine transform
of its time-weighted window. Fourth-order decay therefore controls logarithmic
phase errors even outside the central Fourier lobe. A telescoping reciprocal
square envelope also bounds positive-frequency lattice mass without an
additive window-height term.
-/

noncomputable section
open MeasureTheory Real Filter Topology Finset
open Zeta23
namespace GaloisForLFunctions.TransThresholdPairCorrelation

private theorem cosTransform_eq_interval {Ω : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) (θ : ℝ) :
    cosTransform Ω θ = ∫ t in (a - 1)..(b + 1), Ω t * Real.cos (t * θ) := by
  unfold cosTransform
  rw [intervalIntegral.integral_of_le (by linarith : a - 1 ≤ b + 1),
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro t ht
  have hn : t ∉ Set.Icc a b := fun h => ht ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [hsupp t hn, zero_mul]

/-- The frequency derivative of a compact cosine transform is the negative
sine transform of the time-weighted window. -/
theorem hasDerivAt_cosTransform {Ω : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hΩ : Continuous Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) (θ : ℝ) :
    HasDerivAt (cosTransform Ω)
      (-(∫ t in (a - 1)..(b + 1), (t * Ω t) * Real.sin (θ * t))) θ := by
  let F : ℝ → ℝ → ℝ := fun x t => Ω t * Real.cos (t * x)
  let F' : ℝ → ℝ → ℝ := fun x t => -(t * Ω t) * Real.sin (t * x)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a - 1) (b := b + 1)
    (F := F) (F' := F') (bound := fun t => |t * Ω t|) (s := Set.univ)
    (x₀ := θ) Filter.univ_mem
    (Eventually.of_forall fun x =>
      (by fun_prop : Continuous (fun t : ℝ => F x t)).aestronglyMeasurable)
    ((by fun_prop : Continuous (F θ)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (F' θ)).aestronglyMeasurable)
    (Eventually.of_forall fun t _ x _ => by
      change ‖-(t * Ω t) * Real.sin (t * x)‖ ≤ |t * Ω t|
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
    ((by fun_prop : Continuous (fun t => |t * Ω t|)).intervalIntegrable _ _)
    (Eventually.of_forall fun t _ x _ => by
      have hlin : HasDerivAt (fun y : ℝ => t * y) t x := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul t
      simpa [F, F', mul_assoc, mul_comm, mul_left_comm] using hlin.cos.const_mul (Ω t))
  have he : (fun x => ∫ t in (a - 1)..(b + 1), F x t) = cosTransform Ω := by
    funext x
    exact (cosTransform_eq_interval hab hsupp x).symm
  have hd : (∫ t in (a - 1)..(b + 1), F' θ t) =
      -(∫ t in (a - 1)..(b + 1), (t * Ω t) * Real.sin (θ * t)) := by
    simp only [F', neg_mul, mul_comm θ, intervalIntegral.integral_neg]
  rw [he, hd] at h
  exact h.2

/-- Fourth-order decay survives frequency differentiation by applying
integration by parts to the time-weighted window. -/
theorem abs_deriv_cosTransform_le_fourth {Ω : ℝ → ℝ} {a b θ : ℝ}
    (hab : a ≤ b) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) (hθ : θ ≠ 0) :
    |deriv (cosTransform Ω) θ| ≤
      (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 (fun t => t * Ω t) t|) / |θ|^4 := by
  rw [(hasDerivAt_cosTransform hab hΩ.continuous hsupp θ).deriv, abs_neg]
  have h := abs_intervalIntegral_mul_sin_le hab 4
    (show ContDiff ℝ 4 (fun t => t * Ω t) from contDiff_id.mul hΩ)
    (by intro t ht; rw [hsupp t ht, mul_zero]) hθ 0
  simpa only [add_zero] using h


/-- The first time moment bounds the cosine transform's frequency derivative. -/
theorem abs_deriv_cosTransform_le_mass {Ω : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hΩ : Continuous Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) (θ : ℝ) :
    |deriv (cosTransform Ω) θ| ≤ ∫ t in (a - 1)..(b + 1), |t * Ω t| := by
  rw [(hasDerivAt_cosTransform hab hΩ hsupp θ).deriv, abs_neg]
  refine (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans ?_
  apply intervalIntegral.integral_mono_on (by linarith)
  · exact ((by fun_prop : Continuous (fun t => (t * Ω t) * Real.sin (θ * t))).abs).intervalIntegrable _ _
  · exact ((by fun_prop : Continuous (fun t => t * Ω t)).abs).intervalIntegrable _ _
  · intro t _
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

/-- The quadratic logarithmic shift error retains fourth-order Fourier decay,
instead of paying a global Lipschitz constant at every frequency. -/
theorem abs_cosTransform_log_sub_linear_le {Ω : ℝ → ℝ} {a b x : ℝ}
    (hab : a ≤ b) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) (hx : 0 < x) (hx1 : x ≤ 1) :
    |cosTransform Ω (Real.log (1 + x)) - cosTransform Ω x| ≤
      min ((∫ t in (a - 1)..(b + 1), |t * Ω t|) * x^2)
        (16 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 (fun t => t * Ω t) t|) / x^2) := by
  let M := ∫ t in (a - 1)..(b + 1), |t * Ω t|
  let D := ∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 (fun t => t * Ω t) t|
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  have hD : 0 ≤ D := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  have hl := log_one_add_div_bounds (m := 1) (h := x) (by norm_num) hx.le
  simp only [div_one] at hl
  have hhalf : x / 2 ≤ Real.log (1 + x) :=
    (div_le_div_of_nonneg_left hx.le (by positivity : 0 < 1 + x)
      (by linarith : 1 + x ≤ 2)).trans hl.1
  have herr := sub_log_one_add_div_bounds (m := 1) (h := x) (by norm_num) hx.le
  simp only [div_one, one_mul, one_pow] at herr
  have hbound (y : ℝ) (hy : y ∈ Set.Icc (x / 2) x) :
      ‖deriv (cosTransform Ω) y‖ ≤ min M (16 * D / x^4) := by
    rw [Real.norm_eq_abs]
    apply le_min (abs_deriv_cosTransform_le_mass hab hΩ.continuous hsupp y)
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity : 0 < x / 2) hy.1
    have hh := abs_deriv_cosTransform_le_fourth hab hΩ hsupp hy0.ne'
    rw [abs_of_pos hy0] at hh
    calc
      _ ≤ D / y^4 := hh
      _ ≤ D / (x / 2)^4 := div_le_div_of_nonneg_left hD (by positivity)
        (pow_le_pow_left₀ (by positivity) hy.1 4)
      _ = _ := by
        field_simp [hx.ne']
        norm_num
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := cosTransform Ω) (s := Set.Icc (x / 2) x)
    (fun y _ => (hasDerivAt_cosTransform hab hΩ.continuous hsupp y).differentiableAt)
    hbound (convex_Icc _ _) (show Real.log (1 + x) ∈ Set.Icc (x / 2) x from ⟨hhalf, hl.2⟩)
    (show x ∈ Set.Icc (x / 2) x from ⟨by linarith, le_rfl⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg herr.1] at h
  have hm0 : 0 ≤ min M (16 * D / x^4) := le_min hM (by positivity)
  have he : |cosTransform Ω (Real.log (1 + x)) - cosTransform Ω x| ≤
      min M (16 * D / x^4) * x^2 := by
    rw [abs_sub_comm]
    exact h.trans (mul_le_mul_of_nonneg_left (herr.2.1.trans herr.2.2) hm0)
  apply le_min
  · exact he.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg x))
  · calc
      _ ≤ (16 * D / x^4) * x^2 :=
        he.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg x))
      _ = _ := by field_simp [hx.ne']; ring

private theorem sum_inverse_square_affine_le {α : ℝ} (hα : 0 < α) (R : ℕ) :
    (∑ n ∈ range R, 1 / (1 + α * ((n : ℝ) + 1))^2) ≤ 1 / α := by
  have hpt (n : ℕ) : 1 / (1 + α * ((n : ℝ) + 1))^2 ≤
      (1 / α) * (1 / (1 + α * n) - 1 / (1 + α * (n + 1 : ℕ))) := by
    have ha : 0 < 1 + α * (n : ℝ) := by positivity
    have hb : 0 < 1 + α * ((n : ℝ) + 1) := by positivity
    have he : (1 / α) * (1 / (1 + α * n) - 1 / (1 + α * (n + 1 : ℕ))) =
        1 / ((1 + α * n) * (1 + α * ((n : ℝ) + 1))) := by
      push_cast
      field_simp [hα.ne', ha.ne', hb.ne']
      ring
    rw [he]
    apply one_div_le_one_div_of_le (mul_pos ha hb)
    have hm := mul_le_mul_of_nonneg_right (show 1 + α * (n : ℝ) ≤ 1 + α * ((n : ℝ) + 1) by linarith) hb.le
    simpa only [pow_two] using hm
  calc
    _ ≤ ∑ n ∈ range R, (1 / α) * (1 / (1 + α * n) - 1 / (1 + α * (n + 1 : ℕ))) :=
      sum_le_sum (fun n _ => hpt n)
    _ = (1 / α) * (1 - 1 / (1 + α * R)) := by
      rw [← mul_sum, sum_range_sub']
      simp
    _ ≤ (1 / α) * 1 := mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)
    _ = _ := mul_one _


private theorem min_fourth_envelope {A D x : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hx : 0 < x) :
    min A (D / x^4) ≤ 4 * (A + D) / (1 + x)^2 := by
  have hden : 0 < (1 + x)^2 := by positivity
  by_cases hx1 : x ≤ 1
  · apply (min_le_left _ _).trans
    rw [le_div_iff₀ hden]
    have hb : (1 + x)^2 ≤ 4 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hb hA
    nlinarith only [hm, hD]
  · have h1 : 1 ≤ x := by linarith
    have hx2 : 1 ≤ x^2 := one_le_pow₀ h1
    have hp : x^2 ≤ x^4 := by nlinarith only [sq_nonneg (x^2 - 1), hx2]
    have hb : (1 + x)^2 ≤ 4 * x^4 := by nlinarith only [sq_nonneg (x - 1), h1, hp]
    apply (min_le_right _ _).trans
    rw [div_le_div_iff₀ (by positivity : 0 < x^4) hden]
    have hm := mul_le_mul_of_nonneg_left hb hD
    have ha4 := mul_nonneg hA (pow_nonneg hx.le 4)
    nlinarith only [hm, ha4]

/-- The window mass bounds its cosine transform at every frequency. -/
theorem abs_cosTransform_le_mass {Ω : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hΩ : Continuous Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) (θ : ℝ) :
    |cosTransform Ω θ| ≤ ∫ t in (a - 1)..(b + 1), |Ω t| := by
  rw [cosTransform_eq_interval hab hsupp]
  refine (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans ?_
  apply intervalIntegral.integral_mono_on (by linarith)
  · exact ((hΩ.mul (by fun_prop)).abs).intervalIntegrable _ _
  · exact hΩ.abs.intervalIntegrable _ _
  · intro t _
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- The positive-frequency lattice has mass proportional to its base scale,
with no additive window-height term. The auxiliary scale `T` balances the
zeroth and fourth Fourier moments. -/
theorem sum_abs_cosTransform_even_lattice_le {Ω : ℝ → ℝ} {a b T m : ℝ}
    (hab : a ≤ b) (hT : 0 < T) (hm : 0 < m) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) (R : ℕ) :
    (∑ n ∈ range R, |cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m)|) ≤
      2 * m * ((∫ t in (a - 1)..(b + 1), |Ω t|) / T +
        T^3 * ∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|) := by
  let M := ∫ t in (a - 1)..(b + 1), |Ω t|
  let D := ∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|
  let C := M / T + T^3 * D
  have hM : 0 ≤ M := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  have hD : 0 ≤ D := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => abs_nonneg _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpt (n : ℕ) : |cosTransform Ω (((2 * (n + 1) : ℕ) : ℝ) / m)| ≤
      (4 * T * C) * (1 / (1 + (2 * T / m) * ((n : ℝ) + 1))^2) := by
    let θ : ℝ := ((2 * (n + 1) : ℕ) : ℝ) / m
    have hθ : 0 < θ := by dsimp [θ]; positivity
    have h0 : |cosTransform Ω θ| / T ≤ M / T :=
      div_le_div_of_nonneg_right (abs_cosTransform_le_mass hab hΩ.continuous hsupp θ) hT.le
    have h4 : |cosTransform Ω θ| / T ≤ (T^3 * D) / (T * θ)^4 := by
      have hh := abs_cosTransform_le hab hΩ hsupp hθ.ne'
      rw [abs_of_pos hθ] at hh
      calc
        _ ≤ (D / θ^4) / T := div_le_div_of_nonneg_right hh hT.le
        _ = _ := by field_simp [hT.ne', hθ.ne']
    have h := (le_min h0 h4).trans
      (min_fourth_envelope (div_nonneg hM hT.le) (mul_nonneg (pow_nonneg hT.le _) hD)
        (mul_pos hT hθ))
    rw [div_le_iff₀ hT] at h
    calc
      _ ≤ (4 * C / (1 + T * θ)^2) * T := h
      _ = _ := by
        have he : T * θ = (2 * T / m) * ((n : ℝ) + 1) := by
          dsimp [θ]
          push_cast
          ring
        rw [he]
        ring
  calc
    _ ≤ ∑ n ∈ range R, (4 * T * C) * (1 / (1 + (2 * T / m) * ((n : ℝ) + 1))^2) :=
      sum_le_sum (fun n _ => hpt n)
    _ = (4 * T * C) * ∑ n ∈ range R, 1 / (1 + (2 * T / m) * ((n : ℝ) + 1))^2 :=
      (mul_sum ..).symm
    _ ≤ (4 * T * C) * (1 / (2 * T / m)) :=
      mul_le_mul_of_nonneg_left (sum_inverse_square_affine_le (by positivity) R) (by positivity)
    _ = _ := by
      dsimp [C, M, D]
      field_simp [hT.ne', hm.ne']
      ring

end GaloisForLFunctions.TransThresholdPairCorrelation

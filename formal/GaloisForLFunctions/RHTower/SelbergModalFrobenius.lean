import Mathlib

open Set Filter Topology MeasureTheory

/-!
# Frobenius asymptotics of Maass Fourier modes at `y = 0`

For `y² a'' = (k² y² - s₀(1 - s₀)) a` the quantities `c₋ = (y a' - s₀ a) y^{s₀-1}` and
`c₊ = (y a' - (1 - s₀) a) y^{-s₀}` satisfy `c₋' = k² y^{s₀} a`, `c₊' = k² y^{1-s₀} a` (`hasDerivAt_cm`,
`hasDerivAt_cp`) and `a = (c₋ y^{1-s₀} - c₊ y^{s₀})/(1 - 2s₀)` (`decomp`). For bounded `a` both derivatives are
integrable at `0`, so `a(y) = α y^{1-s₀} + O(y^{s₀})` for `1/2 < s₀ ≤ 1` (`frobenius_asymptotics`).
-/

namespace GaloisForLFunctions.RHTower.SelbergModalFrobenius

variable {a a' a'' : ℝ → ℂ} {k s₀ : ℝ}

/-- The `y^{1-s₀}` coefficient `c₋(y) = (y a'(y) - s₀ a(y)) y^{s₀-1}`. -/
noncomputable def cm (a a' : ℝ → ℂ) (s₀ y : ℝ) : ℂ := ((y : ℂ) * a' y - s₀ * a y) * ((y ^ (s₀ - 1) : ℝ) : ℂ)

/-- The `y^{s₀}` coefficient `c₊(y) = (y a'(y) - (1 - s₀) a(y)) y^{-s₀}`. -/
noncomputable def cp (a a' : ℝ → ℂ) (s₀ y : ℝ) : ℂ := ((y : ℂ) * a' y - (1 - s₀) * a y) * ((y ^ (-s₀) : ℝ) : ℂ)

theorem hasDerivAt_rpow_c {y r : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => ((t ^ r : ℝ) : ℂ)) ((r * y ^ (r - 1) : ℝ) : ℂ) y := by
  have := (Real.hasDerivAt_rpow_const (Or.inl hy.ne') : HasDerivAt (fun t => t ^ r) (r * y ^ (r - 1)) y)
  exact this.ofReal_comp

/-- `c₋' = k² y^{s₀} a`, using `y² a'' = (k² y² - s₀(1 - s₀)) a`. -/
theorem hasDerivAt_cm {y : ℝ} (hy : 0 < y) (ha : HasDerivAt a (a' y) y) (ha' : HasDerivAt a' (a'' y) y)
    (hode : (y : ℂ) ^ 2 * a'' y = ((k ^ 2 * y ^ 2 - s₀ * (1 - s₀) : ℝ) : ℂ) * a y) :
    HasDerivAt (cm a a' s₀) ((k ^ 2 * y ^ s₀ : ℝ) * a y) y := by
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y := by
    simpa using (hasDerivAt_id y).ofReal_comp
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * a' t - s₀ * a t) (1 * a' y + y * a'' y - s₀ * a' y) y :=
    (hid.fun_mul ha').sub (ha.const_mul (s₀ : ℂ))
  have h2 := hasDerivAt_rpow_c (r := s₀ - 1) hy
  have h3 := h1.fun_mul h2
  unfold cm
  refine h3.congr_deriv ?_
  have e1 : ((y ^ (s₀ - 1) : ℝ) : ℂ) = (y : ℂ) * ((y ^ (s₀ - 2) : ℝ) : ℂ) := by
    rw [show s₀ - 1 = 1 + (s₀ - 2) by ring, Real.rpow_add hy, Real.rpow_one]; push_cast; ring
  have e2 : ((y ^ s₀ : ℝ) : ℂ) = (y : ℂ) ^ 2 * ((y ^ (s₀ - 2) : ℝ) : ℂ) := by
    rw [show s₀ = 2 + (s₀ - 2) by ring, Real.rpow_add hy]; norm_num
  rw [show s₀ - 1 - 1 = s₀ - 2 by ring, e1]
  push_cast
  rw [e2]
  push_cast at hode
  linear_combination (((y ^ (s₀ - 2) : ℝ) : ℂ)) * hode

/-- `c₊' = k² y^{1-s₀} a`. -/
theorem hasDerivAt_cp {y : ℝ} (hy : 0 < y) (ha : HasDerivAt a (a' y) y) (ha' : HasDerivAt a' (a'' y) y)
    (hode : (y : ℂ) ^ 2 * a'' y = ((k ^ 2 * y ^ 2 - s₀ * (1 - s₀) : ℝ) : ℂ) * a y) :
    HasDerivAt (cp a a' s₀) ((k ^ 2 * y ^ (1 - s₀) : ℝ) * a y) y := by
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y := by
    simpa using (hasDerivAt_id y).ofReal_comp
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * a' t - (1 - s₀) * a t)
      (1 * a' y + y * a'' y - (1 - s₀) * a' y) y :=
    (hid.fun_mul ha').sub (ha.const_mul ((1 - s₀ : ℝ) : ℂ) |> fun h => by simpa using h)
  have h2 := hasDerivAt_rpow_c (r := -s₀) hy
  have h3 := h1.fun_mul h2
  unfold cp
  refine h3.congr_deriv ?_
  set Y := ((y ^ (-s₀ - 1) : ℝ) : ℂ)
  have e1 : ((y ^ (-s₀) : ℝ) : ℂ) = (y : ℂ) * Y := by
    rw [show -s₀ = 1 + (-s₀ - 1) by ring, Real.rpow_add hy, Real.rpow_one]; push_cast; simp [Y]
  have e2 : ((y ^ (1 - s₀) : ℝ) : ℂ) = (y : ℂ) ^ 2 * Y := by
    rw [show 1 - s₀ = 2 + (-s₀ - 1) by ring, Real.rpow_add hy]; norm_num
    exact Or.inl rfl
  rw [e1]
  push_cast
  rw [e2]
  push_cast at hode
  linear_combination Y * hode

/-- The decomposition `a = (c₋ y^{1-s₀} - c₊ y^{s₀}) / (1 - 2 s₀)`. -/
theorem decomp {y : ℝ} (hy : 0 < y) (hs : s₀ ≠ 1 / 2) :
    a y = (cm a a' s₀ y * ((y ^ (1 - s₀) : ℝ) : ℂ) - cp a a' s₀ y * ((y ^ s₀ : ℝ) : ℂ)) / (1 - 2 * s₀) := by
  have h12 : (1 - 2 * (s₀ : ℂ)) ≠ 0 := by
    intro h; apply hs
    have : (1 - 2 * s₀ : ℝ) = 0 := by exact_mod_cast h
    linarith
  have ha : ((y ^ (s₀ - 1) : ℝ) : ℂ) * ((y ^ (1 - s₀) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hy]; simp
  have hb : ((y ^ (-s₀) : ℝ) : ℂ) * ((y ^ s₀ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hy]; simp
  rw [eq_div_iff h12]
  unfold cm cp
  linear_combination (-((y : ℂ) * a' y - s₀ * a y)) * ha + ((y : ℂ) * a' y - (1 - s₀) * a y) * hb

/-- A continuous function on `(0, 1]` bounded by `K` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_of_bdd {D : ℝ → ℂ} (hc : ContinuousOn D (Ioc 0 1)) {K : ℝ}
    (hK : ∀ y ∈ Ioc (0 : ℝ) 1, ‖D y‖ ≤ K) : IntervalIntegrable D volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := isFiniteMeasure_restrict.mpr (by simp)
  exact Integrable.mono' (integrable_const K) (hc.aestronglyMeasurable measurableSet_Ioc)
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hK))

/-- **Frobenius asymptotics at `0`.** If `y² a'' = (k² y² - s₀(1-s₀)) a` on `(0, 1]` with `1/2 < s₀ ≤ 1` and
`|a| ≤ M` there, then `a(y) = α y^{1-s₀} + O(y^{s₀})` as `y → 0`. -/
theorem frobenius_asymptotics (hs1 : 1 / 2 < s₀) (hs2 : s₀ ≤ 1) {M : ℝ}
    (ha : ∀ y ∈ Ioc (0 : ℝ) 1, HasDerivAt a (a' y) y) (ha' : ∀ y ∈ Ioc (0 : ℝ) 1, HasDerivAt a' (a'' y) y)
    (hode : ∀ y ∈ Ioc (0 : ℝ) 1, (y : ℂ) ^ 2 * a'' y = ((k ^ 2 * y ^ 2 - s₀ * (1 - s₀) : ℝ) : ℂ) * a y)
    (hM : ∀ y ∈ Ioc (0 : ℝ) 1, ‖a y‖ ≤ M) :
    ∃ α : ℂ, ∃ C : ℝ, ∀ y ∈ Ioc (0 : ℝ) 1, ‖a y - α * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ ≤ C * y ^ s₀ ∧
      ‖((y : ℂ) * a' y - s₀ * a y) - (1 - 2 * s₀) * α * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ ≤ C * y ^ s₀ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 ⟨one_pos, le_rfl⟩)
  set Dm : ℝ → ℂ := fun y => ((k ^ 2 * y ^ s₀ : ℝ) : ℂ) * a y
  set Dp : ℝ → ℂ := fun y => ((k ^ 2 * y ^ (1 - s₀) : ℝ) : ℂ) * a y
  have hcont : ContinuousOn a (Ioc 0 1) := fun y hy => (ha y hy).continuousAt.continuousWithinAt
  have hbd : ∀ r : ℝ, 0 ≤ r → ∀ y ∈ Ioc (0 : ℝ) 1, ‖((k ^ 2 * y ^ r : ℝ) : ℂ) * a y‖ ≤ k ^ 2 * M := by
    intro r hr y hy
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg k) (Real.rpow_nonneg hy.1.le r))]
    have h1 : y ^ r ≤ 1 := Real.rpow_le_one hy.1.le hy.2 hr
    have := hM y hy
    calc k ^ 2 * y ^ r * ‖a y‖ ≤ k ^ 2 * 1 * M := by gcongr
      _ = k ^ 2 * M := by ring
  have hDmc : ContinuousOn Dm (Ioc 0 1) := by
    apply ContinuousOn.mul _ hcont
    exact (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.mul (continuousOn_id.rpow_const (fun y hy => Or.inl hy.1.ne'))))
  have hDpc : ContinuousOn Dp (Ioc 0 1) := by
    apply ContinuousOn.mul _ hcont
    exact (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.mul (continuousOn_id.rpow_const (fun y hy => Or.inl hy.1.ne'))))
  have hDmi := intervalIntegrable_of_bdd hDmc (hbd s₀ (by linarith))
  have hDpi := intervalIntegrable_of_bdd hDpc (hbd (1 - s₀) (by linarith))
  -- FTC on `[y, 1]`
  have hftc : ∀ (c D : ℝ → ℂ), IntervalIntegrable D volume 0 1 →
      (∀ y ∈ Ioc (0 : ℝ) 1, HasDerivAt c (D y) y) → ∀ y ∈ Ioc (0 : ℝ) 1,
      c y = c 1 - ∫ t in y..1, D t := by
    intro c D hDi hc y hy
    have hsub : uIcc y 1 ⊆ Ioc 0 1 := by
      rw [uIcc_of_le hy.2]; exact fun t ht => ⟨hy.1.trans_le ht.1, ht.2⟩
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hc t (hsub ht))
      (hDi.mono_set (by rw [uIcc_of_le hy.2, uIcc_of_le zero_le_one]; exact Icc_subset_Icc hy.1.le le_rfl))]
    ring
  have hcm := hftc (cm a a' s₀) Dm hDmi (fun y hy => hasDerivAt_cm hy.1 (ha y hy) (ha' y hy) (hode y hy))
  have hcp := hftc (cp a a' s₀) Dp hDpi (fun y hy => hasDerivAt_cp hy.1 (ha y hy) (ha' y hy) (hode y hy))
  set α₀ := cm a a' s₀ 1 - ∫ t in (0 : ℝ)..1, Dm t
  have h12 : (1 - 2 * s₀ : ℝ) ≠ 0 := by linarith
  refine ⟨α₀ / (1 - 2 * s₀), (k ^ 2 * M + (‖cp a a' s₀ 1‖ + k ^ 2 * M)) / |1 - 2 * s₀| + k ^ 2 * M,
    fun y hy => ?_⟩
  have hy0 := hy.1
  have hy1 := hy.2
  -- `c₋(y) - α₀ = ∫_0^y D₋`
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (hDmi.mono_set (by rw [uIcc_of_le hy0.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hy1))
    (hDmi.mono_set (by rw [uIcc_of_le hy1, uIcc_of_le zero_le_one]; exact Icc_subset_Icc hy0.le le_rfl))
  have hcmα : cm a a' s₀ y - α₀ = ∫ t in (0 : ℝ)..y, Dm t := by
    rw [hcm y hy]; simp only [α₀]; rw [← hadj]; ring
  have hcmb : ‖cm a a' s₀ y - α₀‖ ≤ k ^ 2 * M * y := by
    rw [hcmα]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := y) (C := k ^ 2 * M)
      (f := Dm) (fun t ht => by
        rw [uIoc_of_le hy0.le] at ht
        exact hbd s₀ (by linarith) t ⟨ht.1, ht.2.trans hy1⟩)
    simpa [abs_of_pos hy0] using this
  have hcpb : ‖cp a a' s₀ y‖ ≤ ‖cp a a' s₀ 1‖ + k ^ 2 * M := by
    rw [hcp y hy]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := 1) (C := k ^ 2 * M)
      (f := Dp) (fun t ht => by
        rw [uIoc_of_le hy1] at ht
        exact hbd (1 - s₀) (by linarith) t ⟨hy0.trans ht.1, ht.2⟩)
    have hab : |1 - y| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
    have hk : 0 ≤ k ^ 2 * M := by positivity
    calc ‖cp a a' s₀ 1 - ∫ t in y..1, Dp t‖ ≤ ‖cp a a' s₀ 1‖ + ‖∫ t in y..1, Dp t‖ := norm_sub_le _ _
      _ ≤ ‖cp a a' s₀ 1‖ + k ^ 2 * M * |1 - y| := by gcongr
      _ ≤ ‖cp a a' s₀ 1‖ + k ^ 2 * M := by nlinarith
  -- assemble
  have hdec := decomp (a := a) (a' := a') hy0 (s₀ := s₀) (by linarith)
  have h12c : (1 - 2 * (s₀ : ℂ)) ≠ 0 := by exact_mod_cast h12
  have hdiff : a y - α₀ / (1 - 2 * s₀) * ((y ^ (1 - s₀) : ℝ) : ℂ) =
      ((cm a a' s₀ y - α₀) * ((y ^ (1 - s₀) : ℝ) : ℂ) - cp a a' s₀ y * ((y ^ s₀ : ℝ) : ℂ)) / (1 - 2 * s₀) := by
    rw [hdec]; field_simp; ring
  have hfirst : ‖a y - α₀ / (1 - 2 * s₀) * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ ≤
      (k ^ 2 * M + (‖cp a a' s₀ 1‖ + k ^ 2 * M)) / |1 - 2 * s₀| * y ^ s₀ := by
   rw [hdiff, norm_div]
   have hden : ‖(1 - 2 * (s₀ : ℂ))‖ = |1 - 2 * s₀| := by
     rw [show (1 - 2 * (s₀ : ℂ)) = ((1 - 2 * s₀ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
   rw [hden, div_le_iff₀ (abs_pos.mpr h12)]
   have hY1 : 0 ≤ y ^ (1 - s₀) := Real.rpow_nonneg hy0.le _
   have hYs : 0 ≤ y ^ s₀ := Real.rpow_nonneg hy0.le _
   have hyy : y * y ^ (1 - s₀) ≤ y ^ s₀ := by
     rw [show y * y ^ (1 - s₀) = y ^ (2 - s₀) by
       rw [show 2 - s₀ = 1 + (1 - s₀) by ring, Real.rpow_add hy0, Real.rpow_one]]
     exact Real.rpow_le_rpow_of_exponent_ge hy0 hy1 (by linarith)
   have hk : 0 ≤ k ^ 2 * M := by positivity
   calc ‖(cm a a' s₀ y - α₀) * ((y ^ (1 - s₀) : ℝ) : ℂ) - cp a a' s₀ y * ((y ^ s₀ : ℝ) : ℂ)‖
       ≤ ‖cm a a' s₀ y - α₀‖ * y ^ (1 - s₀) + ‖cp a a' s₀ y‖ * y ^ s₀ := by
         refine (norm_sub_le _ _).trans (le_of_eq ?_)
         rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
           abs_of_nonneg hY1, abs_of_nonneg hYs]
     _ ≤ k ^ 2 * M * y * y ^ (1 - s₀) + (‖cp a a' s₀ 1‖ + k ^ 2 * M) * y ^ s₀ := by gcongr
     _ ≤ k ^ 2 * M * y ^ s₀ + (‖cp a a' s₀ 1‖ + k ^ 2 * M) * y ^ s₀ := by
         rw [mul_assoc (k ^ 2 * M)]; gcongr
     _ = _ := by field_simp

  have hk0 : 0 ≤ k ^ 2 * M := by positivity
  have hsecond : ‖((y : ℂ) * a' y - s₀ * a y) - (1 - 2 * s₀) * (α₀ / (1 - 2 * s₀)) * ((y ^ (1 - s₀) : ℝ) : ℂ)‖
      ≤ k ^ 2 * M * y ^ s₀ := by
    have hc : (y : ℂ) * a' y - s₀ * a y = cm a a' s₀ y * ((y ^ (1 - s₀) : ℝ) : ℂ) := by
      unfold cm
      rw [mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hy0]; simp
    rw [hc, mul_div_cancel₀ _ h12c, ← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hy0.le _)]
    have hyy' : y * y ^ (1 - s₀) ≤ y ^ s₀ := by
      rw [show y * y ^ (1 - s₀) = y ^ (2 - s₀) by
        rw [show 2 - s₀ = 1 + (1 - s₀) by ring, Real.rpow_add hy0, Real.rpow_one]]
      exact Real.rpow_le_rpow_of_exponent_ge hy0 hy1 (by linarith)
    calc ‖cm a a' s₀ y - α₀‖ * y ^ (1 - s₀) ≤ k ^ 2 * M * y * y ^ (1 - s₀) :=
          mul_le_mul_of_nonneg_right hcmb (Real.rpow_nonneg hy0.le _)
      _ ≤ k ^ 2 * M * y ^ s₀ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hyy' hk0
  have hys : 0 ≤ y ^ s₀ := Real.rpow_nonneg hy0.le _
  have hC1 : 0 ≤ (k ^ 2 * M + (‖cp a a' s₀ 1‖ + k ^ 2 * M)) / |1 - 2 * s₀| := by positivity
  refine ⟨hfirst.trans ?_, hsecond.trans ?_⟩
  · nlinarith
  · nlinarith
end GaloisForLFunctions.RHTower.SelbergModalFrobenius

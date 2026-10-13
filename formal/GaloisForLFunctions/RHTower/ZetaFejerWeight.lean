import GaloisForLFunctions.HTGeometry.FejerLatticeVanishing

/-!
# A band-limited Fejér window

For a band `b > 0` let `Λ_b(ξ) = (1 − |ξ|/b)⁺` and

`F_b(v) = ∫_{−b}^{b} Λ_b(ξ) e^{iξv} dξ = (2 − 2cos(bv))/(b v²)`   (`F_b(0) = b`)

(`fejerBandProfile`, `integral_triangle_cexp_eq_profile`).  `F_b` is nonnegative, at most `b`, at most `4/(b v²)`, at
least `(43/48) b` on `|v| ≤ 1/b`, and integrable with total mass `κ_b > 0` (`fejerMass`).

The window of an interval `[s₀, s₁]` is the normalised average `W(s) = κ_b⁻¹ ∫_{s₀}^{s₁} F_b(s − u) du`
(`fejerWindow`): `0 ≤ W ≤ 1`, `W(s) ≥ 1 − 4/(κ_b b)·(1/(s − s₀) + 1/(s₁ − s))` inside, and `W(s) ≤ 4/(κ_b b D)` at
distance `D` outside.  It is the inverse transform of `ψ(ξ) = κ_b⁻¹ Λ_b(ξ) ∫_{s₀}^{s₁} e^{−iξu} du`
(`integral_fejerPsi_mul_cexp`), which is continuous, supported in `[−b, b]`, and has first absolute moment
`∫ |ξ| ‖ψ(ξ)‖ dξ ≤ 2b/κ_b` (`integral_abs_mul_norm_fejerPsi_le`).

Fourier inversion for the triangle gives `∫ F_b(v) e^{−iyv} dv = 2π Λ_b(y)` (`integral_fejerBandProfile_mul_cexp`), so
`κ_b = 2π` (`fejerMass_eq`) and `∫ W(τ) e^{−iyτ} dτ = κ_b⁻¹ 2π Λ_b(y) ∫_{s₀}^{s₁} e^{−iyu} du`
(`integral_fejerWindow_mul_cexp`): the window has no Fourier mass at frequencies `|y| ≥ b`
(`integral_fejerWindow_mul_cexp_eq_zero`).  In particular, for `b < log 2` every prime frequency `log n` is
invisible to `∫ W(τ) P_X(τ) dτ`.
-/

open Complex MeasureTheory Real Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

namespace FejerWeight

variable {b : ℝ}

/-- `F_b(v) = (2 − 2cos(bv))/(b v²)`, `F_b(0) = b`. -/
def fejerBandProfile (b v : ℝ) : ℝ := if v = 0 then b else (2 - 2 * Real.cos (v * b)) / (v ^ 2 * b)

/-- `∫_{−b}^{b} Λ_b(ξ) e^{iξv} dξ = F_b(v)`. -/
theorem integral_triangle_cexp_eq_profile (hb : 0 < b) (v : ℝ) :
    ∫ ξ in (-b)..b, ((triangleFn b ξ : ℝ) : ℂ) * cexp (I * ξ * v) = (fejerBandProfile b v : ℂ) := by
  by_cases hv : v = 0
  · subst hv
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, fejerBandProfile, if_true]
    exact integral_triangleFn hb
  · have h := integral_triangleFn_cexp hb (ω := -v) (neg_ne_zero.mpr hv)
    have e : ∀ ξ : ℝ, cexp (-((-v * ξ : ℝ) : ℂ) * I) = cexp (I * ξ * v) := by
      intro ξ; congr 1; push_cast; ring
    simp_rw [e] at h
    rw [h, fejerBandProfile, if_neg hv]
    congr 1
    rw [neg_mul, Real.cos_neg, neg_sq]

theorem fejerBandProfile_nonneg (hb : 0 < b) (v : ℝ) : 0 ≤ fejerBandProfile b v := by
  unfold fejerBandProfile
  split_ifs with hv
  · exact hb.le
  · have := Real.cos_le_one (v * b)
    have : 0 < v ^ 2 * b := by positivity
    exact div_nonneg (by linarith) this.le

theorem fejerBandProfile_le (hb : 0 < b) (v : ℝ) : fejerBandProfile b v ≤ b := by
  unfold fejerBandProfile
  split_ifs with hv
  · exact le_rfl
  · have hpos : 0 < v ^ 2 * b := by positivity
    rw [div_le_iff₀ hpos]
    have h := Real.one_sub_sq_div_two_le_cos (x := v * b)
    nlinarith [sq_nonneg (v * b)]

theorem fejerBandProfile_le_inv (hb : 0 < b) {v : ℝ} (hv : v ≠ 0) :
    fejerBandProfile b v ≤ 4 / (v ^ 2 * b) := by
  unfold fejerBandProfile
  rw [if_neg hv]
  have hpos : 0 < v ^ 2 * b := by positivity
  apply div_le_div_of_nonneg_right _ hpos.le
  linarith [Real.neg_one_le_cos (v * b)]

theorem fejerBandProfile_le_lorentz (hb : 0 < b) (v : ℝ) :
    fejerBandProfile b v ≤ (2 * b + 8 / b) * (1 + v ^ 2)⁻¹ := by
  have hpos : 0 < 1 + v ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  rcases le_or_gt (v ^ 2) 1 with h | h
  · have h1 := fejerBandProfile_le hb v
    have h2 : 0 ≤ fejerBandProfile b v := fejerBandProfile_nonneg hb v
    have : 0 < 8 / b := by positivity
    nlinarith
  · have hv : v ≠ 0 := by rintro rfl; norm_num at h
    have h1 := fejerBandProfile_le_inv hb hv
    have h2 : 0 ≤ fejerBandProfile b v := fejerBandProfile_nonneg hb v
    have hb8 : 0 < 8 / b := by positivity
    have e : 4 / (v ^ 2 * b) * (1 + v ^ 2) ≤ 8 / b := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hb]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h1 hpos.le]

theorem continuous_fejerBandProfile (hb : 0 < b) : Continuous (fejerBandProfile b) := by
  have h : (fun v : ℝ => ((fejerBandProfile b v : ℝ) : ℂ))
      = fun v : ℝ => ∫ ξ in (-b)..b, ((triangleFn b ξ : ℝ) : ℂ) * cexp (I * ξ * (v : ℂ)) := by
    funext v; rw [integral_triangle_cexp_eq_profile hb]
  have hc : Continuous (fun v : ℝ => ∫ ξ in (-b)..b, ((triangleFn b ξ : ℝ) : ℂ)
      * cexp (I * ξ * (v : ℂ))) := by
    have := continuous_triangleFn b
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (v : ℝ) (ξ : ℝ) => ((triangleFn b ξ : ℝ) : ℂ) * cexp (I * ξ * (v : ℂ)))
      (by fun_prop) continuous_const
  rw [← h] at hc
  exact Complex.continuous_re.comp hc |>.congr fun v => by simp

theorem integrable_fejerBandProfile (hb : 0 < b) : Integrable (fejerBandProfile b) := by
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (2 * b + 8 / b))
    (continuous_fejerBandProfile hb).aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (fejerBandProfile_nonneg hb v)]
  exact fejerBandProfile_le_lorentz hb v

/-- The total mass `κ_b = ∫ F_b` (`fejerMass`). -/
def fejerMass (b : ℝ) : ℝ := ∫ v, fejerBandProfile b v

theorem fejerBandProfile_ge (hb : 0 < b) {v : ℝ} (hv : |v| ≤ 1 / b) :
    (43 / 48) * b ≤ fejerBandProfile b v := by
  unfold fejerBandProfile
  split_ifs with h0
  · linarith
  · have hpos : 0 < v ^ 2 * b := by positivity
    rw [le_div_iff₀ hpos]
    have hx : |v * b| ≤ 1 := by
      rw [abs_mul, abs_of_pos hb]
      calc |v| * b ≤ 1 / b * b := mul_le_mul_of_nonneg_right hv hb.le
        _ = 1 := by field_simp
    have hc := Real.cos_bound hx
    have h4 : |v * b| ^ 4 ≤ (v * b) ^ 2 := by
      rw [show |v * b| ^ 4 = ((v * b) ^ 2) ^ 2 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]]
      have : (v * b) ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (v * b)]
      nlinarith [sq_nonneg (v * b)]
    have := (abs_le.mp hc).2
    nlinarith

theorem fejerMass_pos (hb : 0 < b) : 0 < fejerMass b := by
  unfold fejerMass
  have hI := integrable_fejerBandProfile hb
  have h1 : ∫ v in Icc (-(1 / b)) (1 / b), fejerBandProfile b v ≤ ∫ v, fejerBandProfile b v :=
    setIntegral_le_integral hI (Filter.Eventually.of_forall fun v => fejerBandProfile_nonneg hb v)
  have h2 : ∫ v in Icc (-(1 / b)) (1 / b), (43 / 48) * b ≤ ∫ v in Icc (-(1 / b)) (1 / b), fejerBandProfile b v := by
    refine setIntegral_mono_on continuous_const.integrableOn_Icc hI.integrableOn measurableSet_Icc
      fun v hv => ?_
    exact fejerBandProfile_ge hb (abs_le.mpr ⟨hv.1, hv.2⟩)
  have h3 : ∫ v in Icc (-(1 / b)) (1 / b), (43 / 48) * b = (43 / 48) * b * (2 / b) := by
    have hb1 : 0 < 1 / b := by positivity
    rw [setIntegral_const, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
      smul_eq_mul]
    field_simp
    ring
  have h4 : 0 < (43 / 48) * b * (2 / b) := by positivity
  linarith

theorem fejerBandProfile_neg (b v : ℝ) : fejerBandProfile b (-v) = fejerBandProfile b v := by
  unfold fejerBandProfile
  by_cases hv : v = 0
  · simp [hv]
  · rw [if_neg (neg_ne_zero.mpr hv), if_neg hv, neg_mul, Real.cos_neg, neg_sq]

/-- `∫_{v > D} F_b ≤ 4/(bD)`. -/
theorem setIntegral_Ioi_fejerBandProfile_le (hb : 0 < b) {D : ℝ} (hD : 0 < D) :
    ∫ v in Ioi D, fejerBandProfile b v ≤ 4 / (b * D) := by
  have hcmp : ∀ v ∈ Ioi D, fejerBandProfile b v ≤ (4 / b) * v ^ (-2 : ℝ) := by
    intro v hv
    have hv0 : 0 < v := lt_trans hD hv
    rw [Real.rpow_neg hv0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc fejerBandProfile b v ≤ 4 / (v ^ 2 * b) := fejerBandProfile_le_inv hb hv0.ne'
      _ = (4 / b) * (v ^ 2)⁻¹ := by field_simp
  have hint2 : IntegrableOn (fun v : ℝ => (4 / b) * v ^ (-2 : ℝ)) (Ioi D) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hD).const_mul _
  calc ∫ v in Ioi D, fejerBandProfile b v ≤ ∫ v in Ioi D, (4 / b) * v ^ (-2 : ℝ) :=
        setIntegral_mono_on (integrable_fejerBandProfile hb).integrableOn hint2 measurableSet_Ioi hcmp
    _ = 4 / (b * D) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hD]
        rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
        field_simp

/-- `∫_{v ≤ −D} F_b ≤ 4/(bD)`. -/
theorem setIntegral_Iic_fejerBandProfile_le (hb : 0 < b) {D : ℝ} (hD : 0 < D) :
    ∫ v in Iic (-D), fejerBandProfile b v ≤ 4 / (b * D) := by
  have h := integral_comp_neg_Iic (-D) (fejerBandProfile b)
  simp only [fejerBandProfile_neg, neg_neg] at h
  rw [h]
  exact setIntegral_Ioi_fejerBandProfile_le hb hD

/-- The window of `[s₀, s₁]`: `W(s) = κ_b⁻¹ ∫_{s−s₁}^{s−s₀} F_b = κ_b⁻¹ ∫_{s₀}^{s₁} F_b(s − u) du`. -/
def fejerWindow (b s₀ s₁ s : ℝ) : ℝ := (fejerMass b)⁻¹ * ∫ v in (s - s₁)..(s - s₀), fejerBandProfile b v

variable {s₀ s₁ : ℝ}

theorem fejerWindow_nonneg (hb : 0 < b) (h01 : s₀ ≤ s₁) (s : ℝ) : 0 ≤ fejerWindow b s₀ s₁ s := by
  unfold fejerWindow
  exact mul_nonneg (inv_nonneg.mpr (fejerMass_pos hb).le)
    (intervalIntegral.integral_nonneg (by linarith) fun v _ => fejerBandProfile_nonneg hb v)

theorem fejerWindow_le_one (hb : 0 < b) (h01 : s₀ ≤ s₁) (s : ℝ) : fejerWindow b s₀ s₁ s ≤ 1 := by
  unfold fejerWindow
  have hk := fejerMass_pos hb
  rw [inv_mul_le_iff₀ hk, mul_one, intervalIntegral.integral_of_le (by linarith)]
  exact setIntegral_le_integral (integrable_fejerBandProfile hb)
    (Filter.Eventually.of_forall fun v => fejerBandProfile_nonneg hb v)

/-- Inside the interval the window is close to one. -/
theorem one_sub_le_fejerWindow (hb : 0 < b) {s : ℝ} (h0 : s₀ < s) (h1 : s < s₁) :
    1 - (fejerMass b)⁻¹ * (4 / (b * (s₁ - s)) + 4 / (b * (s - s₀))) ≤ fejerWindow b s₀ s₁ s := by
  have hk := fejerMass_pos hb
  have hI := integrable_fejerBandProfile hb
  have hsplit1 : (∫ v in Iic (s - s₁), fejerBandProfile b v) + (∫ v in Ioi (s - s₁), fejerBandProfile b v)
      = fejerMass b := intervalIntegral.integral_Iic_add_Ioi hI.integrableOn hI.integrableOn
  have hsplit2 : (∫ v in (s - s₁)..(s - s₀), fejerBandProfile b v) + (∫ v in Ioi (s - s₀), fejerBandProfile b v)
      = ∫ v in Ioi (s - s₁), fejerBandProfile b v :=
    intervalIntegral.integral_interval_add_Ioi hI.integrableOn hI.integrableOn
  have hL := setIntegral_Iic_fejerBandProfile_le hb (D := s₁ - s) (by linarith)
  rw [neg_sub] at hL
  have hR := setIntegral_Ioi_fejerBandProfile_le hb (D := s - s₀) (by linarith)
  have e : (∫ v in (s - s₁)..(s - s₀), fejerBandProfile b v)
      = fejerMass b - (∫ v in Iic (s - s₁), fejerBandProfile b v) - (∫ v in Ioi (s - s₀), fejerBandProfile b v) := by
    linear_combination hsplit2 + hsplit1
  unfold fejerWindow
  rw [e]
  have e2 : (fejerMass b)⁻¹ * (fejerMass b - (∫ v in Iic (s - s₁), fejerBandProfile b v)
        - (∫ v in Ioi (s - s₀), fejerBandProfile b v))
      = 1 - (fejerMass b)⁻¹ * (∫ v in Iic (s - s₁), fejerBandProfile b v)
        - (fejerMass b)⁻¹ * (∫ v in Ioi (s - s₀), fejerBandProfile b v) := by
    field_simp
  rw [e2]
  have h2 : (fejerMass b)⁻¹ * (∫ v in Iic (s - s₁), fejerBandProfile b v) ≤ (fejerMass b)⁻¹ * (4 / (b * (s₁ - s))) :=
    mul_le_mul_of_nonneg_left hL (inv_nonneg.mpr hk.le)
  have h3 : (fejerMass b)⁻¹ * (∫ v in Ioi (s - s₀), fejerBandProfile b v) ≤ (fejerMass b)⁻¹ * (4 / (b * (s - s₀))) :=
    mul_le_mul_of_nonneg_left hR (inv_nonneg.mpr hk.le)
  linarith [mul_add (fejerMass b)⁻¹ (4 / (b * (s₁ - s))) (4 / (b * (s - s₀)))]

/-- To the right of the interval, at distance `D`, the window is at most `4/(κ_b b D)`. -/
theorem fejerWindow_le_right (hb : 0 < b) {s D : ℝ} (hD : 0 < D) (hs : s₁ + D ≤ s) :
    fejerWindow b s₀ s₁ s ≤ (fejerMass b)⁻¹ * (4 / (b * D)) := by
  have hk := fejerMass_pos hb
  have hI := integrable_fejerBandProfile hb
  have hsplit : (∫ v in (s - s₁)..(s - s₀), fejerBandProfile b v) + (∫ v in Ioi (s - s₀), fejerBandProfile b v)
      = ∫ v in Ioi (s - s₁), fejerBandProfile b v :=
    intervalIntegral.integral_interval_add_Ioi hI.integrableOn hI.integrableOn
  have hpos : 0 ≤ ∫ v in Ioi (s - s₀), fejerBandProfile b v :=
    setIntegral_nonneg measurableSet_Ioi fun v _ => fejerBandProfile_nonneg hb v
  have hmono : ∫ v in Ioi (s - s₁), fejerBandProfile b v ≤ ∫ v in Ioi D, fejerBandProfile b v :=
    setIntegral_mono_set hI.integrableOn
      (Filter.Eventually.of_forall fun v => fejerBandProfile_nonneg hb v)
      (Filter.Eventually.of_forall fun v hv => lt_of_le_of_lt (by linarith) hv)
  have hR := setIntegral_Ioi_fejerBandProfile_le hb hD
  unfold fejerWindow
  exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hk.le)

/-- To the left of the interval, at distance `D`, the window is at most `4/(κ_b b D)`. -/
theorem fejerWindow_le_left (hb : 0 < b) {s D : ℝ} (hD : 0 < D) (hs : s + D ≤ s₀) :
    fejerWindow b s₀ s₁ s ≤ (fejerMass b)⁻¹ * (4 / (b * D)) := by
  have hrefl : fejerWindow b s₀ s₁ s = fejerWindow b (-s₁) (-s₀) (-s) := by
    unfold fejerWindow
    congr 1
    have h := intervalIntegral.integral_comp_neg (a := s - s₁) (b := s - s₀) (fejerBandProfile b)
    simp only [fejerBandProfile_neg] at h
    rw [h]
    congr 1 <;> ring
  rw [hrefl]
  exact fejerWindow_le_right hb hD (by linarith)

/-! ### The Fourier side of the window -/

/-- `ψ(ξ) = κ_b⁻¹ Λ_b(ξ) ∫_{s₀}^{s₁} e^{−iξu} du`, supported in `[−b, b]`. -/
def fejerPsi (b s₀ s₁ ξ : ℝ) : ℂ :=
  (((fejerMass b)⁻¹ : ℝ) : ℂ) * ((triangleFn b ξ : ℝ) : ℂ) * ∫ u in s₀..s₁, cexp (-(I * ξ * u))

theorem fejerPsi_eq_zero (hb : 0 < b) {ξ : ℝ} (hξ : b ≤ |ξ|) : fejerPsi b s₀ s₁ ξ = 0 := by
  unfold fejerPsi; rw [triangleFn_eq_zero hb hξ]; simp

theorem continuous_fejerPsi (b s₀ s₁ : ℝ) : Continuous (fejerPsi b s₀ s₁) := by
  unfold fejerPsi
  have h1 := continuous_triangleFn b
  have h2 : Continuous fun ξ : ℝ => ∫ u in s₀..s₁, cexp (-(I * ξ * u)) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (f := fun (ξ : ℝ) (u : ℝ) => cexp (-(I * ξ * u))) (a₀ := s₀) (by fun_prop)
      (continuous_const (y := s₁))
  fun_prop

theorem norm_fejerPsi_le (hb : 0 < b) (h01 : s₀ ≤ s₁) (ξ : ℝ) :
    ‖fejerPsi b s₀ s₁ ξ‖ ≤ (fejerMass b)⁻¹ * (s₁ - s₀) := by
  have hk := fejerMass_pos hb
  unfold fejerPsi
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hk), abs_of_nonneg (triangleFn_nonneg b ξ)]
  have hI : ‖∫ u in s₀..s₁, cexp (-(I * ξ * u))‖ ≤ 1 * |s₁ - s₀| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => by
      rw [show -(I * (ξ : ℂ) * (u : ℂ)) = ((-(ξ * u) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
  rw [one_mul, abs_of_nonneg (by linarith)] at hI
  have ht := triangleFn_le_one hb ξ
  have h0 := triangleFn_nonneg b ξ
  calc (fejerMass b)⁻¹ * triangleFn b ξ * ‖∫ u in s₀..s₁, cexp (-(I * ξ * u))‖
      ≤ (fejerMass b)⁻¹ * 1 * (s₁ - s₀) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hk.le)) hI (norm_nonneg _)
        positivity
    _ = (fejerMass b)⁻¹ * (s₁ - s₀) := by ring

/-- `|ξ| ‖ψ(ξ)‖ ≤ 2 κ_b⁻¹ Λ_b(ξ)`: the transform of an interval is `(e^{−iξs₁} − e^{−iξs₀})/(−iξ)`. -/
theorem abs_mul_norm_fejerPsi_le (hb : 0 < b) (ξ : ℝ) :
    |ξ| * ‖fejerPsi b s₀ s₁ ξ‖ ≤ 2 * (fejerMass b)⁻¹ * triangleFn b ξ := by
  have hk := fejerMass_pos hb
  by_cases hξ : ξ = 0
  · subst hξ; simp only [abs_zero, zero_mul]; have := triangleFn_nonneg b 0; positivity
  have hc : (-(I * (ξ : ℂ))) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, mul_eq_zero, I_ne_zero, Complex.ofReal_eq_zero, hξ, or_self,
      not_false_eq_true]
  have hint : ∫ u in s₀..s₁, cexp (-(I * ξ * u))
      = (cexp (-(I * ξ) * s₁) - cexp (-(I * ξ) * s₀)) / (-(I * ξ)) := by
    rw [← integral_exp_mul_complex hc]
    congr 1 with u; ring_nf
  have hnum : ‖cexp (-(I * ξ) * s₁) - cexp (-(I * ξ) * s₀)‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [show -(I * (ξ : ℂ)) * (s₁ : ℂ) = ((-(ξ * s₁)) : ℝ) * I by push_cast; ring,
      show -(I * (ξ : ℂ)) * (s₀ : ℂ) = ((-(ξ * s₀)) : ℝ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hden : ‖-(I * (ξ : ℂ))‖ = |ξ| := by
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hξp : 0 < |ξ| := abs_pos.mpr hξ
  unfold fejerPsi
  rw [hint, norm_mul, norm_mul, norm_div, hden, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk),
    abs_of_nonneg (triangleFn_nonneg b ξ)]
  have ht := triangleFn_nonneg b ξ
  calc |ξ| * ((fejerMass b)⁻¹ * triangleFn b ξ
        * (‖cexp (-(I * ξ) * s₁) - cexp (-(I * ξ) * s₀)‖ / |ξ|))
      = (fejerMass b)⁻¹ * triangleFn b ξ * ‖cexp (-(I * ξ) * s₁) - cexp (-(I * ξ) * s₀)‖ := by
        field_simp
    _ ≤ (fejerMass b)⁻¹ * triangleFn b ξ * 2 :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = 2 * (fejerMass b)⁻¹ * triangleFn b ξ := by ring

/-- **The window is the inverse transform of `ψ`:** `∫ ψ(ξ) e^{iξs} dξ = W(s)`. -/
theorem integral_fejerPsi_mul_cexp (hb : 0 < b) (h01 : s₀ ≤ s₁) (s : ℝ) :
    ∫ ξ, fejerPsi b s₀ s₁ ξ * cexp (I * ξ * s) = (fejerWindow b s₀ s₁ s : ℂ) := by
  have hk := fejerMass_pos hb
  -- restrict to the band
  have hsupp : ∀ ξ ∉ Ioc (-b) b, fejerPsi b s₀ s₁ ξ * cexp (I * ξ * s) = 0 := by
    intro ξ hξ
    rw [fejerPsi_eq_zero hb, zero_mul]
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hξ
    rcases hξ with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    ← intervalIntegral.integral_of_le (by linarith)]
  -- the integrand as an inner integral
  set g : ℝ → ℝ → ℂ := fun ξ u => ((triangleFn b ξ : ℝ) : ℂ) * cexp (I * ξ * ((s - u : ℝ) : ℂ))
    with hg
  have hpt : ∀ ξ : ℝ, fejerPsi b s₀ s₁ ξ * cexp (I * ξ * s)
      = (((fejerMass b)⁻¹ : ℝ) : ℂ) * ∫ u in Ioc s₀ s₁, g ξ u := by
    intro ξ
    unfold fejerPsi
    rw [intervalIntegral.integral_of_le h01, mul_assoc, mul_assoc]
    congr 1
    rw [← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hg]
    rw [mul_assoc]
    congr 1
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  -- swap the two integrals
  haveI : IsFiniteMeasure (volume.restrict (Ioc s₀ s₁)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (-b) b)) :=
    isFiniteMeasure_restrict.mpr (by rw [Set.uIoc]; exact measure_Ioc_lt_top.ne)
  have hgc : Continuous (Function.uncurry g) := by
    have := continuous_triangleFn b
    simp only [hg]
    fun_prop
  have hgint : Integrable (Function.uncurry g)
      ((volume.restrict (Set.uIoc (-b) b)).prod (volume.restrict (Ioc s₀ s₁))) := by
    refine Integrable.of_bound hgc.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun q => ?_)
    show ‖((triangleFn b q.1 : ℝ) : ℂ) * cexp (I * (q.1 : ℂ) * ((s - q.2 : ℝ) : ℂ))‖ ≤ 1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (triangleFn_nonneg b _),
      show I * ((q.1 : ℝ) : ℂ) * ((s - q.2 : ℝ) : ℂ) = ((q.1 * (s - q.2) : ℝ) : ℂ) * I by
        push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact triangleFn_le_one hb _
  rw [intervalIntegral_integral_swap hgint]
  -- the inner integral is the profile
  have hinner : ∀ u : ℝ, ∫ ξ in (-b)..b, g ξ u = (fejerBandProfile b (s - u) : ℂ) := by
    intro u
    rw [← integral_triangle_cexp_eq_profile hb (s - u)]
  simp_rw [hinner]
  rw [← intervalIntegral.integral_of_le h01, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_comp_sub_left (fun v => fejerBandProfile b v) s]
  unfold fejerWindow
  push_cast
  ring

theorem hasCompactSupport_fejerPsi (hb : 0 < b) : HasCompactSupport (fejerPsi b s₀ s₁) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -b) (b := b)) ?_
  intro ξ hξ
  rw [Function.mem_support] at hξ
  by_contra h
  apply hξ
  apply fejerPsi_eq_zero hb
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem integrable_fejerPsi (hb : 0 < b) : Integrable (fejerPsi b s₀ s₁) :=
  (continuous_fejerPsi b s₀ s₁).integrable_of_hasCompactSupport (hasCompactSupport_fejerPsi hb)

theorem integrable_abs_mul_norm_fejerPsi (hb : 0 < b) :
    Integrable fun ξ => |ξ| * ‖fejerPsi b s₀ s₁ ξ‖ := by
  have hc := continuous_fejerPsi b s₀ s₁
  exact (continuous_abs.mul hc.norm).integrable_of_hasCompactSupport
    (hasCompactSupport_fejerPsi hb).norm.mul_left

theorem integral_triangleFn_real (hb : 0 < b) : ∫ ξ, triangleFn b ξ = b := by
  have hsupp : ∀ ξ ∉ Ioc (-b) b, triangleFn b ξ = 0 := by
    intro ξ hξ
    apply triangleFn_eq_zero hb
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hξ
    rcases hξ with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    ← intervalIntegral.integral_of_le (by linarith)]
  have h := integral_triangleFn hb
  rw [intervalIntegral.integral_ofReal] at h
  exact_mod_cast h

/-- **The first absolute moment of `ψ`:** `∫ |ξ| ‖ψ(ξ)‖ dξ ≤ 2b/κ_b`. -/
theorem integral_abs_mul_norm_fejerPsi_le (hb : 0 < b) :
    ∫ ξ, |ξ| * ‖fejerPsi b s₀ s₁ ξ‖ ≤ 2 * (fejerMass b)⁻¹ * b := by
  have hΛ : Integrable (triangleFn b) :=
    (continuous_triangleFn b).integrable_of_hasCompactSupport (by
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -b) (b := b)) ?_
      intro ξ hξ
      rw [Function.mem_support] at hξ
      by_contra h
      apply hξ
      apply triangleFn_eq_zero hb
      rw [mem_Icc, not_and_or, not_le, not_le] at h
      rcases h with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)
  calc ∫ ξ, |ξ| * ‖fejerPsi b s₀ s₁ ξ‖ ≤ ∫ ξ, 2 * (fejerMass b)⁻¹ * triangleFn b ξ :=
        integral_mono (integrable_abs_mul_norm_fejerPsi hb) (hΛ.const_mul _)
          fun ξ => abs_mul_norm_fejerPsi_le hb ξ
    _ = 2 * (fejerMass b)⁻¹ * b := by rw [integral_const_mul, integral_triangleFn_real hb]

/-! ### The transform of the window is band-limited -/

/-- `F_b(v) = b sinc(bv/2)²`. -/
theorem fejerBandProfile_eq_sinc (hb : 0 < b) (v : ℝ) :
    fejerBandProfile b v = b * Real.sinc (b * v / 2) ^ 2 := by
  unfold fejerBandProfile
  by_cases hv : v = 0
  · simp [hv]
  · rw [if_neg hv, Real.sinc_of_ne_zero (by positivity)]
    have hc : Real.cos (v * b) = 1 - 2 * Real.sin (b * v / 2) ^ 2 := by
      rw [show v * b = 2 * (b * v / 2) by ring, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (b * v / 2)]
    rw [hc]
    field_simp
    ring

/-- `F_b(v) = 𝓕Λ_b(−v/2π)` (Mathlib's normalisation `𝓕f(w) = ∫ f(ξ) e^{−2πiξw} dξ`). -/
theorem fejerBandProfile_eq_fourier (hb : 0 < b) (v : ℝ) :
    ((fejerBandProfile b v : ℝ) : ℂ)
      = FourierTransform.fourier (fun u : ℝ => ((triangleFn b u : ℝ) : ℂ)) (-v / (2 * π)) := by
  rw [fourier_triangleFn hb, fejerBandProfile_eq_sinc hb]
  congr 2
  rw [show π * b * (-v / (2 * π)) = -(b * v / 2) by field_simp, Real.sinc_neg]

theorem integrable_fourier_triangleFn (hb : 0 < b) :
    Integrable (FourierTransform.fourier (fun u : ℝ => ((triangleFn b u : ℝ) : ℂ))) := by
  have h : (FourierTransform.fourier (fun u : ℝ => ((triangleFn b u : ℝ) : ℂ)))
      = fun w : ℝ => ((fejerBandProfile b (-(2 * π) * w) : ℝ) : ℂ) := by
    funext w
    rw [fejerBandProfile_eq_fourier hb]
    field_simp
  rw [h]
  exact ((integrable_fejerBandProfile hb).comp_mul_left' (neg_ne_zero.mpr (by positivity))).ofReal

/-- **Fourier inversion for the Fejér profile:** `∫ F_b(v) e^{−iyv} dv = 2π Λ_b(y)`. -/
theorem integral_fejerBandProfile_mul_cexp (hb : 0 < b) (y : ℝ) :
    ∫ v, ((fejerBandProfile b v : ℝ) : ℂ) * cexp (-(I * y * v)) = 2 * π * ((triangleFn b y : ℝ) : ℂ) := by
  set f : ℝ → ℂ := fun u => ((triangleFn b u : ℝ) : ℂ) with hf
  have hfc : Continuous f := by have := continuous_triangleFn b; fun_prop
  have hfi : Integrable f := by
    refine hfc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -b) (b := b)) ?_
    intro ξ hξ
    rw [Function.mem_support] at hξ
    by_contra h
    apply hξ
    simp only [hf]
    rw [triangleFn_eq_zero hb]
    · simp
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hinv := congrFun (hfc.fourierInv_fourier_eq hfi (integrable_fourier_triangleFn hb)) y
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq] at hinv
  set g : ℝ → ℂ := fun w => FourierTransform.fourier f w * cexp (((2 * π * (w * y)) : ℝ) * I) with hg
  have hinv' : ∫ w, g w = f y := by
    rw [← hinv]
    congr 1 with w
    simp only [hg, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    rw [mul_comm, show -(w * -y) = w * y by ring]
  have hcov := Measure.integral_comp_mul_left g (-(1 / (2 * π)))
  have hpt : ∀ v : ℝ, g (-(1 / (2 * π)) * v)
      = ((fejerBandProfile b v : ℝ) : ℂ) * cexp (-(I * y * v)) := by
    intro v
    simp only [hg, hf]
    rw [fejerBandProfile_eq_fourier hb]
    congr 2
    · ring_nf
    · push_cast; field_simp
  simp_rw [hpt] at hcov
  rw [hcov, hinv', show |(-(1 / (2 * π)))⁻¹| = 2 * π by
    rw [inv_neg, abs_neg, one_div, inv_inv, abs_of_pos (by positivity)], Complex.real_smul]
  simp only [hf]
  push_cast
  ring

/-- The total mass of the profile is `2π`. -/
theorem fejerMass_eq (hb : 0 < b) : fejerMass b = 2 * π := by
  have h := integral_fejerBandProfile_mul_cexp hb 0
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at h
  rw [show triangleFn b 0 = 1 by simp [triangleFn]] at h
  rw [integral_complex_ofReal] at h
  have h' : ((∫ v, fejerBandProfile b v : ℝ) : ℂ) = ((2 * π : ℝ) : ℂ) := by
    rw [h]; push_cast; ring
  exact_mod_cast h'

/-- **The transform of the window:**
`∫ W(τ) e^{−iyτ} dτ = κ_b⁻¹ · 2π Λ_b(y) · ∫_{s₀}^{s₁} e^{−iyu} du`. -/
theorem integral_fejerWindow_mul_cexp (hb : 0 < b) (h01 : s₀ ≤ s₁) (y : ℝ) :
    ∫ τ, ((fejerWindow b s₀ s₁ τ : ℝ) : ℂ) * cexp (-(I * y * τ))
      = (((fejerMass b)⁻¹ : ℝ) : ℂ) * (2 * π * ((triangleFn b y : ℝ) : ℂ))
        * ∫ u in s₀..s₁, cexp (-(I * y * u)) := by
  set ν : Measure ℝ := volume.restrict (Ioc s₀ s₁) with hν
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  set h : ℝ → ℝ → ℂ := fun τ u => ((fejerBandProfile b (τ - u) : ℝ) : ℂ) * cexp (-(I * y * τ)) with hh
  have hFc := continuous_fejerBandProfile hb
  have hFi := integrable_fejerBandProfile hb
  have hpt : ∀ τ : ℝ, ((fejerWindow b s₀ s₁ τ : ℝ) : ℂ) * cexp (-(I * y * τ))
      = (((fejerMass b)⁻¹ : ℝ) : ℂ) * ∫ u, h τ u ∂ν := by
    intro τ
    unfold fejerWindow
    rw [← intervalIntegral.integral_comp_sub_left (fun v => fejerBandProfile b v) τ,
      intervalIntegral.integral_of_le h01, Complex.ofReal_mul, mul_assoc]
    congr 1
    rw [← integral_complex_ofReal, ← integral_mul_const]
  simp_rw [hpt]
  rw [integral_const_mul]
  have hnorm : ∀ τ u, ‖h τ u‖ = fejerBandProfile b (τ - u) := by
    intro τ u
    rw [hh]
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fejerBandProfile_nonneg hb _),
      show -(I * (y : ℂ) * (τ : ℂ)) = ((-(y * τ)) : ℝ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hint : Integrable (Function.uncurry h) (volume.prod ν) := by
    have hc : Continuous (Function.uncurry h) := by
      simp only [hh]
      fun_prop
    refine (integrable_prod_iff' hc.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · refine Filter.Eventually.of_forall fun u => ?_
      refine Integrable.mono' (hFi.comp_sub_right u) (by fun_prop : Continuous fun τ => h τ u).aestronglyMeasurable
        (Filter.Eventually.of_forall fun τ => le_of_eq (hnorm τ u))
    · have : (fun u => ∫ τ, ‖Function.uncurry h (τ, u)‖) = fun _ => fejerMass b := by
        funext u
        simp only [Function.uncurry_apply_pair, hnorm]
        exact integral_sub_right_eq_self (fejerBandProfile b) u
      rw [this]
      exact integrable_const _
  rw [integral_integral_swap hint]
  have hinner : ∀ u, ∫ τ, h τ u = cexp (-(I * y * u)) * (2 * π * ((triangleFn b y : ℝ) : ℂ)) := by
    intro u
    set f : ℝ → ℂ := fun v => ((fejerBandProfile b v : ℝ) : ℂ) * cexp (-(I * y * v)) * cexp (-(I * y * u))
      with hf
    have hfh : ∀ τ, h τ u = f (τ - u) := by
      intro τ
      simp only [hh, hf, mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    simp_rw [hfh]
    rw [integral_sub_right_eq_self f u, hf, integral_mul_const, integral_fejerBandProfile_mul_cexp hb y]
    ring
  simp_rw [hinner]
  rw [integral_mul_const, intervalIntegral.integral_of_le h01]
  ring

/-- Beyond the band the window has no Fourier mass: `∫ W(τ) e^{−iyτ} dτ = 0` for `|y| ≥ b`. -/
theorem integral_fejerWindow_mul_cexp_eq_zero (hb : 0 < b) (h01 : s₀ ≤ s₁) {y : ℝ} (hy : b ≤ |y|) :
    ∫ τ, ((fejerWindow b s₀ s₁ τ : ℝ) : ℂ) * cexp (-(I * y * τ)) = 0 := by
  rw [integral_fejerWindow_mul_cexp hb h01, triangleFn_eq_zero hb hy]
  simp

end FejerWeight

end RHTower

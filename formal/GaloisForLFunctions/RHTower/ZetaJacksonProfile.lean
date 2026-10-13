import GaloisForLFunctions.RHTower.ZetaFejerGridSum

/-!
# The Jackson profile `F_b²`

The Fejér profile `F_b(v) = (2 − 2cos(bv))/(bv²)` has tails `∫_{v>D} F_b ≍ 1/(bD)`, too heavy for windows on a
grid whose prime frequencies reach `T^{4/3}`.  Its square `F_b²` decays like `16/(b²v⁴)` and is still band-limited:

`∫ F_b(v)² e^{−iyv} dv = 2π ∫ Λ_b(ξ) Λ_b(y − ξ) dξ`   (`integral_jacksonProfile_mul_cexp`),

which vanishes for `|y| ≥ 2b` (`integral_jacksonProfile_mul_cexp_eq_zero`).  The proof writes
`F_b(v) e^{−iyv} = ∫ Λ_b(ξ) e^{−i(y−ξ)v} dξ`, exchanges the integrals and applies the Fejér inversion
`∫ F_b(v) e^{−i(y−ξ)v} dv = 2π Λ_b(y − ξ)`.
-/

open Complex MeasureTheory Real Set Filter
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

namespace FejerWeight

variable {b : ℝ}

/-- The Jackson profile `F_b(v)²`. -/
def jacksonProfile (b v : ℝ) : ℝ := fejerBandProfile b v ^ 2

theorem jacksonProfile_nonneg (b v : ℝ) : 0 ≤ jacksonProfile b v := sq_nonneg _

theorem jacksonProfile_le (hb : 0 < b) (v : ℝ) : jacksonProfile b v ≤ b ^ 2 := by
  unfold jacksonProfile
  exact pow_le_pow_left₀ (fejerBandProfile_nonneg hb v) (fejerBandProfile_le hb v) 2

theorem jacksonProfile_le_inv (hb : 0 < b) {v : ℝ} (hv : v ≠ 0) :
    jacksonProfile b v ≤ 16 / (v ^ 4 * b ^ 2) := by
  unfold jacksonProfile
  have h := pow_le_pow_left₀ (fejerBandProfile_nonneg hb v) (fejerBandProfile_le_inv hb hv) 2
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

theorem continuous_jacksonProfile (hb : 0 < b) : Continuous (jacksonProfile b) := by
  unfold jacksonProfile
  exact (continuous_fejerBandProfile hb).pow 2

theorem integrable_jacksonProfile (hb : 0 < b) : Integrable (jacksonProfile b) := by
  refine Integrable.mono' ((integrable_fejerBandProfile hb).const_mul b)
    (continuous_jacksonProfile hb).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (jacksonProfile_nonneg b v)]
  unfold jacksonProfile
  rw [sq]
  exact mul_le_mul_of_nonneg_right (fejerBandProfile_le hb v) (fejerBandProfile_nonneg hb v)

theorem integrable_triangleFn_real (hb : 0 < b) : Integrable (triangleFn b) := by
  refine (continuous_triangleFn b).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -b) (b := b)) ?_
  intro ξ hξ
  rw [Function.mem_support] at hξ
  by_contra h
  apply hξ
  apply triangleFn_eq_zero hb
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- `F_b(v) = ∫ Λ_b(ξ) e^{iξv} dξ` over the whole line. -/
theorem fejerBandProfile_eq_integral (hb : 0 < b) (v : ℝ) :
    ((fejerBandProfile b v : ℝ) : ℂ) = ∫ ξ, ((triangleFn b ξ : ℝ) : ℂ) * cexp (I * ξ * v) := by
  rw [← integral_triangle_cexp_eq_profile hb v, intervalIntegral.integral_of_le (by linarith)]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun ξ hξ => ?_)
  rw [triangleFn_eq_zero hb]
  · simp
  rw [mem_Ioc, not_and_or, not_lt, not_le] at hξ
  rcases hξ with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- **The Jackson profile is band-limited:** `∫ F_b(v)² e^{−iyv} dv = 2π ∫ Λ_b(ξ) Λ_b(y − ξ) dξ`. -/
theorem integral_jacksonProfile_mul_cexp (hb : 0 < b) (y : ℝ) :
    ∫ v, ((jacksonProfile b v : ℝ) : ℂ) * cexp (-(I * y * v))
      = 2 * π * ∫ ξ, ((triangleFn b ξ : ℝ) : ℂ) * ((triangleFn b (y - ξ) : ℝ) : ℂ) := by
  set f : ℝ → ℝ → ℂ := fun v ξ => ((fejerBandProfile b v : ℝ) : ℂ) * ((triangleFn b ξ : ℝ) : ℂ)
      * cexp (-(I * ((y - ξ : ℝ) : ℂ) * v)) with hf
  have hpt : ∀ v, ((jacksonProfile b v : ℝ) : ℂ) * cexp (-(I * y * v)) = ∫ ξ, f v ξ := by
    intro v
    unfold jacksonProfile
    rw [Complex.ofReal_pow, sq]
    conv_lhs => rw [mul_assoc]; arg 2; arg 1; rw [fejerBandProfile_eq_integral hb v]
    rw [← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hf]
    rw [show cexp (-(I * ((y - ξ : ℝ) : ℂ) * v)) = cexp (I * ξ * v) * cexp (-(I * y * v)) by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  simp_rw [hpt]
  have hint : Integrable (Function.uncurry f) (volume.prod volume) := by
    have hc : Continuous (Function.uncurry f) := by
      have h1 := continuous_fejerBandProfile hb
      have h2 := continuous_triangleFn b
      simp only [hf]
      fun_prop
    have hmaj : Integrable (fun q : ℝ × ℝ => fejerBandProfile b q.1 * triangleFn b q.2) (volume.prod volume) :=
      (integrable_fejerBandProfile hb).mul_prod (integrable_triangleFn_real hb)
    refine hmaj.mono' hc.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    show ‖((fejerBandProfile b q.1 : ℝ) : ℂ) * ((triangleFn b q.2 : ℝ) : ℂ)
        * cexp (-(I * ((y - q.2 : ℝ) : ℂ) * q.1))‖ ≤ fejerBandProfile b q.1 * triangleFn b q.2
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (fejerBandProfile_nonneg hb _), abs_of_nonneg (triangleFn_nonneg b _),
      show -(I * ((y - q.2 : ℝ) : ℂ) * (q.1 : ℂ)) = ((-((y - q.2) * q.1)) : ℝ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [integral_integral_swap hint, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [hf]
  have h := integral_fejerBandProfile_mul_cexp hb (y - ξ)
  calc ∫ v, ((fejerBandProfile b v : ℝ) : ℂ) * ((triangleFn b ξ : ℝ) : ℂ)
        * cexp (-(I * ((y - ξ : ℝ) : ℂ) * v))
      = ((triangleFn b ξ : ℝ) : ℂ) * ∫ v, ((fejerBandProfile b v : ℝ) : ℂ)
        * cexp (-(I * ((y - ξ : ℝ) : ℂ) * v)) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        ring
    _ = 2 * π * (((triangleFn b ξ : ℝ) : ℂ) * ((triangleFn b (y - ξ) : ℝ) : ℂ)) := by
        rw [h]; ring

/-- Beyond twice the band the Jackson profile has no Fourier mass. -/
theorem integral_jacksonProfile_mul_cexp_eq_zero (hb : 0 < b) {y : ℝ} (hy : 2 * b ≤ |y|) :
    ∫ v, ((jacksonProfile b v : ℝ) : ℂ) * cexp (-(I * y * v)) = 0 := by
  rw [integral_jacksonProfile_mul_cexp hb]
  have h0 : ∀ ξ : ℝ, ((triangleFn b ξ : ℝ) : ℂ) * ((triangleFn b (y - ξ) : ℝ) : ℂ) = 0 := by
    intro ξ
    by_cases hξ : b ≤ |ξ|
    · rw [triangleFn_eq_zero hb hξ]; simp
    · push Not at hξ
      have : b ≤ |y - ξ| := by
        have := abs_sub_abs_le_abs_sub y ξ
        linarith
      rw [triangleFn_eq_zero hb this]; simp
  simp_rw [h0, integral_zero, mul_zero]

theorem jacksonProfile_neg (b v : ℝ) : jacksonProfile b (-v) = jacksonProfile b v := by
  unfold jacksonProfile; rw [fejerBandProfile_neg]

/-- `∫_{v > D} F_b² ≤ 16/(3b²D³)`. -/
theorem setIntegral_Ioi_jacksonProfile_le (hb : 0 < b) {D : ℝ} (hD : 0 < D) :
    ∫ v in Ioi D, jacksonProfile b v ≤ 16 / (3 * b ^ 2 * D ^ 3) := by
  have hcmp : ∀ v ∈ Ioi D, jacksonProfile b v ≤ (16 / b ^ 2) * v ^ (-4 : ℝ) := by
    intro v hv
    have hv0 : 0 < v := lt_trans hD hv
    rw [Real.rpow_neg hv0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc jacksonProfile b v ≤ 16 / (v ^ 4 * b ^ 2) := jacksonProfile_le_inv hb hv0.ne'
      _ = (16 / b ^ 2) * (v ^ 4)⁻¹ := by field_simp
  have hint2 : IntegrableOn (fun v : ℝ => (16 / b ^ 2) * v ^ (-4 : ℝ)) (Ioi D) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hD).const_mul _
  calc ∫ v in Ioi D, jacksonProfile b v ≤ ∫ v in Ioi D, (16 / b ^ 2) * v ^ (-4 : ℝ) :=
        setIntegral_mono_on (integrable_jacksonProfile hb).integrableOn hint2 measurableSet_Ioi hcmp
    _ = 16 / (3 * b ^ 2 * D ^ 3) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hD]
        rw [show (-4 : ℝ) + 1 = -3 by norm_num, Real.rpow_neg hD.le,
          show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp

theorem setIntegral_Iic_jacksonProfile_le (hb : 0 < b) {D : ℝ} (hD : 0 < D) :
    ∫ v in Iic (-D), jacksonProfile b v ≤ 16 / (3 * b ^ 2 * D ^ 3) := by
  have h := integral_comp_neg_Iic (-D) (jacksonProfile b)
  simp only [jacksonProfile_neg, neg_neg] at h
  rw [h]
  exact setIntegral_Ioi_jacksonProfile_le hb hD

/-- The total mass `κ₂ = ∫ F_b²`. -/
def jacksonMass (b : ℝ) : ℝ := ∫ v, jacksonProfile b v

theorem jacksonMass_pos (hb : 0 < b) : 0 < jacksonMass b := by
  unfold jacksonMass
  have hI := integrable_jacksonProfile hb
  have hlow : ∀ v ∈ Icc (-(1 / b)) (1 / b), ((43 / 48) * b) ^ 2 ≤ jacksonProfile b v := by
    intro v hv
    unfold jacksonProfile
    exact pow_le_pow_left₀ (by positivity) (fejerBandProfile_ge hb (abs_le.mpr ⟨hv.1, hv.2⟩)) 2
  have h1 : ∫ v in Icc (-(1 / b)) (1 / b), jacksonProfile b v ≤ ∫ v, jacksonProfile b v :=
    setIntegral_le_integral hI (Eventually.of_forall fun v => jacksonProfile_nonneg b v)
  have h2 : ∫ v in Icc (-(1 / b)) (1 / b), ((43 / 48) * b) ^ 2
      ≤ ∫ v in Icc (-(1 / b)) (1 / b), jacksonProfile b v :=
    setIntegral_mono_on continuous_const.integrableOn_Icc hI.integrableOn measurableSet_Icc hlow
  have h3 : ∫ v in Icc (-(1 / b)) (1 / b), ((43 / 48) * b) ^ 2 = ((43 / 48) * b) ^ 2 * (2 / b) := by
    have hb1 : 0 < 1 / b := by positivity
    rw [setIntegral_const, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
      smul_eq_mul]
    field_simp
    ring
  have h4 : 0 < ((43 / 48) * b) ^ 2 * (2 / b) := by positivity
  linarith

/-- The Jackson window of `[s₀, s₁]`: `W(s) = κ₂⁻¹ ∫_{s−s₁}^{s−s₀} F_b²`. -/
def jacksonWindow (b s₀ s₁ s : ℝ) : ℝ := (jacksonMass b)⁻¹ * ∫ v in (s - s₁)..(s - s₀), jacksonProfile b v

variable {s₀ s₁ : ℝ}

theorem jacksonWindow_nonneg (hb : 0 < b) (h01 : s₀ ≤ s₁) (s : ℝ) : 0 ≤ jacksonWindow b s₀ s₁ s := by
  unfold jacksonWindow
  exact mul_nonneg (inv_nonneg.mpr (jacksonMass_pos hb).le)
    (intervalIntegral.integral_nonneg (by linarith) fun v _ => jacksonProfile_nonneg b v)

theorem jacksonWindow_le_one (hb : 0 < b) (h01 : s₀ ≤ s₁) (s : ℝ) : jacksonWindow b s₀ s₁ s ≤ 1 := by
  unfold jacksonWindow
  have hk := jacksonMass_pos hb
  rw [inv_mul_le_iff₀ hk, mul_one, intervalIntegral.integral_of_le (by linarith)]
  exact setIntegral_le_integral (integrable_jacksonProfile hb)
    (Eventually.of_forall fun v => jacksonProfile_nonneg b v)

/-- Inside the interval the Jackson window is within `O(1/(b d)³)` of one. -/
theorem one_sub_le_jacksonWindow (hb : 0 < b) {s : ℝ} (h0 : s₀ < s) (h1 : s < s₁) :
    1 - (jacksonMass b)⁻¹ * (16 / (3 * b ^ 2 * (s₁ - s) ^ 3) + 16 / (3 * b ^ 2 * (s - s₀) ^ 3))
      ≤ jacksonWindow b s₀ s₁ s := by
  have hk := jacksonMass_pos hb
  have hI := integrable_jacksonProfile hb
  have hsplit1 : (∫ v in Iic (s - s₁), jacksonProfile b v) + (∫ v in Ioi (s - s₁), jacksonProfile b v)
      = jacksonMass b := intervalIntegral.integral_Iic_add_Ioi hI.integrableOn hI.integrableOn
  have hsplit2 : (∫ v in (s - s₁)..(s - s₀), jacksonProfile b v) + (∫ v in Ioi (s - s₀), jacksonProfile b v)
      = ∫ v in Ioi (s - s₁), jacksonProfile b v :=
    intervalIntegral.integral_interval_add_Ioi hI.integrableOn hI.integrableOn
  have hL := setIntegral_Iic_jacksonProfile_le hb (D := s₁ - s) (by linarith)
  rw [neg_sub] at hL
  have hR := setIntegral_Ioi_jacksonProfile_le hb (D := s - s₀) (by linarith)
  have e : (∫ v in (s - s₁)..(s - s₀), jacksonProfile b v)
      = jacksonMass b - (∫ v in Iic (s - s₁), jacksonProfile b v)
        - (∫ v in Ioi (s - s₀), jacksonProfile b v) := by
    linear_combination hsplit2 + hsplit1
  unfold jacksonWindow
  rw [e]
  have e2 : (jacksonMass b)⁻¹ * (jacksonMass b - (∫ v in Iic (s - s₁), jacksonProfile b v)
        - (∫ v in Ioi (s - s₀), jacksonProfile b v))
      = 1 - (jacksonMass b)⁻¹ * (∫ v in Iic (s - s₁), jacksonProfile b v)
        - (jacksonMass b)⁻¹ * (∫ v in Ioi (s - s₀), jacksonProfile b v) := by
    field_simp
  rw [e2]
  have h2 := mul_le_mul_of_nonneg_left hL (inv_nonneg.mpr hk.le)
  have h3 := mul_le_mul_of_nonneg_left hR (inv_nonneg.mpr hk.le)
  linarith [mul_add (jacksonMass b)⁻¹ (16 / (3 * b ^ 2 * (s₁ - s) ^ 3))
    (16 / (3 * b ^ 2 * (s - s₀) ^ 3))]

/-- To the right of the interval, at distance `D`, the Jackson window is at most `16/(3κ₂ b² D³)`. -/
theorem jacksonWindow_le_right (hb : 0 < b) {s D : ℝ} (hD : 0 < D) (hs : s₁ + D ≤ s) :
    jacksonWindow b s₀ s₁ s ≤ (jacksonMass b)⁻¹ * (16 / (3 * b ^ 2 * D ^ 3)) := by
  have hk := jacksonMass_pos hb
  have hI := integrable_jacksonProfile hb
  have hsplit : (∫ v in (s - s₁)..(s - s₀), jacksonProfile b v) + (∫ v in Ioi (s - s₀), jacksonProfile b v)
      = ∫ v in Ioi (s - s₁), jacksonProfile b v :=
    intervalIntegral.integral_interval_add_Ioi hI.integrableOn hI.integrableOn
  have hpos : 0 ≤ ∫ v in Ioi (s - s₀), jacksonProfile b v :=
    setIntegral_nonneg measurableSet_Ioi fun v _ => jacksonProfile_nonneg b v
  have hmono : ∫ v in Ioi (s - s₁), jacksonProfile b v ≤ ∫ v in Ioi D, jacksonProfile b v :=
    setIntegral_mono_set hI.integrableOn
      (Eventually.of_forall fun v => jacksonProfile_nonneg b v)
      (Eventually.of_forall fun v hv => lt_of_le_of_lt (by linarith) hv)
  have hR := setIntegral_Ioi_jacksonProfile_le hb hD
  unfold jacksonWindow
  exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hk.le)

/-- To the left of the interval, at distance `D`, the Jackson window is at most `16/(3κ₂ b² D³)`. -/
theorem jacksonWindow_le_left (hb : 0 < b) {s D : ℝ} (hD : 0 < D) (hs : s + D ≤ s₀) :
    jacksonWindow b s₀ s₁ s ≤ (jacksonMass b)⁻¹ * (16 / (3 * b ^ 2 * D ^ 3)) := by
  have hrefl : jacksonWindow b s₀ s₁ s = jacksonWindow b (-s₁) (-s₀) (-s) := by
    unfold jacksonWindow
    congr 1
    have h := intervalIntegral.integral_comp_neg (a := s - s₁) (b := s - s₀) (jacksonProfile b)
    simp only [jacksonProfile_neg] at h
    rw [h]
    congr 1 <;> ring
  rw [hrefl]
  exact jacksonWindow_le_right hb hD (by linarith)

theorem continuous_jacksonWindow (hb : 0 < b) : Continuous (jacksonWindow b s₀ s₁) := by
  unfold jacksonWindow
  refine continuous_const.mul ?_
  have hF := continuous_jacksonProfile hb
  have : (fun s => ∫ v in (s - s₁)..(s - s₀), jacksonProfile b v)
      = fun s => (∫ v in (0 : ℝ)..(s - s₀), jacksonProfile b v)
        - ∫ v in (0 : ℝ)..(s - s₁), jacksonProfile b v := by
    funext s
    rw [intervalIntegral.integral_interval_sub_left (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)]
  rw [this]
  have hP : Continuous fun u : ℝ => ∫ v in (0 : ℝ)..u, jacksonProfile b v :=
    continuous_iff_continuousAt.mpr fun u => (hF.integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt
  exact (hP.comp (continuous_id.sub continuous_const)).sub (hP.comp (continuous_id.sub continuous_const))

end FejerWeight

end RHTower

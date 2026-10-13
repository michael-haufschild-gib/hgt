import GaloisForLFunctions.RHTower.ZetaJacksonGridSum

/-!
# The Jackson window as an inverse Fourier transform

With `C_b(ζ) = ∫ Λ_b(ξ) Λ_b(ζ − ξ) dξ` (`triConv`, continuous, nonnegative, supported in `[−2b, 2b]`, total mass
`b²`) the Jackson profile is `F_b(v)² = ∫ C_b(ζ) e^{iζv} dζ` (`jacksonProfile_eq_integral`), and the Jackson window is
the inverse transform of

`ψ₂(ζ) = κ₂⁻¹ C_b(ζ) ∫_{s₀}^{s₁} e^{−iζu} du`   (`jacksonPsi`, `integral_jacksonPsi_mul_cexp`),

which is continuous, supported in `[−2b, 2b]`, and has first absolute moment `∫ |ζ| ‖ψ₂(ζ)‖ dζ ≤ 2b²/κ₂`
(`integral_abs_mul_norm_jacksonPsi_le`).  These are the hypotheses of the weighted Poisson identity
(`TwistedPoisson.hasSum_weighted_phiHat`, `norm_weighted_sub_main_le`) whenever `2b ≤ L`.
-/

open Complex MeasureTheory Real Set Filter
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

namespace FejerWeight

variable {b : ℝ}

/-- `C_b(ζ) = ∫ Λ_b(ξ) Λ_b(ζ − ξ) dξ`. -/
def triConv (b ζ : ℝ) : ℝ := ∫ ξ, triangleFn b ξ * triangleFn b (ζ - ξ)

theorem triConv_nonneg (b ζ : ℝ) : 0 ≤ triConv b ζ :=
  integral_nonneg fun ξ => mul_nonneg (triangleFn_nonneg b ξ) (triangleFn_nonneg b _)

theorem triangleFn_mul_eq_zero (hb : 0 < b) {ζ : ℝ} (hζ : 2 * b ≤ |ζ|) (ξ : ℝ) :
    triangleFn b ξ * triangleFn b (ζ - ξ) = 0 := by
  by_cases hξ : b ≤ |ξ|
  · rw [triangleFn_eq_zero hb hξ, zero_mul]
  · push Not at hξ
    have : b ≤ |ζ - ξ| := by have := abs_sub_abs_le_abs_sub ζ ξ; linarith
    rw [triangleFn_eq_zero hb this, mul_zero]

theorem triConv_eq_zero (hb : 0 < b) {ζ : ℝ} (hζ : 2 * b ≤ |ζ|) : triConv b ζ = 0 := by
  unfold triConv
  simp_rw [triangleFn_mul_eq_zero hb hζ, integral_zero]

theorem triConv_eq_setIntegral (hb : 0 < b) (ζ : ℝ) :
    triConv b ζ = ∫ ξ in Icc (-b) b, triangleFn b ξ * triangleFn b (ζ - ξ) := by
  unfold triConv
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun ξ hξ => ?_).symm
  rw [triangleFn_eq_zero hb, zero_mul]
  rw [mem_Icc, not_and_or, not_le, not_le] at hξ
  rcases hξ with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem continuous_triConv (hb : 0 < b) : Continuous (triConv b) := by
  have h : triConv b = fun ζ => ∫ ξ in Icc (-b) b, triangleFn b ξ * triangleFn b (ζ - ξ) := by
    funext ζ; exact triConv_eq_setIntegral hb ζ
  rw [h]
  have := continuous_triangleFn b
  exact continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc

theorem hasCompactSupport_triConv (hb : 0 < b) : HasCompactSupport (triConv b) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(2 * b)) (b := 2 * b)) ?_
  intro ζ hζ
  rw [Function.mem_support] at hζ
  by_contra h
  apply hζ
  apply triConv_eq_zero hb
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem integrable_triConv (hb : 0 < b) : Integrable (triConv b) :=
  (continuous_triConv hb).integrable_of_hasCompactSupport (hasCompactSupport_triConv hb)

/-- `F_b(v)² = ∫ C_b(ζ) e^{iζv} dζ`. -/
theorem jacksonProfile_eq_integral (hb : 0 < b) (v : ℝ) :
    ((jacksonProfile b v : ℝ) : ℂ) = ∫ ζ, ((triConv b ζ : ℝ) : ℂ) * cexp (I * ζ * v) := by
  have hΛ := integrable_triangleFn_real hb
  have hΛc := continuous_triangleFn b
  set f : ℝ → ℝ → ℂ := fun ξ ζ => ((triangleFn b ξ : ℝ) : ℂ) * ((triangleFn b (ζ - ξ) : ℝ) : ℂ)
      * cexp (I * ζ * v) with hf
  -- product of the two one-dimensional integrals
  have hprod : ((jacksonProfile b v : ℝ) : ℂ) = ∫ ξ, ∫ ζ, f ξ ζ := by
    unfold jacksonProfile
    rw [Complex.ofReal_pow, sq, fejerBandProfile_eq_integral hb v, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [← integral_const_mul, ← integral_add_left_eq_self (fun ζ => f ξ ζ) ξ]
    refine integral_congr_ae (Eventually.of_forall fun η => ?_)
    simp only [hf, add_sub_cancel_left]
    rw [show cexp (I * ((ξ + η : ℝ) : ℂ) * v) = cexp (I * ξ * v) * cexp (I * η * v) by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  have hnorm : ∀ ξ ζ, ‖f ξ ζ‖ = triangleFn b ξ * triangleFn b (ζ - ξ) := by
    intro ξ ζ
    simp only [hf]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (triangleFn_nonneg b _), abs_of_nonneg (triangleFn_nonneg b _),
      show I * (ζ : ℂ) * (v : ℂ) = ((ζ * v : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hint : Integrable (Function.uncurry f) (volume.prod volume) := by
    have hc : Continuous (Function.uncurry f) := by simp only [hf]; fun_prop
    refine (integrable_prod_iff hc.aestronglyMeasurable).mpr ⟨Eventually.of_forall fun ξ => ?_, ?_⟩
    · refine Integrable.mono' ((hΛ.comp_sub_right ξ).const_mul (triangleFn b ξ))
        (by fun_prop : Continuous fun ζ => f ξ ζ).aestronglyMeasurable
        (Eventually.of_forall fun ζ => le_of_eq (hnorm ξ ζ))
    · have e : (fun ξ => ∫ ζ, ‖Function.uncurry f (ξ, ζ)‖) = fun ξ => (∫ η, triangleFn b η) * triangleFn b ξ := by
        funext ξ
        simp only [Function.uncurry_apply_pair, hnorm]
        rw [integral_const_mul, integral_sub_right_eq_self (triangleFn b) ξ, mul_comm]
      rw [e]
      exact hΛ.const_mul _
  rw [hprod, integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  simp only [hf]
  rw [integral_mul_const, triConv, ← integral_complex_ofReal]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  push_cast; ring

theorem triConv_le (hb : 0 < b) (ζ : ℝ) : triConv b ζ ≤ b := by
  unfold triConv
  calc ∫ ξ, triangleFn b ξ * triangleFn b (ζ - ξ) ≤ ∫ ξ, triangleFn b ξ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ξ =>
            mul_nonneg (triangleFn_nonneg b ξ) (triangleFn_nonneg b _))
          (integrable_triangleFn_real hb)
          (Eventually.of_forall fun ξ => by
            have h1 := triangleFn_le_one hb (ζ - ξ)
            have h0 := triangleFn_nonneg b ξ
            nlinarith)
    _ = b := integral_triangleFn_real hb

/-- `∫ C_b = b²`. -/
theorem integral_triConv (hb : 0 < b) : ∫ ζ, triConv b ζ = b ^ 2 := by
  have hΛ := integrable_triangleFn_real hb
  have hc : Continuous (Function.uncurry fun ξ ζ => triangleFn b ξ * triangleFn b (ζ - ξ)) := by
    have := continuous_triangleFn b; fun_prop
  have hint : Integrable (Function.uncurry fun ξ ζ => triangleFn b ξ * triangleFn b (ζ - ξ))
      (volume.prod volume) := by
    refine (integrable_prod_iff hc.aestronglyMeasurable).mpr ⟨Eventually.of_forall fun ξ => ?_, ?_⟩
    · exact (hΛ.comp_sub_right ξ).const_mul (triangleFn b ξ)
    · have e : (fun ξ => ∫ ζ, ‖(Function.uncurry fun ξ ζ => triangleFn b ξ * triangleFn b (ζ - ξ)) (ξ, ζ)‖)
          = fun ξ => b * triangleFn b ξ := by
        funext ξ
        simp only [Function.uncurry_apply_pair, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (triangleFn_nonneg b _) (triangleFn_nonneg b _))]
        rw [integral_const_mul, integral_sub_right_eq_self (triangleFn b) ξ, integral_triangleFn_real hb,
          mul_comm]
      rw [e]
      exact hΛ.const_mul _
  unfold triConv
  rw [← integral_integral_swap hint]
  simp_rw [integral_const_mul, integral_sub_right_eq_self (triangleFn b), integral_triangleFn_real hb]
  rw [integral_mul_const, integral_triangleFn_real hb]
  ring

variable {s₀ s₁ : ℝ}

/-- `ψ₂(ζ) = κ₂⁻¹ C_b(ζ) ∫_{s₀}^{s₁} e^{−iζu} du`. -/
def jacksonPsi (b s₀ s₁ ζ : ℝ) : ℂ :=
  (((jacksonMass b)⁻¹ : ℝ) : ℂ) * ((triConv b ζ : ℝ) : ℂ) * ∫ u in s₀..s₁, cexp (-(I * ζ * u))

theorem jacksonPsi_eq_zero (hb : 0 < b) {ζ : ℝ} (hζ : 2 * b ≤ |ζ|) : jacksonPsi b s₀ s₁ ζ = 0 := by
  unfold jacksonPsi; rw [triConv_eq_zero hb hζ]; simp

theorem continuous_jacksonPsi (hb : 0 < b) : Continuous (jacksonPsi b s₀ s₁) := by
  unfold jacksonPsi
  have h1 := continuous_triConv hb
  have h2 : Continuous fun ζ : ℝ => ∫ u in s₀..s₁, cexp (-(I * ζ * u)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (f := fun (ζ : ℝ) (u : ℝ) => cexp (-(I * ζ * u))) (a₀ := s₀) (by fun_prop)
      (continuous_const (y := s₁))
  fun_prop

theorem hasCompactSupport_jacksonPsi (hb : 0 < b) : HasCompactSupport (jacksonPsi b s₀ s₁) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(2 * b)) (b := 2 * b)) ?_
  intro ζ hζ
  rw [Function.mem_support] at hζ
  by_contra h
  apply hζ
  apply jacksonPsi_eq_zero hb
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem integrable_jacksonPsi (hb : 0 < b) : Integrable (jacksonPsi b s₀ s₁) :=
  (continuous_jacksonPsi hb).integrable_of_hasCompactSupport (hasCompactSupport_jacksonPsi hb)

theorem integrable_abs_mul_norm_jacksonPsi (hb : 0 < b) :
    Integrable fun ζ => |ζ| * ‖jacksonPsi b s₀ s₁ ζ‖ := by
  have hc := continuous_jacksonPsi (s₀ := s₀) (s₁ := s₁) hb
  exact (continuous_abs.mul hc.norm).integrable_of_hasCompactSupport
    (hasCompactSupport_jacksonPsi hb).norm.mul_left

theorem abs_mul_norm_jacksonPsi_le (hb : 0 < b) (ζ : ℝ) :
    |ζ| * ‖jacksonPsi b s₀ s₁ ζ‖ ≤ 2 * (jacksonMass b)⁻¹ * triConv b ζ := by
  have hk := jacksonMass_pos hb
  by_cases hζ : ζ = 0
  · subst hζ; simp only [abs_zero, zero_mul]; have := triConv_nonneg b 0; positivity
  have hc : (-(I * (ζ : ℂ))) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, mul_eq_zero, I_ne_zero, Complex.ofReal_eq_zero, hζ, or_self,
      not_false_eq_true]
  have hint : ∫ u in s₀..s₁, cexp (-(I * ζ * u))
      = (cexp (-(I * ζ) * s₁) - cexp (-(I * ζ) * s₀)) / (-(I * ζ)) := by
    rw [← integral_exp_mul_complex hc]
    congr 1 with u; ring_nf
  have hnum : ‖cexp (-(I * ζ) * s₁) - cexp (-(I * ζ) * s₀)‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [show -(I * (ζ : ℂ)) * (s₁ : ℂ) = ((-(ζ * s₁)) : ℝ) * I by push_cast; ring,
      show -(I * (ζ : ℂ)) * (s₀ : ℂ) = ((-(ζ * s₀)) : ℝ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hden : ‖-(I * (ζ : ℂ))‖ = |ζ| := by
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hζp : 0 < |ζ| := abs_pos.mpr hζ
  unfold jacksonPsi
  rw [hint, norm_mul, norm_mul, norm_div, hden, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk), abs_of_nonneg (triConv_nonneg b ζ)]
  have ht := triConv_nonneg b ζ
  calc |ζ| * ((jacksonMass b)⁻¹ * triConv b ζ
        * (‖cexp (-(I * ζ) * s₁) - cexp (-(I * ζ) * s₀)‖ / |ζ|))
      = (jacksonMass b)⁻¹ * triConv b ζ * ‖cexp (-(I * ζ) * s₁) - cexp (-(I * ζ) * s₀)‖ := by
        field_simp
    _ ≤ (jacksonMass b)⁻¹ * triConv b ζ * 2 := mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = 2 * (jacksonMass b)⁻¹ * triConv b ζ := by ring

/-- **First absolute moment of `ψ₂`:** `∫ |ζ| ‖ψ₂(ζ)‖ dζ ≤ 2b²/κ₂`. -/
theorem integral_abs_mul_norm_jacksonPsi_le (hb : 0 < b) :
    ∫ ζ, |ζ| * ‖jacksonPsi b s₀ s₁ ζ‖ ≤ 2 * (jacksonMass b)⁻¹ * b ^ 2 := by
  calc ∫ ζ, |ζ| * ‖jacksonPsi b s₀ s₁ ζ‖ ≤ ∫ ζ, 2 * (jacksonMass b)⁻¹ * triConv b ζ :=
        integral_mono (integrable_abs_mul_norm_jacksonPsi hb) ((integrable_triConv hb).const_mul _)
          fun ζ => abs_mul_norm_jacksonPsi_le hb ζ
    _ = 2 * (jacksonMass b)⁻¹ * b ^ 2 := by rw [integral_const_mul, integral_triConv hb]

/-- **The Jackson window is the inverse transform of `ψ₂`:** `∫ ψ₂(ζ) e^{iζs} dζ = W₂(s)`. -/
theorem integral_jacksonPsi_mul_cexp (hb : 0 < b) (h01 : s₀ ≤ s₁) (s : ℝ) :
    ∫ ζ, jacksonPsi b s₀ s₁ ζ * cexp (I * ζ * s) = (jacksonWindow b s₀ s₁ s : ℂ) := by
  have hk := jacksonMass_pos hb
  have hb2 : 0 < 2 * b := by linarith
  have hsupp : ∀ ζ ∉ Ioc (-(2 * b)) (2 * b), jacksonPsi b s₀ s₁ ζ * cexp (I * ζ * s) = 0 := by
    intro ζ hζ
    rw [jacksonPsi_eq_zero hb, zero_mul]
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hζ
    rcases hζ with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    ← intervalIntegral.integral_of_le (by linarith)]
  set g : ℝ → ℝ → ℂ := fun ζ u => ((triConv b ζ : ℝ) : ℂ) * cexp (I * ζ * ((s - u : ℝ) : ℂ)) with hg
  have hpt : ∀ ζ : ℝ, jacksonPsi b s₀ s₁ ζ * cexp (I * ζ * s)
      = (((jacksonMass b)⁻¹ : ℝ) : ℂ) * ∫ u in Ioc s₀ s₁, g ζ u := by
    intro ζ
    unfold jacksonPsi
    rw [intervalIntegral.integral_of_le h01, mul_assoc, mul_assoc]
    congr 1
    rw [← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hg]
    rw [mul_assoc]
    congr 1
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  haveI : IsFiniteMeasure (volume.restrict (Ioc s₀ s₁)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (-(2 * b)) (2 * b))) :=
    isFiniteMeasure_restrict.mpr (by rw [Set.uIoc]; exact measure_Ioc_lt_top.ne)
  have hgc : Continuous (Function.uncurry g) := by
    have := continuous_triConv hb
    simp only [hg]
    fun_prop
  have hgint : Integrable (Function.uncurry g)
      ((volume.restrict (Set.uIoc (-(2 * b)) (2 * b))).prod (volume.restrict (Ioc s₀ s₁))) := by
    refine Integrable.of_bound hgc.aestronglyMeasurable b (Eventually.of_forall fun q => ?_)
    show ‖((triConv b q.1 : ℝ) : ℂ) * cexp (I * (q.1 : ℂ) * ((s - q.2 : ℝ) : ℂ))‖ ≤ b
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (triConv_nonneg b _),
      show I * ((q.1 : ℝ) : ℂ) * ((s - q.2 : ℝ) : ℂ) = ((q.1 * (s - q.2) : ℝ) : ℂ) * I by
        push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact triConv_le hb _
  rw [intervalIntegral_integral_swap hgint]
  have hinner : ∀ u : ℝ, ∫ ζ in (-(2 * b))..(2 * b), g ζ u = (jacksonProfile b (s - u) : ℂ) := by
    intro u
    rw [jacksonProfile_eq_integral hb (s - u), intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun ζ hζ => ?_
    simp only [hg]
    rw [triConv_eq_zero hb, Complex.ofReal_zero, zero_mul]
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hζ
    rcases hζ with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  simp_rw [hinner]
  rw [← intervalIntegral.integral_of_le h01, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_comp_sub_left (fun v => jacksonProfile b v) s]
  unfold jacksonWindow
  push_cast
  ring

end FejerWeight

end RHTower

import GaloisForLFunctions.RHTower.ZetaJacksonProfile

/-!
# Grid character sums of band-limited windows

For a continuous window `W` with quadratic decay whose transform `∫ W(s) e^{−iηs} ds` vanishes for `|η| ≥ B`,
Poisson summation on the grid `τ_k = T + k·2π/L` gives `Σ_{k∈ℤ} W(τ_k) e^{iyτ_k} = 0` whenever `|jL − y| ≥ B` for all
`j ∈ ℤ` (`hasSum_grid_char_eq_zero_of_window`).

The Jackson window `W(s) = κ₂⁻¹ ∫_{s₀}^{s₁} F_b(s − u)² du` qualifies with `B = 2b`
(`integral_jacksonWindow_mul_cexp_eq_zero`, `hasSum_jackson_grid_char_eq_zero`); unlike the Fejér window it decays like
`(b d)⁻³` at distance `d` from the interval.
-/

open Complex MeasureTheory Real Set Filter Asymptotics
open GaloisForLFunctions.HTGeometry
open scoped FourierTransform

noncomputable section

namespace RHTower

namespace FejerWeight

/-- **Poisson summation for a band-limited window on the Gabor grid.** -/
theorem hasSum_grid_char_eq_zero_of_window {W : ℝ → ℝ} {B L : ℝ} (hWc : Continuous W)
    {C R : ℝ} (hC : 0 ≤ C) (hWdec : ∀ s, R ≤ |s| → |W s| ≤ C / s ^ 2)
    (hWF : ∀ η : ℝ, B ≤ |η| → ∫ s, ((W s : ℝ) : ℂ) * cexp (-(I * η * s)) = 0)
    (hL : 0 < L) (T y : ℝ) (hy : ∀ j : ℤ, B ≤ |j * L - y|) :
    HasSum (fun k : ℤ => ((W (T + k * (2 * π / L)) : ℝ) : ℂ)
      * cexp (I * y * ((T + k * (2 * π / L) : ℝ) : ℂ))) 0 := by
  set h : ℝ := 2 * π / L with hh
  have hh0 : 0 < h := by positivity
  set g : ℝ → ℂ := fun x => ((W (T + x * h) : ℝ) : ℂ) * cexp (I * y * ((T + x * h : ℝ) : ℂ)) with hg
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hnorm : ∀ x, ‖g x‖ = |W (T + x * h)| := by
    intro x
    simp only [hg]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show I * (y : ℂ) * ((T + x * h : ℝ) : ℂ) = ((y * (T + x * h)) : ℝ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  -- decay of the samples
  have hgO : g =O[cocompact ℝ] fun x => |x| ^ (-2 : ℝ) := by
    refine IsBigO.of_bound (4 * C / h ^ 2) ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually
      (eventually_ge_atTop (2 * (|T| + |R| + 1) / h))] with x hx
    rw [Real.norm_eq_abs, div_le_iff₀ hh0] at hx
    have hT := abs_nonneg T
    have hRa := abs_nonneg R
    have hxh : |x * h| = |x| * h := by rw [abs_mul, abs_of_pos hh0]
    have h2 : |x * h| ≤ |T + x * h| + |T| := by
      have := abs_sub (T + x * h) T
      rwa [add_sub_cancel_left] at this
    have hs : |x| * h / 2 ≤ |T + x * h| := by linarith
    have hRs : R ≤ |T + x * h| := by linarith [le_abs_self R]
    have hpos : 0 < |x| * h / 2 := by linarith
    have hx0 : 0 < |x| := by
      by_contra h0; push Not at h0
      have : |x| = 0 := le_antisymm h0 (abs_nonneg x)
      rw [this] at hpos; linarith
    rw [hnorm, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) (-2)),
      Real.rpow_neg (abs_nonneg x), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hdec := hWdec (T + x * h) hRs
    refine hdec.trans ?_
    have hsq : (|x| * h / 2) ^ 2 ≤ (T + x * h) ^ 2 := by
      rw [← sq_abs (T + x * h)]; exact pow_le_pow_left₀ hpos.le hs 2
    calc C / (T + x * h) ^ 2 ≤ C / (|x| * h / 2) ^ 2 :=
          div_le_div_of_nonneg_left hC (by positivity) hsq
      _ = 4 * C / h ^ 2 * (|x| ^ 2)⁻¹ := by field_simp; ring
  -- the transform of the samples vanishes off the aliases
  have hF0 : ∀ w : ℝ, B ≤ |w * L - y| → 𝓕 g w = 0 := by
    intro w hw
    set G : ℝ → ℂ := fun s => cexp (I * ((w * L * T : ℝ) : ℂ))
        * (((W s : ℝ) : ℂ) * cexp (-(I * ((w * L - y : ℝ) : ℂ) * s))) with hG
    have hpt : ∀ x : ℝ, Real.fourierChar (-(x * w)) • g x = G (T + h * x) := by
      intro x
      simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, hg, hG]
      rw [show T + x * h = T + h * x by ring]
      have e1 : cexp (((2 * π * -(x * w) : ℝ) : ℂ) * I) * cexp (I * (y : ℂ) * ((T + h * x : ℝ) : ℂ))
          = cexp (I * ((w * L * T : ℝ) : ℂ))
            * cexp (-(I * ((w * L - y : ℝ) : ℂ) * ((T + h * x : ℝ) : ℂ))) := by
        have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        rw [hh]
        push_cast
        field_simp
        ring
      linear_combination ((W (T + h * x) : ℝ) : ℂ) * e1
    rw [Real.fourier_real_eq]
    simp_rw [hpt]
    have h1 := Measure.integral_comp_mul_left (fun z => G (T + z)) h
    rw [h1, integral_add_left_eq_self G T, hG, integral_const_mul, hWF _ hw, mul_zero, smul_zero]
  have hFO : 𝓕 g =O[cocompact ℝ] fun x => |x| ^ (-2 : ℝ) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop ((|y| + B) / L))]
      with w hw
    rw [Real.norm_eq_abs, div_le_iff₀ hL] at hw
    rw [hF0 w]
    · simp
    · have h1 : |w * L| - |y| ≤ |w * L - y| := abs_sub_abs_le_abs_sub _ _
      rw [abs_mul, abs_of_pos hL] at h1
      linarith
  have hsum : Summable (fun k : ℤ => g k) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) (hgO.comp_tendsto Int.tendsto_coe_cofinite)
  have key := Real.tsum_eq_tsum_fourier_of_rpow_decay hgc one_lt_two hgO hFO 0
  simp only [zero_add] at key
  have h0 : ∀ n : ℤ, 𝓕 g n * fourier n ((0 : ℝ) : UnitAddCircle) = 0 := by
    intro n
    rw [hF0 n (hy n), zero_mul]
  simp_rw [h0, tsum_zero] at key
  have hfin : HasSum (fun k : ℤ => g k) 0 := by rw [← key]; exact hsum.hasSum
  convert hfin using 1

/-- **The transform of an interval average of a profile:** for `P` continuous, integrable and nonnegative,
`∫ (∫_{τ−s₁}^{τ−s₀} P) e^{−iyτ} dτ = (∫ P(v) e^{−iyv} dv) · ∫_{s₀}^{s₁} e^{−iyu} du`. -/
theorem integral_profileWindow_mul_cexp {P : ℝ → ℝ} (hPc : Continuous P) (hPi : Integrable P)
    (hP0 : ∀ v, 0 ≤ P v) {s₀ s₁ : ℝ} (h01 : s₀ ≤ s₁) (y : ℝ) :
    ∫ τ, ((∫ v in (τ - s₁)..(τ - s₀), P v : ℝ) : ℂ) * cexp (-(I * y * τ))
      = (∫ v, ((P v : ℝ) : ℂ) * cexp (-(I * y * v))) * ∫ u in s₀..s₁, cexp (-(I * y * u)) := by
  set ν : Measure ℝ := volume.restrict (Ioc s₀ s₁) with hν
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  set h : ℝ → ℝ → ℂ := fun τ u => ((P (τ - u) : ℝ) : ℂ) * cexp (-(I * y * τ)) with hh
  have hpt : ∀ τ : ℝ, ((∫ v in (τ - s₁)..(τ - s₀), P v : ℝ) : ℂ) * cexp (-(I * y * τ))
      = ∫ u, h τ u ∂ν := by
    intro τ
    rw [← intervalIntegral.integral_comp_sub_left (fun v => P v) τ,
      intervalIntegral.integral_of_le h01, ← integral_complex_ofReal, ← integral_mul_const]
  simp_rw [hpt]
  have hnorm : ∀ τ u, ‖h τ u‖ = P (τ - u) := by
    intro τ u
    rw [hh]
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP0 _),
      show -(I * (y : ℂ) * (τ : ℂ)) = ((-(y * τ)) : ℝ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hint : Integrable (Function.uncurry h) (volume.prod ν) := by
    have hc : Continuous (Function.uncurry h) := by
      simp only [hh]
      fun_prop
    refine (integrable_prod_iff' hc.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · refine Eventually.of_forall fun u => ?_
      refine Integrable.mono' (hPi.comp_sub_right u) (by fun_prop : Continuous fun τ => h τ u).aestronglyMeasurable
        (Eventually.of_forall fun τ => le_of_eq (hnorm τ u))
    · have : (fun u => ∫ τ, ‖Function.uncurry h (τ, u)‖) = fun _ => ∫ v, P v := by
        funext u
        simp only [Function.uncurry_apply_pair, hnorm]
        exact integral_sub_right_eq_self P u
      rw [this]
      exact integrable_const _
  rw [integral_integral_swap hint]
  have hinner : ∀ u, ∫ τ, h τ u = cexp (-(I * y * u)) * ∫ v, ((P v : ℝ) : ℂ) * cexp (-(I * y * v)) := by
    intro u
    set f : ℝ → ℂ := fun v => ((P v : ℝ) : ℂ) * cexp (-(I * y * v)) * cexp (-(I * y * u)) with hf
    have hfh : ∀ τ, h τ u = f (τ - u) := by
      intro τ
      simp only [hh, hf, mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    simp_rw [hfh]
    rw [integral_sub_right_eq_self f u, hf, integral_mul_const]
    ring
  simp_rw [hinner]
  rw [integral_mul_const, intervalIntegral.integral_of_le h01]
  ring

variable {b s₀ s₁ : ℝ}

/-- The Jackson window has no Fourier mass at frequencies `|y| ≥ 2b`. -/
theorem integral_jacksonWindow_mul_cexp_eq_zero (hb : 0 < b) (h01 : s₀ ≤ s₁) {y : ℝ}
    (hy : 2 * b ≤ |y|) : ∫ τ, ((jacksonWindow b s₀ s₁ τ : ℝ) : ℂ) * cexp (-(I * y * τ)) = 0 := by
  have e : ∀ τ, ((jacksonWindow b s₀ s₁ τ : ℝ) : ℂ) * cexp (-(I * y * τ))
      = (((jacksonMass b)⁻¹ : ℝ) : ℂ)
        * (((∫ v in (τ - s₁)..(τ - s₀), jacksonProfile b v : ℝ) : ℂ) * cexp (-(I * y * τ))) := by
    intro τ; unfold jacksonWindow; push_cast; ring
  simp_rw [e]
  rw [integral_const_mul, integral_profileWindow_mul_cexp (continuous_jacksonProfile hb)
    (integrable_jacksonProfile hb) (jacksonProfile_nonneg b) h01,
    integral_jacksonProfile_mul_cexp_eq_zero hb hy, zero_mul, mul_zero]

/-- Quadratic decay of the Jackson window away from the interval (with an explicit constant). -/
theorem abs_jacksonWindow_le_inv_sq (hb : 0 < b) (h01 : s₀ ≤ s₁) {s : ℝ}
    (hs : 2 * (|s₀| + |s₁| + 1) ≤ |s|) :
    |jacksonWindow b s₀ s₁ s| ≤ (jacksonMass b)⁻¹ * (64 / (3 * b ^ 2)) / s ^ 2 := by
  have hk := jacksonMass_pos hb
  rw [abs_of_nonneg (jacksonWindow_nonneg hb h01 s)]
  have h0 := abs_nonneg s₀
  have h1 := abs_nonneg s₁
  rcases le_or_gt 0 s with hsp | hsn
  · rw [abs_of_nonneg hsp] at hs
    have hD : s / 2 ≤ s - s₁ := by linarith [le_abs_self s₁]
    have hD1 : 1 ≤ s - s₁ := by linarith [le_abs_self s₁]
    have hW := jacksonWindow_le_right hb (s₀ := s₀) (s₁ := s₁) (s := s) (D := s - s₁) (by linarith)
      (by linarith)
    refine hW.trans ?_
    have hs0 : 0 < s := by linarith
    have hcube : s ^ 2 / 4 ≤ (s - s₁) ^ 3 := by
      have : (s / 2) ^ 2 ≤ (s - s₁) ^ 2 := pow_le_pow_left₀ (by positivity) hD 2
      nlinarith
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hk.le)
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg b]
  · rw [abs_of_neg hsn] at hs
    have hD : -s / 2 ≤ s₀ - s := by linarith [neg_abs_le s₀]
    have hD1 : 1 ≤ s₀ - s := by linarith [neg_abs_le s₀]
    have hW := jacksonWindow_le_left hb (s₀ := s₀) (s₁ := s₁) (s := s) (D := s₀ - s) (by linarith)
      (by linarith)
    refine hW.trans ?_
    have hcube : s ^ 2 / 4 ≤ (s₀ - s) ^ 3 := by
      have : (-s / 2) ^ 2 ≤ (s₀ - s) ^ 2 := pow_le_pow_left₀ (by linarith) hD 2
      nlinarith
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hk.le)
    have hs2 : 0 < s ^ 2 := by nlinarith
    have hsc : 0 < (s₀ - s) ^ 3 := by positivity
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg b]

/-- **Jackson grid character sums vanish off the aliases:** if `|jL − y| ≥ 2b` for every `j ∈ ℤ`, then
`Σ_{k∈ℤ} W(τ_k) e^{iyτ_k} = 0` for the Jackson window `W` on the grid `τ_k = T + k·2π/L`. -/
theorem hasSum_jackson_grid_char_eq_zero (hb : 0 < b) (h01 : s₀ ≤ s₁) {L : ℝ} (hL : 0 < L) (T y : ℝ)
    (hy : ∀ j : ℤ, 2 * b ≤ |j * L - y|) :
    HasSum (fun k : ℤ => ((jacksonWindow b s₀ s₁ (T + k * (2 * π / L)) : ℝ) : ℂ)
      * cexp (I * y * ((T + k * (2 * π / L) : ℝ) : ℂ))) 0 :=
  hasSum_grid_char_eq_zero_of_window (continuous_jacksonWindow hb)
    (by have := (jacksonMass_pos hb).le; positivity)
    (fun s hs => abs_jacksonWindow_le_inv_sq hb h01 hs)
    (fun η hη => integral_jacksonWindow_mul_cexp_eq_zero hb h01 hη) hL T y hy

end FejerWeight

end RHTower

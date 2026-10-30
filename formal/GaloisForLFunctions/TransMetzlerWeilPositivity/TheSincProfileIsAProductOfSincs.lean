import GaloisForLFunctions.TransMetzlerWeilPositivity.TheSincProductProfile
import GaloisForLFunctions.HTGeometry.NyquistLatticeSum
import GaloisForLFunctions.HTGeometry.FourierDecayFromDerivative
import GaloisForLFunctions.HTGeometry.FourierFirstOrderWeight
import GaloisForLFunctions.HTGeometry.QuantitativeMonomialWallCrossingLaw
import GaloisForLFunctions.RHTower.BaezDuarteDistancePlancherel

/-!
# The Fourier transform of the sinc-product profile

With `𝓕f(ξ) = ∫ f(x) e^{−2πixξ} dx`:

* a Steklov average of radius `a` multiplies the transform by `sinc(2πaξ)`
  (`fourier_steklovAvg`; Fubini and `∫_{−a}^{a} e^{2πitξ} dt = 2a sinc(2πaξ)`);
* hence `𝓕(boxSeq M)(ξ) = Π_{j ≤ M} sinc(2π r_j ξ) · 𝓕β(a_M ξ)` for the base bump `β`
  (`fourier_boxSeq`), and, since the bumps shrink, the partial products
  `sincPartial m ξ = Π_{j<m} sinc(2π r_j ξ)` converge to `𝓕 sincProfile (ξ)`
  (`tendsto_sincPartial`);
* factors with `2π r_j |ξ| ≤ 1` are at least `e^{−(2π r_j ξ)²/3}`, so the transform is bounded
  below by a finite partial product times `exp(−(4π²ξ²/3) Σ_{j ≥ J} r_j²)`
  (`abs_sincPartial_mul_exp_le_norm_fourier`).
-/

noncomputable section

open MeasureTheory Filter Topology Real
open scoped ContDiff FourierTransform

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

/-! ### One Steklov average -/

/-- `∫_{−a}^{a} e^{2πitξ} dt = 2a sinc(2πaξ)`. -/
theorem integral_fourierChar_Icc {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    (∫ t in (-a)..a, (𝐞 (t * ξ) : ℂ)) = 2 * a * (Real.sinc (2 * π * a * ξ) : ℂ) := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp
    ring
  have hπ := Real.pi_pos
  have hc : (2 * π * ξ * Complex.I : ℂ) ≠ 0 := by
    simp [hξ, Real.pi_ne_zero, Complex.I_ne_zero]
  have h1 : (fun t : ℝ => (𝐞 (t * ξ) : ℂ)) =
      fun t : ℝ => Complex.exp ((2 * π * ξ * Complex.I) * t) := by
    funext t
    rw [Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  rw [h1, integral_exp_mul_complex hc]
  set y : ℝ := 2 * π * a * ξ with hy
  have hs : y ≠ 0 := by rw [hy]; positivity
  rw [Real.sinc_of_ne_zero hs]
  have e1 : (2 * π * ξ * Complex.I : ℂ) * (a : ℂ) = (y : ℂ) * Complex.I := by
    rw [hy]; push_cast; ring
  have e2 : (2 * π * ξ * Complex.I : ℂ) * ((-a : ℝ) : ℂ) = ((-y : ℝ) : ℂ) * Complex.I := by
    rw [hy]; push_cast; ring
  rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ
  have hπc : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [hy]
  push_cast
  field_simp
  ring

/-- **A Steklov average multiplies the Fourier transform by `sinc(2πaξ)`.** -/
theorem fourier_steklovAvg {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {a : ℝ}
    (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun x => (steklovAvg a f x : ℂ)) ξ =
      (Real.sinc (2 * π * a * ξ) : ℂ) * 𝓕 (fun x => (f x : ℂ)) ξ := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
  set F : ℝ → ℝ → ℂ := fun t v => 𝐞 (-(v * ξ)) • ((f (v + t) : ℝ) : ℂ) with hFdef
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Set.uIoc (-a) a)).prod volume) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry F)
        ((volume.restrict (Set.uIoc (-a) a)).prod volume) := by
      refine Continuous.aestronglyMeasurable ?_
      simp only [hFdef, Function.uncurry_def]
      fun_prop
    rw [integrable_prod_iff hmeas]
    refine ⟨Filter.Eventually.of_forall fun t => ?_, ?_⟩
    · simp only [Function.uncurry_apply_pair, hFdef]
      refine Integrable.mono' (hfi.comp_add_right t).abs ?_
        (Filter.Eventually.of_forall fun v => ?_)
      · exact (by fun_prop : Continuous fun v : ℝ =>
          𝐞 (-(v * ξ)) • ((f (v + t) : ℝ) : ℂ)).aestronglyMeasurable
      · simp [Circle.smul_def]
    · have hconst : (fun t => ∫ v, ‖Function.uncurry F (t, v)‖) = fun _ => ∫ v, |f v| := by
        funext t
        simp only [Function.uncurry_apply_pair, hFdef, Circle.smul_def, smul_eq_mul, norm_mul,
          Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact integral_add_right_eq_self (μ := volume) (fun v => |f v|) t
      rw [hconst]
      haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (-a) a)) :=
        isFiniteMeasure_restrict.mpr (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
      exact integrable_const _
  have hS : ∀ v, ((steklovAvg a f v : ℝ) : ℂ) =
      ((2 * a : ℝ)⁻¹ : ℂ) * ∫ t in (-a)..a, ((f (v + t) : ℝ) : ℂ) := by
    intro v
    simp only [steklovAvg]
    push_cast
    rw [intervalIntegral.integral_ofReal]
  have hinner : ∀ t, ∫ v, F t v = (𝐞 (t * ξ) : ℂ) * 𝓕 (fun x => (f x : ℂ)) ξ := by
    intro t
    rw [fourier_real_eq, ← integral_const_mul]
    have := integral_add_right_eq_self (μ := volume)
      (fun u => (𝐞 (t * ξ) : ℂ) * (𝐞 (-(u * ξ)) • ((f u : ℝ) : ℂ))) t
    rw [← this]
    congr 1
    funext v
    simp only [hFdef, smul_eq_mul, Circle.smul_def]
    rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3
    ring
  calc 𝓕 (fun x => (steklovAvg a f x : ℂ)) ξ
      = ∫ v, 𝐞 (-(v * ξ)) • (((2 * a : ℝ)⁻¹ : ℂ) *
          ∫ t in (-a)..a, ((f (v + t) : ℝ) : ℂ)) := by
        rw [fourier_real_eq]; simp_rw [hS]
    _ = ((2 * a : ℝ)⁻¹ : ℂ) * ∫ v, ∫ t in (-a)..a, F t v := by
        rw [← integral_const_mul]
        congr 1
        funext v
        simp only [hFdef, Circle.smul_def, smul_eq_mul]
        rw [intervalIntegral.integral_const_mul]
        ring
    _ = ((2 * a : ℝ)⁻¹ : ℂ) * ∫ t in (-a)..a, ∫ v, F t v := by
        rw [intervalIntegral_integral_swap hint]
    _ = ((2 * a : ℝ)⁻¹ : ℂ) *
          ((∫ t in (-a)..a, (𝐞 (t * ξ) : ℂ)) * 𝓕 (fun x => (f x : ℂ)) ξ) := by
        simp_rw [hinner]
        rw [intervalIntegral.integral_mul_const]
    _ = (Real.sinc (2 * π * a * ξ) : ℂ) * 𝓕 (fun x => (f x : ℂ)) ξ := by
        rw [integral_fourierChar_Icc ha ξ]
        have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
        push_cast
        field_simp

/-! ### The approximants -/

/-- Partial sinc products `Π_{j<m} sinc(2π r_j ξ)`. -/
def sincPartial (m : ℕ) (ξ : ℝ) : ℝ := ∏ j ∈ Finset.range m, Real.sinc (2 * π * sincRadius j * ξ)

theorem hasCompactSupport_boxStek {β : ℝ → ℝ} {R : ℝ} (hβ : SupportedIn R β) (m : ℕ) :
    HasCompactSupport (boxStek β m) :=
  hasCompactSupport_of_vanishes (supportedIn_boxStek hβ m)

theorem fourier_boxStek {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {R : ℝ} (hβR : SupportedIn R β)
    (m : ℕ) (ξ : ℝ) :
    𝓕 (fun x => (boxStek β m x : ℂ)) ξ = (sincPartial m ξ : ℂ) * 𝓕 (fun x => (β x : ℂ)) ξ := by
  induction m with
  | zero => simp [sincPartial, boxStek]
  | succ m ih =>
    show 𝓕 (fun x => (steklovAvg (sincRadius m) (boxStek β m) x : ℂ)) ξ = _
    rw [fourier_steklovAvg (contDiff_boxStek hβ m).continuous (hasCompactSupport_boxStek hβR m)
      (sincRadius_pos m), ih]
    simp only [sincPartial, Finset.prod_range_succ]
    push_cast
    ring

/-- The base bump transforms to the base transform at the shrunken frequency. -/
theorem fourier_boxBase (M : ℕ) (ξ : ℝ) :
    𝓕 (fun x => (boxBase M x : ℂ)) ξ =
      𝓕 (fun x => (steklovBase x : ℂ)) (steklovRadius M * ξ) := by
  have ha := steklovRadius_pos M
  set k := (steklovRadius M)⁻¹ with hk
  have hk0 : 0 < k := inv_pos.mpr ha
  have hfun : (fun x => (boxBase M x : ℂ)) =
      fun x => (k : ℂ) * (fun y => (steklovBase y : ℂ)) (k * x) := by
    funext x; simp [boxBase, dilate, hk]
  have h := HTGeometry.fourier_comp_mul_pos hk0 (fun y => (steklovBase y : ℂ)) ξ
  rw [hfun]
  have hlin : 𝓕 (fun x => (k : ℂ) * (fun y => (steklovBase y : ℂ)) (k * x)) ξ =
      (k : ℂ) * 𝓕 (fun x => (fun y => (steklovBase y : ℂ)) (k * x)) ξ :=
    RHTower.fourier_const_mul_fun _ _ ξ
  rw [hlin, h, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hk0.ne'), one_mul]
  rw [hk, div_inv_eq_mul, mul_comm]

theorem fourier_boxSeq (M : ℕ) (ξ : ℝ) :
    𝓕 (fun x => (boxSeq M x : ℂ)) ξ =
      (sincPartial (M + 1) ξ : ℂ) * 𝓕 (fun x => (steklovBase x : ℂ)) (steklovRadius M * ξ) := by
  rw [boxSeq, fourier_boxStek (contDiff_boxBase M) (fun u hu => boxBase_eq_zero hu),
    fourier_boxBase]

/-! ### Passing to the limit -/

theorem tendsto_fourier_boxSeq (ξ : ℝ) :
    Tendsto (fun M => 𝓕 (fun x => (boxSeq M x : ℂ)) ξ) atTop
      (𝓝 (𝓕 (fun x => (sincProfile x : ℂ)) ξ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hunif := Metric.tendstoUniformly_iff.mp tendstoUniformly_boxSeq (ε / 4) (by positivity)
  filter_upwards [hunif] with M hM
  rw [dist_eq_norm]
  have hlin : 𝓕 (fun x => (boxSeq M x : ℂ)) ξ - 𝓕 (fun x => (sincProfile x : ℂ)) ξ =
      𝓕 (fun x => ((boxSeq M x - sincProfile x : ℝ) : ℂ)) ξ := by
    have hb : Integrable (fun x => (boxSeq M x : ℂ)) :=
      ((contDiff_boxSeq M).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_of_vanishes (supportedIn_boxSeq M))).ofReal
    have hs : Integrable (fun x => (sincProfile x : ℂ)) :=
      (contDiff_sincProfile.continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_of_vanishes sincProfile_vanishesOff)).ofReal
    rw [show (fun x => ((boxSeq M x - sincProfile x : ℝ) : ℂ)) =
      (fun x => (boxSeq M x : ℂ) - (sincProfile x : ℂ)) by
        funext x; push_cast; rfl]
    exact (RHTower.fourier_sub_of_integrable hb hs ξ).symm
  rw [hlin]
  refine (HTGeometry.norm_fourierReal_le_integral_norm _ ξ).trans_lt ?_
  have hd : Continuous fun x => boxSeq M x - sincProfile x :=
    (contDiff_boxSeq M).continuous.sub contDiff_sincProfile.continuous
  have hdR : SupportedIn 1 fun x => boxSeq M x - sincProfile x := fun x hx => by
    simp only [supportedIn_boxSeq M x hx, sincProfile_vanishesOff x hx, sub_zero]
  have hb := integral_abs_le_of_bound hd (hasCompactSupport_of_vanishes hdR)
    (fun x => by
      have := hM x
      rw [Real.dist_eq, abs_sub_comm] at this
      exact this.le) hdR zero_le_one
  simp only [Complex.norm_real, Real.norm_eq_abs]
  linarith

theorem tendsto_fourier_steklovBase_shrink (ξ : ℝ) :
    Tendsto (fun M => 𝓕 (fun x => (steklovBase x : ℂ)) (steklovRadius M * ξ)) atTop (𝓝 1) := by
  have hcont : Continuous (𝓕 (fun x => (steklovBase x : ℂ))) :=
    HTGeometry.continuous_fourier ((contDiff_steklovBase.continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanishes supportedIn_steklovBase)).ofReal)
  have hrad : Tendsto (fun M => steklovRadius M * ξ) atTop (𝓝 0) := by
    have h0 : Tendsto steklovRadius atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        tendsto_one_div_atTop_nhds_zero_nat
        (Eventually.of_forall fun M => (steklovRadius_pos M).le) ?_
      filter_upwards [eventually_ge_atTop 1] with M hM
      have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
      unfold steklovRadius
      have hl : 1 ≤ Real.log ((M : ℝ) + 3) := by
        rw [Real.le_log_iff_exp_le (by positivity)]
        have := Real.exp_one_lt_d9
        linarith [Nat.cast_nonneg (α := ℝ) M]
      apply one_div_le_one_div_of_le hM0
      have : (1 : ℝ) ≤ Real.log ((M : ℝ) + 3) ^ 2 := one_le_pow₀ hl
      nlinarith [Nat.cast_nonneg (α := ℝ) M]
    simpa using h0.mul_const ξ
  have h := (hcont.tendsto 0).comp hrad
  rw [HTGeometry.fourier_zero_eq_integral] at h
  have hint : ∫ v, (steklovBase v : ℂ) = 1 := by
    rw [integral_complex_ofReal, integral_steklovBase]; simp
  rw [hint] at h
  exact h

/-- **The transform is the limit of the partial sinc products.** -/
theorem tendsto_sincPartial (ξ : ℝ) :
    Tendsto (fun M => (sincPartial (M + 1) ξ : ℂ)) atTop
      (𝓝 (𝓕 (fun x => (sincProfile x : ℂ)) ξ)) := by
  have h1 := tendsto_fourier_boxSeq ξ
  have h2 := tendsto_fourier_steklovBase_shrink ξ
  have hne : ∀ᶠ M in atTop, 𝓕 (fun x => (steklovBase x : ℂ)) (steklovRadius M * ξ) ≠ 0 :=
    h2.eventually (isOpen_ne.mem_nhds one_ne_zero)
  have hq := h1.div h2 one_ne_zero
  rw [div_one] at hq
  refine hq.congr' ?_
  filter_upwards [hne] with M hM
  simp only [Pi.div_apply]
  rw [fourier_boxSeq, mul_div_cancel_right₀ _ hM]

/-! ### A lower bound from small arguments -/

/-- `sinc x ≥ e^{−x²/3}` for `|x| ≤ 1`, from `sinc x ≥ 1 − x²/6`. -/
theorem exp_neg_sq_div_three_le_sinc {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp (-(x ^ 2 / 3)) ≤ Real.sinc x := by
  have h6 : 1 - x ^ 2 / 6 ≤ Real.sinc x := by
    have := HTGeometry.abs_real_sinc_sub_one_le_sq_div_six x
    have := (abs_le.mp this).1
    linarith
  set y := x ^ 2 / 6 with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 / 2 := by
    have : x ^ 2 ≤ 1 := by
      have := abs_le.mp hx
      nlinarith
    rw [hy]; linarith
  have he : 1 + 2 * y ≤ Real.exp (2 * y) := by
    have := Real.add_one_le_exp (2 * y); linarith
  have hpos : 0 < Real.exp (2 * y) := Real.exp_pos _
  have h1 : Real.exp (-(x ^ 2 / 3)) = (Real.exp (2 * y))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; rw [hy]; ring
  rw [h1]
  refine le_trans ?_ h6
  rw [inv_le_iff_one_le_mul₀ hpos]
  have : 1 ≤ (1 - y) * (1 + 2 * y) := by nlinarith
  nlinarith

/-- **Lower bound by a finite product.** If every factor beyond `J` has `2π r_j |ξ| ≤ 1` and
`Σ_{J ≤ j < M} r_j² ≤ S` for all `M`, then
`|Π_{j<J} sinc(2π r_j ξ)| · exp(−(4π²ξ²/3) S) ≤ ‖𝓕 sincProfile (ξ)‖`. -/
theorem abs_sincPartial_mul_exp_le_norm_fourier {J : ℕ} {ξ S : ℝ}
    (hsmall : ∀ j, J ≤ j → 2 * π * sincRadius j * |ξ| ≤ 1)
    (hS : ∀ M, ∑ j ∈ Finset.Ico J M, sincRadius j ^ 2 ≤ S) :
    |sincPartial J ξ| * Real.exp (-(4 * π ^ 2 * ξ ^ 2 / 3 * S)) ≤
      ‖𝓕 (fun x => (sincProfile x : ℂ)) ξ‖ := by
  have hlim := (tendsto_sincPartial ξ).norm
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop J] with M hM
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have hsplit : sincPartial (M + 1) ξ = sincPartial J ξ *
      ∏ j ∈ Finset.Ico J (M + 1), Real.sinc (2 * π * sincRadius j * ξ) := by
    rw [sincPartial, sincPartial, ← Finset.prod_range_mul_prod_Ico _ (by omega : J ≤ M + 1)]
  rw [hsplit, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hfac : ∀ j ∈ Finset.Ico J (M + 1),
      Real.exp (-((2 * π * sincRadius j * ξ) ^ 2 / 3)) ≤ Real.sinc (2 * π * sincRadius j * ξ) := by
    intro j hj
    refine exp_neg_sq_div_three_le_sinc ?_
    have hr := (sincRadius_pos j).le
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π * sincRadius j)]
    exact hsmall j (Finset.mem_Ico.mp hj).1
  have hprod : Real.exp (-(∑ j ∈ Finset.Ico J (M + 1), (2 * π * sincRadius j * ξ) ^ 2 / 3)) ≤
      ∏ j ∈ Finset.Ico J (M + 1), Real.sinc (2 * π * sincRadius j * ξ) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod (fun j _ => (Real.exp_pos _).le) hfac
  have hsum : ∑ j ∈ Finset.Ico J (M + 1), (2 * π * sincRadius j * ξ) ^ 2 / 3 ≤
      4 * π ^ 2 * ξ ^ 2 / 3 * S := by
    have hrw : ∑ j ∈ Finset.Ico J (M + 1), (2 * π * sincRadius j * ξ) ^ 2 / 3 =
        4 * π ^ 2 * ξ ^ 2 / 3 * ∑ j ∈ Finset.Ico J (M + 1), sincRadius j ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left (hS (M + 1)) (by positivity)
  calc Real.exp (-(4 * π ^ 2 * ξ ^ 2 / 3 * S))
      ≤ Real.exp (-(∑ j ∈ Finset.Ico J (M + 1), (2 * π * sincRadius j * ξ) ^ 2 / 3)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := hprod
    _ ≤ |∏ j ∈ Finset.Ico J (M + 1), Real.sinc (2 * π * sincRadius j * ξ)| := le_abs_self _

end GaloisForLFunctions.TransMetzlerWeilPositivity

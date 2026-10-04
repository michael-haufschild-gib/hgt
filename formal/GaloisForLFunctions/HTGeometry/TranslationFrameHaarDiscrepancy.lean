import Mathlib
import GaloisForLFunctions.HTGeometry.YoungConvolutionL2
import GaloisForLFunctions.HTGeometry.FourierTranslationModulation

/-!
# Frames of translates against a cumulative discrepancy

Let `h ∈ W^{1,1}(ℝ) ∩ L²(ℝ)` with weak derivative `h'`, and let `T_y h = h(· - y)`.  For
`f ∈ L²(ℝ)` the translate correlation `g_f(y) = ⟪f, T_y h⟫` obeys Young's inequality
`‖g_f‖₂ ≤ ‖h‖₁ ‖f‖₂`, is absolutely continuous with derivative
`G_f(y) = -∫ conj (f x) h'(x - y) dx`, and `‖G_f‖₂ ≤ ‖h'‖₁ ‖f‖₂`.  Hence `q_f = |g_f|²` is
absolutely continuous with `‖q_f'‖₁ ≤ 2 ‖h‖₁ ‖h'‖₁ ‖f‖₂²` and tends to zero at infinity.

Stieltjes integration by parts on bounded windows then compares a measure `μ` on the future
half-line with Lebesgue measure through the cumulative discrepancy `μ[0, y] - y`: if that
discrepancy is at most `ε` in absolute value, then

`|∫ q_f dμ - ∫_0^∞ q_f dy| ≤ ε ‖q_f'‖₁ ≤ 2 ε ‖h‖₁ ‖h'‖₁ ‖f‖₂²`.

* `SobolevTranslateWindow` — the window hypotheses;
* `translateCorrelation`, `translateCorrelation_eq_integral` — `g_f`;
* `lintegral_translateCorrelation_sq_le`, `lintegral_derivCorrelation_sq_le` — Young bounds;
* `translateCorrelation_sub_eq_integral` — `g_f(y) - g_f(z) = ∫_z^y G_f`;
* `normSq_sub_eq_integral_of_primitive` — the product rule for primitives of locally integrable
  functions;
* `abs_setIntegral_Icc_sub_le` — Stieltjes comparison on a bounded window.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ### The window and its translate correlations -/

/-- A `W^{1,1}(ℝ) ∩ L²(ℝ)` window `h` with weak derivative `h'`, in its absolutely continuous
representative: `h y - h x = ∫_x^y h'`. -/
structure SobolevTranslateWindow (h h' : ℝ → ℂ) : Prop where
  integrable : Integrable h
  memLp_two : MemLp h 2
  integrable_deriv : Integrable h'
  sub_eq_integral : ∀ x y, h y - h x = ∫ t in x..y, h' t

/-- Right translate on `L²(ℝ)`: `(T_y w)(x) = w (x - y)`. -/
def translateRight (y : ℝ) (w : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  translateL2 (-y) w

theorem coeFn_translateRight (y : ℝ) (w : Lp ℂ 2 (volume : Measure ℝ)) :
    (translateRight y w : ℝ → ℂ) =ᵐ[volume] fun x => (w : ℝ → ℂ) (x - y) := by
  filter_upwards [coeFn_translateL2 (-y) w] with x hx
  rw [translateRight, hx, sub_eq_add_neg]

@[simp] theorem norm_translateRight (y : ℝ) (w : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖translateRight y w‖ = ‖w‖ :=
  (translateL2 (-y)).norm_map w

/-- The translate correlation `g_f(y) = ⟪f, T_y w⟫`. -/
def translateCorrelation (w f : Lp ℂ 2 (volume : Measure ℝ)) (y : ℝ) : ℂ :=
  ⟪f, translateRight y w⟫_ℂ

theorem norm_translateCorrelation_le (w f : Lp ℂ 2 (volume : Measure ℝ)) (y : ℝ) :
    ‖translateCorrelation w f y‖ ≤ ‖f‖ * ‖w‖ := by
  have := norm_inner_le_norm (𝕜 := ℂ) f (translateRight y w)
  rwa [norm_translateRight] at this

theorem lintegral_enorm_sq_ne_top (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ 2 ≠ ⊤ := by
  have h := (Lp.memLp f).eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h
  have h2 : (∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ ((2 : ℝ≥0∞).toReal)) ≠ ⊤ := by
    intro htop
    rw [htop] at h
    simp at h
  simpa [ENNReal.toReal_ofNat, ENNReal.rpow_two] using h2

namespace SobolevTranslateWindow

variable {h h' : ℝ → ℂ}

theorem continuous (W : SobolevTranslateWindow h h') : Continuous h := by
  have hprim : Continuous fun y => ∫ t in (0 : ℝ)..y, h' t :=
    intervalIntegral.continuous_primitive (fun a b => W.integrable_deriv.intervalIntegrable) 0
  have heq : h = fun y => h 0 + ∫ t in (0 : ℝ)..y, h' t := by
    funext y
    rw [← W.sub_eq_integral 0 y]
    ring
  rw [heq]
  exact continuous_const.add hprim

theorem measurable (W : SobolevTranslateWindow h h') : Measurable h :=
  W.continuous.measurable

/-- The window as an element of `L²(ℝ)`. -/
def toL2 (W : SobolevTranslateWindow h h') : Lp ℂ 2 (volume : Measure ℝ) :=
  W.memLp_two.toLp h

theorem coeFn_toL2 (W : SobolevTranslateWindow h h') :
    (W.toL2 : ℝ → ℂ) =ᵐ[volume] h :=
  W.memLp_two.coeFn_toLp

/-- A measurable representative of the weak derivative. -/
def derivRep (W : SobolevTranslateWindow h h') : ℝ → ℂ :=
  W.integrable_deriv.aestronglyMeasurable.mk h'

theorem stronglyMeasurable_derivRep (W : SobolevTranslateWindow h h') :
    StronglyMeasurable W.derivRep :=
  W.integrable_deriv.aestronglyMeasurable.stronglyMeasurable_mk

theorem derivRep_ae_eq (W : SobolevTranslateWindow h h') : h' =ᵐ[volume] W.derivRep :=
  W.integrable_deriv.aestronglyMeasurable.ae_eq_mk

theorem integrable_derivRep (W : SobolevTranslateWindow h h') : Integrable W.derivRep :=
  W.integrable_deriv.congr W.derivRep_ae_eq

/-- For every base point, the translated derivative agrees with its representative a.e. -/
theorem derivRep_comp_sub_ae_eq (W : SobolevTranslateWindow h h') (c : ℝ) :
    (fun s => h' (c - s)) =ᵐ[volume] fun s => W.derivRep (c - s) := by
  have hmp : MeasurePreserving (fun s : ℝ => c - s) volume volume :=
    Measure.measurePreserving_sub_left volume c
  exact hmp.quasiMeasurePreserving.ae_eq_comp W.derivRep_ae_eq

theorem sub_shift_eq_integral (W : SobolevTranslateWindow h h') (x y z : ℝ) :
    h (x - y) - h (x - z) = -∫ s in z..y, W.derivRep (x - s) := by
  have h1 : ∫ s in z..y, W.derivRep (x - s) = ∫ s in z..y, h' (x - s) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [W.derivRep_comp_sub_ae_eq x] with s hs _
    exact hs.symm
  rw [h1, intervalIntegral.integral_comp_sub_left (fun t => h' t) x, W.sub_eq_integral,
    intervalIntegral.integral_symm]

/-- The translate correlation as an integral. -/
theorem translateCorrelation_eq_integral (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) (y : ℝ) :
    translateCorrelation W.toL2 f y = ∫ x, conj ((f : ℝ → ℂ) x) * h (x - y) := by
  rw [translateCorrelation, L2.inner_def]
  refine integral_congr_ae ?_
  have hmp : MeasurePreserving (fun x : ℝ => x - y) volume volume :=
    measurePreserving_sub_right volume y
  have hcomp : (fun x => (W.toL2 : ℝ → ℂ) (x - y)) =ᵐ[volume] fun x => h (x - y) :=
    hmp.quasiMeasurePreserving.ae_eq_comp W.coeFn_toL2
  filter_upwards [coeFn_translateRight y W.toL2, hcomp] with x hx hx'
  rw [hx, hx', RCLike.inner_apply, mul_comm]

/-- The derivative correlation `G_f(y) = -∫ conj (f x) h'(x - y) dx`. -/
def derivCorrelation (W : SobolevTranslateWindow h h') (f : Lp ℂ 2 (volume : Measure ℝ))
    (y : ℝ) : ℂ :=
  -∫ x, conj ((f : ℝ → ℂ) x) * W.derivRep (x - y)

/-! ### Young bounds -/

private theorem lintegral_mul_shift_eq (F K : ℝ → ℝ≥0∞) (y : ℝ) :
    ∫⁻ x, F x * K (x - y) = ∫⁻ t, K (-t) * F (y - t) := by
  have h := lintegral_sub_left_eq_self (μ := (volume : Measure ℝ))
    (fun x => F x * K (x - y)) y
  rw [← h]
  refine lintegral_congr fun t => ?_
  rw [mul_comm]
  congr 2
  ring

/-- Pointwise convolution majorant of a correlation integral. -/
private theorem enorm_correlation_le (F : ℝ → ℂ) (k : ℝ → ℂ) (y : ℝ) :
    ‖∫ x, conj (F x) * k (x - y)‖ₑ ≤ ∫⁻ t, ‖k (-t)‖ₑ * ‖F (y - t)‖ₑ := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  rw [← lintegral_mul_shift_eq (fun x => ‖F x‖ₑ) (fun x => ‖k x‖ₑ) y]
  refine lintegral_congr fun x => ?_
  rw [enorm_mul, RCLike.enorm_conj]

private theorem lintegral_enorm_neg (k : ℝ → ℂ) :
    ∫⁻ t, ‖k (-t)‖ₑ = ∫⁻ t, ‖k t‖ₑ := by
  have h := lintegral_sub_left_eq_self (μ := (volume : Measure ℝ)) (fun t => ‖k t‖ₑ) 0
  simpa using h

/-- **Young's inequality** for the translate correlation: `‖g_f‖₂ ≤ ‖h‖₁‖f‖₂`. -/
theorem lintegral_translateCorrelation_sq_le (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫⁻ y, ‖translateCorrelation W.toL2 f y‖ₑ ^ 2 ≤
      (∫⁻ x, ‖h x‖ₑ) ^ 2 * ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ 2 := by
  have hK : Measurable fun t => ‖h (-t)‖ₑ := (W.measurable.comp measurable_neg).enorm
  have hF : Measurable fun x => ‖(f : ℝ → ℂ) x‖ₑ := (Lp.stronglyMeasurable f).measurable.enorm
  have hb := lintegral_enorm_sq_le_of_convolution_bound hK hF (G := translateCorrelation W.toL2 f)
    (fun y => by rw [W.translateCorrelation_eq_integral]; exact enorm_correlation_le _ h y)
  rwa [lintegral_enorm_neg h] at hb

/-- **Young's inequality** for the derivative correlation: `‖G_f‖₂ ≤ ‖h'‖₁‖f‖₂`. -/
theorem lintegral_derivCorrelation_sq_le (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫⁻ y, ‖W.derivCorrelation f y‖ₑ ^ 2 ≤
      (∫⁻ x, ‖h' x‖ₑ) ^ 2 * ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ 2 := by
  have hK : Measurable fun t => ‖W.derivRep (-t)‖ₑ :=
    (W.stronglyMeasurable_derivRep.measurable.comp measurable_neg).enorm
  have hF : Measurable fun x => ‖(f : ℝ → ℂ) x‖ₑ := (Lp.stronglyMeasurable f).measurable.enorm
  have hb := lintegral_enorm_sq_le_of_convolution_bound hK hF (G := W.derivCorrelation f)
    (fun y => by rw [derivCorrelation, enorm_neg]; exact enorm_correlation_le _ _ y)
  have hrep : ∫⁻ t, ‖W.derivRep t‖ₑ = ∫⁻ t, ‖h' t‖ₑ :=
    lintegral_congr_ae (W.derivRep_ae_eq.mono fun x hx => by simp only [hx])
  rwa [lintegral_enorm_neg, hrep] at hb


/-! ### The correlation is a primitive of the derivative correlation -/

private theorem enorm_le_sq_add_one (a : ℝ≥0∞) : a ≤ a ^ 2 + 1 := by
  rcases le_or_gt a 1 with ha | ha
  · exact ha.trans (le_add_self)
  · calc a = a * 1 := (mul_one a).symm
      _ ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + 1 := le_self_add

/-- The integrand `conj (f x) h'(x - s)` of the derivative correlation. -/
private def corrKernel (W : SobolevTranslateWindow h h') (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ℝ → ℝ → ℂ :=
  fun x s => conj ((f : ℝ → ℂ) x) * W.derivRep (x - s)

private theorem stronglyMeasurable_corrKernel (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    StronglyMeasurable (Function.uncurry (W.corrKernel f)) := by
  have h1 : StronglyMeasurable fun p : ℝ × ℝ => conj ((f : ℝ → ℂ) p.1) :=
    (continuous_star.comp_stronglyMeasurable (Lp.stronglyMeasurable f)).comp_measurable
      measurable_fst
  have h2 : StronglyMeasurable fun p : ℝ × ℝ => W.derivRep (p.1 - p.2) :=
    W.stronglyMeasurable_derivRep.comp_measurable (measurable_fst.sub measurable_snd)
  exact h1.mul h2

/-- `∫⁻ |h'(x - s)| ds ≤ ‖h'‖₁` over any set. -/
private theorem setLIntegral_derivRep_shift_le (W : SobolevTranslateWindow h h') (S : Set ℝ)
    (x : ℝ) : ∫⁻ s in S, ‖W.derivRep (x - s)‖ₑ ≤ ∫⁻ t, ‖W.derivRep t‖ₑ := by
  refine (setLIntegral_le_lintegral S _).trans (le_of_eq ?_)
  exact lintegral_sub_left_eq_self (μ := (volume : Measure ℝ)) (fun t => ‖W.derivRep t‖ₑ) x

private theorem lintegral_enorm_derivRep_ne_top (W : SobolevTranslateWindow h h') :
    ∫⁻ t, ‖W.derivRep t‖ₑ ≠ ⊤ :=
  (hasFiniteIntegral_iff_enorm.mp W.integrable_derivRep.hasFiniteIntegral).ne

private theorem integrable_corrKernel (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) (z y : ℝ) :
    Integrable (Function.uncurry (W.corrKernel f))
      ((volume : Measure ℝ).prod (volume.restrict (Ioc z y))) := by
  refine ⟨(W.stronglyMeasurable_corrKernel f).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _
    (W.stronglyMeasurable_corrKernel f).aestronglyMeasurable.enorm]
  set M := ∫⁻ t, ‖W.derivRep t‖ₑ
  set k : ℝ → ℝ≥0∞ := fun x => ∫⁻ s in Ioc z y, ‖W.derivRep (x - s)‖ₑ
  have hk : ∀ x, k x ≤ M := fun x => W.setLIntegral_derivRep_shift_le _ x
  have hkmeas : Measurable k := by
    have : Measurable (Function.uncurry fun (x s : ℝ) => ‖W.derivRep (x - s)‖ₑ) :=
      (W.stronglyMeasurable_derivRep.measurable.comp
        (measurable_fst.sub measurable_snd)).enorm
    exact this.lintegral_prod_right'
  have hkint : ∫⁻ x, k x = M * ENNReal.ofReal (y - z) := by
    have hsw := lintegral_lintegral_swap (μ := (volume : Measure ℝ))
      (ν := volume.restrict (Ioc z y)) (f := fun x s => ‖W.derivRep (x - s)‖ₑ)
      ((W.stronglyMeasurable_derivRep.measurable.comp
        (measurable_fst.sub measurable_snd)).enorm.aemeasurable)
    simp only [k]
    rw [hsw]
    have : ∀ s : ℝ, ∫⁻ x, ‖W.derivRep (x - s)‖ₑ = M := fun s =>
      lintegral_sub_right_eq_self (μ := (volume : Measure ℝ)) (fun t => ‖W.derivRep t‖ₑ) s
    simp_rw [this]
    rw [setLIntegral_const, Real.volume_Ioc, mul_comm]
  have hpt : ∀ x, ∫⁻ s in Ioc z y, ‖Function.uncurry (W.corrKernel f) (x, s)‖ₑ =
      ‖(f : ℝ → ℂ) x‖ₑ * k x := by
    intro x
    simp only [Function.uncurry_apply_pair, corrKernel, enorm_mul, RCLike.enorm_conj, k]
    exact lintegral_const_mul _
      ((W.stronglyMeasurable_derivRep.measurable.comp (measurable_const.sub measurable_id)).enorm)
  simp_rw [hpt]
  have hMfin : M < ⊤ := W.lintegral_enorm_derivRep_ne_top.lt_top
  have hpt2 : ∀ x, ‖(f : ℝ → ℂ) x‖ₑ * k x ≤ M * ‖(f : ℝ → ℂ) x‖ₑ ^ 2 + k x := by
    intro x
    have h1 : ‖(f : ℝ → ℂ) x‖ₑ * k x ≤ (‖(f : ℝ → ℂ) x‖ₑ ^ 2 + 1) * k x := by
      gcongr
      exact enorm_le_sq_add_one _
    have h2 : ‖(f : ℝ → ℂ) x‖ₑ ^ 2 * k x ≤ ‖(f : ℝ → ℂ) x‖ₑ ^ 2 * M := by
      gcongr
      exact hk x
    calc ‖(f : ℝ → ℂ) x‖ₑ * k x ≤ (‖(f : ℝ → ℂ) x‖ₑ ^ 2 + 1) * k x := h1
      _ = ‖(f : ℝ → ℂ) x‖ₑ ^ 2 * k x + k x := by rw [add_mul, one_mul]
      _ ≤ ‖(f : ℝ → ℂ) x‖ₑ ^ 2 * M + k x := by gcongr
      _ = M * ‖(f : ℝ → ℂ) x‖ₑ ^ 2 + k x := by rw [mul_comm]
  have hsum : ∫⁻ x, (M * ‖(f : ℝ → ℂ) x‖ₑ ^ 2 + k x) =
      M * (∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ 2) + M * ENNReal.ofReal (y - z) := by
    rw [lintegral_add_right _ hkmeas, lintegral_const_mul' _ _ hMfin.ne, hkint]
  have hfin : M * (∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ 2) + M * ENNReal.ofReal (y - z) < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hMfin (lintegral_enorm_sq_ne_top f).lt_top,
      ENNReal.mul_lt_top hMfin ENNReal.ofReal_lt_top⟩
  exact lt_of_le_of_lt ((lintegral_mono hpt2).trans (le_of_eq hsum)) hfin

/-- **The correlation is a primitive of the derivative correlation**:
`g_f(y) - g_f(z) = ∫_z^y G_f` for `z ≤ y`. -/
theorem translateCorrelation_sub_eq_integral (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) {z y : ℝ} (hzy : z ≤ y) :
    translateCorrelation W.toL2 f y - translateCorrelation W.toL2 f z =
      ∫ s in z..y, W.derivCorrelation f s := by
  have hint : ∀ c, Integrable (fun x => conj ((f : ℝ → ℂ) x) * h (x - c)) := by
    intro c
    refine (L2.integrable_inner (𝕜 := ℂ) f (translateRight c W.toL2)).congr ?_
    have hmp : MeasurePreserving (fun x : ℝ => x - c) volume volume :=
      measurePreserving_sub_right volume c
    have hcomp : (fun x => (W.toL2 : ℝ → ℂ) (x - c)) =ᵐ[volume] fun x => h (x - c) :=
      hmp.quasiMeasurePreserving.ae_eq_comp W.coeFn_toL2
    filter_upwards [coeFn_translateRight c W.toL2, hcomp] with x hx hx'
    rw [hx, hx', RCLike.inner_apply, mul_comm]
  rw [W.translateCorrelation_eq_integral, W.translateCorrelation_eq_integral,
    ← integral_sub (hint y) (hint z)]
  have hpt : ∀ x, conj ((f : ℝ → ℂ) x) * h (x - y) - conj ((f : ℝ → ℂ) x) * h (x - z) =
      -∫ s in z..y, W.corrKernel f x s := by
    intro x
    rw [← mul_sub, W.sub_shift_eq_integral x y z, mul_neg, ← intervalIntegral.integral_const_mul]
    rfl
  simp_rw [hpt]
  rw [integral_neg]
  simp_rw [intervalIntegral.integral_of_le hzy]
  rw [integral_integral_swap (W.integrable_corrKernel f z y), ← integral_neg]
  rfl

/-- The derivative correlation is strongly measurable. -/
theorem stronglyMeasurable_derivCorrelation (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) : StronglyMeasurable (W.derivCorrelation f) :=
  ((W.stronglyMeasurable_corrKernel f).integral_prod_left (μ := volume)).neg

/-- The derivative correlation lies in `L²`. -/
theorem memLp_derivCorrelation (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) : MemLp (W.derivCorrelation f) 2 := by
  refine (memLp_two_iff_integrable_sq_norm
    (W.stronglyMeasurable_derivCorrelation f).aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · exact ((W.stronglyMeasurable_derivCorrelation f).norm.pow 2).aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt (W.lintegral_derivCorrelation_sq_le f) ?_)
    · refine lintegral_congr fun y => ?_
      rw [enorm_pow, enorm_norm]
    · refine ENNReal.mul_lt_top (ENNReal.pow_lt_top ?_) (lintegral_enorm_sq_ne_top f).lt_top
      exact (hasFiniteIntegral_iff_enorm.mp W.integrable_deriv.hasFiniteIntegral)

theorem locallyIntegrable_derivCorrelation (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) : LocallyIntegrable (W.derivCorrelation f) volume :=
  (W.memLp_derivCorrelation f).locallyIntegrable (by norm_num)

/-- The correlation as a primitive from an arbitrary base point. -/
theorem translateCorrelation_eq_add_integral (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) (a y : ℝ) :
    translateCorrelation W.toL2 f y =
      translateCorrelation W.toL2 f a + ∫ s in a..y, W.derivCorrelation f s := by
  rcases le_total a y with hay | hya
  · rw [← W.translateCorrelation_sub_eq_integral f hay]; ring
  · rw [intervalIntegral.integral_symm, ← W.translateCorrelation_sub_eq_integral f hya]; ring

theorem continuous_translateCorrelation (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) : Continuous (translateCorrelation W.toL2 f) := by
  have hprim : Continuous fun y => ∫ s in (0 : ℝ)..y, W.derivCorrelation f s :=
    intervalIntegral.continuous_primitive
      (fun a b => ((W.locallyIntegrable_derivCorrelation f).integrableOn_isCompact
        isCompact_uIcc).intervalIntegrable) 0
  have heq : translateCorrelation W.toL2 f =
      fun y => translateCorrelation W.toL2 f 0 + ∫ s in (0 : ℝ)..y, W.derivCorrelation f s :=
    funext fun y => W.translateCorrelation_eq_add_integral f 0 y
  rw [heq]
  exact continuous_const.add hprim


/-- The window's `L¹` norms enter as finite `ℝ≥0∞` constants. -/
theorem lintegral_enorm_ne_top (W : SobolevTranslateWindow h h') : ∫⁻ x, ‖h x‖ₑ ≠ ⊤ :=
  (hasFiniteIntegral_iff_enorm.mp W.integrable.hasFiniteIntegral).ne

theorem lintegral_enorm_deriv_ne_top (W : SobolevTranslateWindow h h') :
    ∫⁻ x, ‖h' x‖ₑ ≠ ⊤ :=
  (hasFiniteIntegral_iff_enorm.mp W.integrable_deriv.hasFiniteIntegral).ne

end SobolevTranslateWindow

/-! ### The product rule for primitives -/

/-- **Product rule for primitives of locally integrable functions.**  If
`F y = F a + ∫_a^y Φ` for every `y`, with `Φ` locally integrable, then
`‖F b‖² - ‖F a‖² = ∫_a^b 2 Re (conj (F t) Φ t)`. -/
theorem normSq_sub_eq_integral_of_primitive {F Φ : ℝ → ℂ} (hΦ : LocallyIntegrable Φ volume)
    {a : ℝ} (hF : ∀ y, F y = F a + ∫ t in a..y, Φ t) (b : ℝ) :
    ‖F b‖ ^ 2 - ‖F a‖ ^ 2 = ∫ t in a..b, 2 * (conj (F t) * Φ t).re := by
  have hloc : ∀ c d, IntegrableOn Φ (uIcc c d) := fun c d =>
    hΦ.integrableOn_isCompact isCompact_uIcc
  have hii : ∀ c d, IntervalIntegrable Φ volume c d := fun c d => (hloc c d).intervalIntegrable
  have hReI : ∀ c d, IntervalIntegrable (fun t => (Φ t).re) volume c d := fun c d =>
    IntegrableOn.intervalIntegrable ((hloc c d).re)
  have hImI : ∀ c d, IntervalIntegrable (fun t => (Φ t).im) volume c d := fun c d =>
    IntegrableOn.intervalIntegrable ((hloc c d).im)
  have hRe : ∀ y, (F y).re = (F a).re + ∫ t in a..y, (Φ t).re := by
    intro y
    rw [hF y, Complex.add_re]
    congr 1
    have := (Complex.reCLM.intervalIntegral_comp_comm (hii a y)).symm
    simpa using this
  have hIm : ∀ y, (F y).im = (F a).im + ∫ t in a..y, (Φ t).im := by
    intro y
    rw [hF y, Complex.add_im]
    congr 1
    have := (Complex.imCLM.intervalIntegral_comp_comm (hii a y)).symm
    simpa using this
  have hconst : ∀ c : ℝ, AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b := fun c =>
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
  have hacRe : AbsolutelyContinuousOnInterval (fun y => (F y).re) a b := by
    have heq : (fun y => (F y).re) =
        (fun _ : ℝ => (F a).re) + fun y => ∫ t in a..y, (Φ t).re := funext hRe
    rw [heq]
    exact (hconst _).add ((hReI a b).absolutelyContinuousOnInterval_intervalIntegral
      left_mem_uIcc)
  have hacIm : AbsolutelyContinuousOnInterval (fun y => (F y).im) a b := by
    have heq : (fun y => (F y).im) =
        (fun _ : ℝ => (F a).im) + fun y => ∫ t in a..y, (Φ t).im := funext hIm
    rw [heq]
    exact (hconst _).add ((hImI a b).absolutelyContinuousOnInterval_intervalIntegral
      left_mem_uIcc)
  have hq : AbsolutelyContinuousOnInterval (fun y => ‖F y‖ ^ 2) a b := by
    have heq : (fun y => ‖F y‖ ^ 2) = (fun y => (F y).re) * (fun y => (F y).re) +
        (fun y => (F y).im) * (fun y => (F y).im) := by
      funext y
      simp only [Pi.add_apply, Pi.mul_apply, Complex.sq_norm, Complex.normSq_apply]
    rw [heq]
    exact (hacRe.mul hacRe).add (hacIm.mul hacIm)
  rw [← hq.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hΦ] with t ht _
  have hd : HasDerivAt F (Φ t) t := by
    have h1 := (ht a).const_add (F a)
    have h2 : (fun x => F a + ∫ s in a..x, Φ s) = F := funext fun y => (hF y).symm
    rwa [h2] at h1
  rw [hd.norm_sq.deriv, Complex.inner, mul_comm (Φ t)]

/-! ### The squared correlation and its derivative -/

/-- `‖f‖₂²` as a lower integral. -/
theorem lintegral_enorm_sq_eq (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ 2 = ENNReal.ofReal (‖f‖ ^ 2) := by
  have h1 : ‖f‖ ^ 2 = (∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ 2).toReal := by
    have h2 := L2.integral_inner_eq_sq_eLpNorm (𝕜 := ℂ) f
    rw [← L2.inner_def] at h2
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), h2]
    simp [enorm_eq_nnnorm]
  rw [h1, ENNReal.ofReal_toReal (lintegral_enorm_sq_ne_top f)]

private theorem lintegral_mul_le_of_sq {u v : ℝ → ℝ≥0∞} (hu : Measurable u) (hv : Measurable v)
    {A B F : ℝ≥0∞} (huF : ∫⁻ x, u x ^ 2 ≤ A ^ 2 * F) (hvF : ∫⁻ x, v x ^ 2 ≤ B ^ 2 * F) :
    ∫⁻ x, u x * v x ≤ A * B * F := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure ℝ)
    Real.HolderConjugate.two_two hu.aemeasurable hv.aemeasurable
  have hrp : ∀ w : ℝ → ℝ≥0∞, ∫⁻ x, w x ^ (2 : ℝ) = ∫⁻ x, w x ^ 2 := fun w =>
    lintegral_congr fun x => ENNReal.rpow_two (w x)
  rw [hrp, hrp] at hH
  have hsq : ∀ C : ℝ≥0∞, (C ^ 2 * F) ^ (1 / (2 : ℝ)) = C * F ^ (1 / (2 : ℝ)) := by
    intro C
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num
  have hF : F ^ (1 / (2 : ℝ)) * F ^ (1 / (2 : ℝ)) = F := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  calc ∫⁻ x, u x * v x = ∫⁻ x, (u * v) x := rfl
    _ ≤ (∫⁻ x, u x ^ 2) ^ (1 / (2 : ℝ)) * (∫⁻ x, v x ^ 2) ^ (1 / (2 : ℝ)) := hH
    _ ≤ (A ^ 2 * F) ^ (1 / (2 : ℝ)) * (B ^ 2 * F) ^ (1 / (2 : ℝ)) := by
        gcongr
    _ = A * B * F := by
        rw [hsq, hsq, mul_mul_mul_comm, hF]

namespace SobolevTranslateWindow

variable {h h' : ℝ → ℂ}

/-- The squared correlation `q_f = |g_f|²`. -/
def corrSq (W : SobolevTranslateWindow h h') (f : Lp ℂ 2 (volume : Measure ℝ)) (y : ℝ) : ℝ :=
  ‖translateCorrelation W.toL2 f y‖ ^ 2

/-- Its derivative `q_f' = 2 Re (conj g_f · G_f)`. -/
def corrSqDeriv (W : SobolevTranslateWindow h h') (f : Lp ℂ 2 (volume : Measure ℝ)) (y : ℝ) :
    ℝ :=
  2 * (conj (translateCorrelation W.toL2 f y) * W.derivCorrelation f y).re

theorem corrSq_nonneg (W : SobolevTranslateWindow h h') (f : Lp ℂ 2 (volume : Measure ℝ))
    (y : ℝ) : 0 ≤ W.corrSq f y :=
  sq_nonneg _

theorem continuous_corrSq (W : SobolevTranslateWindow h h') (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Continuous (W.corrSq f) :=
  (W.continuous_translateCorrelation f).norm.pow 2

/-- **`q_f` is the primitive of `q_f'`.** -/
theorem corrSq_sub_eq_integral (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) (a b : ℝ) :
    W.corrSq f b - W.corrSq f a = ∫ t in a..b, W.corrSqDeriv f t :=
  normSq_sub_eq_integral_of_primitive (W.locallyIntegrable_derivCorrelation f)
    (fun y => W.translateCorrelation_eq_add_integral f a y) b

theorem stronglyMeasurable_corrSqDeriv (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) : StronglyMeasurable (W.corrSqDeriv f) := by
  have hg : StronglyMeasurable (translateCorrelation W.toL2 f) :=
    (W.continuous_translateCorrelation f).stronglyMeasurable
  exact stronglyMeasurable_const.mul
    (Complex.continuous_re.comp_stronglyMeasurable
      ((continuous_star.comp_stronglyMeasurable hg).mul (W.stronglyMeasurable_derivCorrelation f)))

/-- `∫ q_f ≤ ‖h‖₁² ‖f‖₂²` in `ℝ≥0∞` form. -/
theorem lintegral_corrSq_le (W : SobolevTranslateWindow h h') (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫⁻ y, ENNReal.ofReal (W.corrSq f y) ≤
      (∫⁻ x, ‖h x‖ₑ) ^ 2 * ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ 2 := by
  refine le_trans (le_of_eq (lintegral_congr fun y => ?_))
    (W.lintegral_translateCorrelation_sq_le f)
  rw [corrSq, ← enorm_pow, ← ofReal_norm, norm_pow]

/-- `‖q_f'‖₁ ≤ 2 ‖h‖₁ ‖h'‖₁ ‖f‖₂²` in `ℝ≥0∞` form. -/
theorem lintegral_enorm_corrSqDeriv_le (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫⁻ y, ‖W.corrSqDeriv f y‖ₑ ≤
      2 * ((∫⁻ x, ‖h x‖ₑ) * (∫⁻ x, ‖h' x‖ₑ) * ∫⁻ x, ‖(f : ℝ → ℂ) x‖ₑ ^ 2) := by
  have hpt : ∀ y, ‖W.corrSqDeriv f y‖ₑ ≤
      2 * (‖translateCorrelation W.toL2 f y‖ₑ * ‖W.derivCorrelation f y‖ₑ) := by
    intro y
    rw [corrSqDeriv, enorm_mul]
    have h2 : ‖(2 : ℝ)‖ₑ = 2 := by
      rw [Real.enorm_eq_ofReal_abs, abs_two, ENNReal.ofReal_ofNat]
    rw [h2]
    gcongr
    refine (enorm_le_iff_norm_le.mpr (Complex.abs_re_le_norm _)).trans ?_
    rw [enorm_mul, RCLike.enorm_conj]
  have hmeas_g : Measurable fun y => ‖translateCorrelation W.toL2 f y‖ₑ :=
    (W.continuous_translateCorrelation f).measurable.enorm
  have hmeas_G : Measurable fun y => ‖W.derivCorrelation f y‖ₑ :=
    (W.stronglyMeasurable_derivCorrelation f).measurable.enorm
  calc ∫⁻ y, ‖W.corrSqDeriv f y‖ₑ
      ≤ ∫⁻ y, 2 * (‖translateCorrelation W.toL2 f y‖ₑ * ‖W.derivCorrelation f y‖ₑ) :=
        lintegral_mono hpt
    _ = 2 * ∫⁻ y, ‖translateCorrelation W.toL2 f y‖ₑ * ‖W.derivCorrelation f y‖ₑ :=
        lintegral_const_mul _ (hmeas_g.mul hmeas_G)
    _ ≤ _ := by
        gcongr
        exact lintegral_mul_le_of_sq hmeas_g hmeas_G (W.lintegral_translateCorrelation_sq_le f)
          (W.lintegral_derivCorrelation_sq_le f)

theorem integrable_corrSq (W : SobolevTranslateWindow h h') (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable (W.corrSq f) := by
  refine ⟨(W.continuous_corrSq f).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (.of_forall (W.corrSq_nonneg f))]
  refine lt_of_le_of_lt (W.lintegral_corrSq_le f) (ENNReal.mul_lt_top ?_ ?_)
  · exact ENNReal.pow_lt_top W.lintegral_enorm_ne_top.lt_top
  · exact (lintegral_enorm_sq_ne_top f).lt_top

theorem integrable_corrSqDeriv (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) : Integrable (W.corrSqDeriv f) := by
  refine ⟨(W.stronglyMeasurable_corrSqDeriv f).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt (W.lintegral_enorm_corrSqDeriv_le f) (ENNReal.mul_lt_top (by simp) ?_)
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top W.lintegral_enorm_ne_top.lt_top
    W.lintegral_enorm_deriv_ne_top.lt_top) (lintegral_enorm_sq_ne_top f).lt_top

/-- `‖q_f'‖₁ ≤ 2 ‖h‖₁ ‖h'‖₁ ‖f‖₂²`. -/
theorem integral_norm_corrSqDeriv_le (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫ y, ‖W.corrSqDeriv f y‖ ≤ 2 * ((∫ x, ‖h x‖) * (∫ x, ‖h' x‖) * ‖f‖ ^ 2) := by
  have e1 := (ofReal_integral_norm_eq_lintegral_enorm W.integrable).symm
  have e2 := (ofReal_integral_norm_eq_lintegral_enorm W.integrable_deriv).symm
  have e3 := lintegral_enorm_sq_eq f
  have e4 := ofReal_integral_norm_eq_lintegral_enorm (W.integrable_corrSqDeriv f)
  have hA : 0 ≤ ∫ x, ‖h x‖ := integral_nonneg fun _ => norm_nonneg _
  have hB : 0 ≤ ∫ x, ‖h' x‖ := integral_nonneg fun _ => norm_nonneg _
  have key : ENNReal.ofReal (∫ y, ‖W.corrSqDeriv f y‖) ≤
      ENNReal.ofReal (2 * ((∫ x, ‖h x‖) * (∫ x, ‖h' x‖) * ‖f‖ ^ 2)) := by
    rw [e4]
    refine (W.lintegral_enorm_corrSqDeriv_le f).trans (le_of_eq ?_)
    rw [e1, e2, e3, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul hA, ENNReal.ofReal_ofNat]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp key

/-- `q_f → 0` at `+∞`. -/
theorem tendsto_corrSq_atTop (W : SobolevTranslateWindow h h')
    (f : Lp ℂ 2 (volume : Measure ℝ)) : Tendsto (W.corrSq f) atTop (𝓝 0) := by
  have hlim : Tendsto (fun b => ∫ t in (0 : ℝ)..b, W.corrSqDeriv f t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), W.corrSqDeriv f t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (W.integrable_corrSqDeriv f).integrableOn tendsto_id
  set L := W.corrSq f 0 + ∫ t in Ioi (0 : ℝ), W.corrSqDeriv f t
  have hq : Tendsto (W.corrSq f) atTop (𝓝 L) := by
    have := hlim.const_add (W.corrSq f 0)
    refine this.congr fun b => ?_
    have := W.corrSq_sub_eq_integral f 0 b
    linarith
  suffices hL : L = 0 by rwa [hL] at hq
  by_contra hL
  have hLpos : 0 < L := lt_of_le_of_ne (ge_of_tendsto' hq (W.corrSq_nonneg f)) (Ne.symm hL)
  obtain ⟨T, hT⟩ := (eventually_ge_atTop (0 : ℝ)).and
    (hq.eventually (lt_mem_nhds (half_lt_self hLpos))) |>.exists_forall_of_atTop
  have hint := (W.integrable_corrSq f).integrableOn (s := Ici T)
  have hinf : ∫⁻ y in Ici T, ENNReal.ofReal (W.corrSq f y) = ⊤ := by
    refine top_unique ?_
    calc (⊤ : ℝ≥0∞) = ∫⁻ _ in Ici T, ENNReal.ofReal (L / 2) := by
          rw [setLIntegral_const, Real.volume_Ici, ENNReal.mul_top]
          exact (ENNReal.ofReal_pos.mpr (half_pos hLpos)).ne'
      _ ≤ ∫⁻ y in Ici T, ENNReal.ofReal (W.corrSq f y) :=
          setLIntegral_mono (W.continuous_corrSq f).measurable.ennreal_ofReal
            fun y hy => ENNReal.ofReal_le_ofReal (hT y hy).2.le
  have hfin := (hasFiniteIntegral_iff_ofReal (.of_forall (W.corrSq_nonneg f))).mp
    hint.hasFiniteIntegral
  exact absurd hinf hfin.ne

end SobolevTranslateWindow

/-! ### Stieltjes comparison on the future half-line -/

/-- **Integration by parts against a distribution function on a window.**  If
`q y = q R - ∫_y^R φ` on `[0, R]`, then
`∫_{[0,R]} q dμ = q R · μ[0,R] - ∫_{[0,R]} φ(s) μ[0,s] ds`. -/
theorem setIntegral_Icc_eq_of_primitive (μ : Measure ℝ) {R : ℝ}
    (hμ : μ (Icc 0 R) ≠ ⊤) {q φ : ℝ → ℝ} (hφ : IntegrableOn φ (Icc 0 R))
    (hq : ∀ y ∈ Icc (0 : ℝ) R, q y = q R - ∫ s in y..R, φ s) :
    ∫ y in Icc 0 R, q y ∂μ =
      q R * μ.real (Icc 0 R) - ∫ s in Icc 0 R, φ s * μ.real (Icc 0 s) := by
  haveI : IsFiniteMeasure (μ.restrict (Icc 0 R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμ.lt_top⟩
  set F : ℝ → ℝ → ℝ := fun y s => (Ici y).indicator φ s
  have hmeasS : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
    measurableSet_le measurable_fst measurable_snd
  have hFeq : Function.uncurry F = {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun p => φ p.2) := by
    funext ⟨y, t⟩
    show (Ici y).indicator φ t = _
    by_cases hyt : y ≤ t <;> simp [hyt]
  have hFint : Integrable (Function.uncurry F)
      ((μ.restrict (Icc 0 R)).prod (volume.restrict (Icc 0 R))) := by
    rw [hFeq]
    exact (Integrable.comp_snd hφ (μ.restrict (Icc 0 R))).indicator hmeasS
  have hI : ∀ y ∈ Icc (0 : ℝ) R, ∫ s in y..R, φ s = ∫ s in Icc 0 R, F y s := by
    intro y hy
    have hset : Icc 0 R ∩ Ici y = Icc y R := by
      ext s
      simp only [mem_Icc, mem_inter_iff, mem_Ici]
      constructor
      · rintro ⟨⟨_, h2⟩, h1⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨hy.1.trans h1, h2⟩, h1⟩
    rw [intervalIntegral.integral_of_le hy.2, ← integral_Icc_eq_integral_Ioc,
      setIntegral_indicator measurableSet_Ici, hset]
  have hJ : ∀ s ∈ Icc (0 : ℝ) R, ∫ y in Icc 0 R, F y s ∂μ = φ s * μ.real (Icc 0 s) := by
    intro s hs
    have hpt : ∀ y, F y s = (Iic s).indicator (fun _ => φ s) y := by
      intro y
      simp only [F, Set.indicator, mem_Ici, mem_Iic]
    simp_rw [hpt]
    rw [setIntegral_indicator measurableSet_Iic, setIntegral_const, smul_eq_mul, mul_comm]
    congr 2
    ext y
    simp only [mem_Icc, mem_inter_iff, mem_Iic]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, h3.trans hs.2⟩, h3⟩
  calc ∫ y in Icc 0 R, q y ∂μ = ∫ y in Icc 0 R, (q R - ∫ s in Icc 0 R, F y s) ∂μ :=
        setIntegral_congr_fun measurableSet_Icc fun y hy => by rw [hq y hy, hI y hy]
    _ = q R * μ.real (Icc 0 R) - ∫ y in Icc 0 R, (∫ s in Icc 0 R, F y s) ∂μ := by
        have hint : Integrable (fun y => ∫ s in Icc 0 R, F y s) (μ.restrict (Icc 0 R)) :=
          hFint.integral_prod_left
        rw [integral_sub (integrable_const _) hint, setIntegral_const, smul_eq_mul, mul_comm]
    _ = q R * μ.real (Icc 0 R) - ∫ s in Icc 0 R, ∫ y in Icc 0 R, F y s ∂μ := by
        rw [integral_integral_swap hFint]
    _ = _ := by
        congr 1
        exact setIntegral_congr_fun measurableSet_Icc hJ

/-- The cumulative distribution function `s ↦ μ[0, s]` of a measure finite on bounded windows is
monotone, hence measurable. -/
theorem monotone_measureReal_Icc (μ : Measure ℝ) (hμ : ∀ R, μ (Icc 0 R) ≠ ⊤) :
    Monotone fun s : ℝ => μ.real (Icc 0 s) := by
  intro a b hab
  exact measureReal_mono (Icc_subset_Icc_right hab) (hμ b)

/-- **Stieltjes comparison on the future half-line.**  Let `μ, ν` be finite on bounded windows of
`[0, ∞)` with cumulative discrepancy `|μ[0, y] - ν[0, y]| ≤ ε`, and let `q ≥ 0` be continuous,
`ν`-integrable on `[0, ∞)`, tending to zero, with a Lebesgue-integrable derivative `φ` in the
primitive sense.  Then `q` is `μ`-integrable on `[0, ∞)` and
`|∫_{[0,∞)} q dμ - ∫_{[0,∞)} q dν| ≤ ε ∫_0^∞ |φ|`. -/
theorem abs_setIntegral_Ici_sub_le (μ ν : Measure ℝ) (hμ : ∀ R, μ (Icc 0 R) ≠ ⊤)
    (hν : ∀ R, ν (Icc 0 R) ≠ ⊤) {ε : ℝ}
    (hD : ∀ y, 0 ≤ y → |μ.real (Icc 0 y) - ν.real (Icc 0 y)| ≤ ε)
    {q φ : ℝ → ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqc : Continuous q) (hqint : IntegrableOn q (Ici 0) ν)
    (hφ : IntegrableOn φ (Ici 0)) (hprim : ∀ a b, q b - q a = ∫ s in a..b, φ s)
    (hqlim : Tendsto q atTop (𝓝 0)) :
    IntegrableOn q (Ici 0) μ ∧
      |∫ y in Ici 0, q y ∂μ - ∫ y in Ici 0, q y ∂ν| ≤ ε * ∫ s in Ici 0, |φ s| := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hD 0 le_rfl)
  set C := ∫ s in Ici (0 : ℝ), |φ s|
  have hwin : ∀ ρ : Measure ℝ, (∀ R, ρ (Icc 0 R) ≠ ⊤) → ∀ R,
      ∫ y in Icc 0 R, q y ∂ρ =
        q R * ρ.real (Icc 0 R) - ∫ s in Icc 0 R, φ s * ρ.real (Icc 0 s) := by
    intro ρ hρ R
    refine setIntegral_Icc_eq_of_primitive ρ (hρ R) (hφ.mono_set Icc_subset_Ici_self)
      fun y _ => ?_
    have := hprim y R
    linarith
  have hφR : ∀ R, IntegrableOn φ (Icc 0 R) := fun R => hφ.mono_set Icc_subset_Ici_self
  have hwt : ∀ ρ : Measure ℝ, (∀ R, ρ (Icc 0 R) ≠ ⊤) → ∀ R,
      IntegrableOn (fun s => φ s * ρ.real (Icc 0 s)) (Icc 0 R) := by
    intro ρ hρ R
    refine (hφR R).mul_bdd (c := ρ.real (Icc 0 R))
      (monotone_measureReal_Icc ρ hρ).measurable.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).mpr (.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact monotone_measureReal_Icc ρ hρ hs.2
  have hdiff : ∀ R, 0 ≤ R →
      |∫ y in Icc 0 R, q y ∂μ - ∫ y in Icc 0 R, q y ∂ν| ≤ ε * (q R + C) := by
    intro R hR
    rw [hwin μ hμ R, hwin ν hν R]
    have hsplit : (q R * μ.real (Icc 0 R) - ∫ s in Icc 0 R, φ s * μ.real (Icc 0 s)) -
        (q R * ν.real (Icc 0 R) - ∫ s in Icc 0 R, φ s * ν.real (Icc 0 s)) =
        q R * (μ.real (Icc 0 R) - ν.real (Icc 0 R)) -
          ∫ s in Icc 0 R, φ s * (μ.real (Icc 0 s) - ν.real (Icc 0 s)) := by
      have hfun : (fun s => φ s * (μ.real (Icc 0 s) - ν.real (Icc 0 s))) =
          fun s => φ s * μ.real (Icc 0 s) - φ s * ν.real (Icc 0 s) := by
        funext s
        ring
      rw [hfun, integral_sub (hwt μ hμ R) (hwt ν hν R)]
      ring
    rw [hsplit]
    have hint_bound : ‖∫ s in Icc 0 R, φ s * (μ.real (Icc 0 s) - ν.real (Icc 0 s))‖ ≤
        ε * C := by
      calc ‖∫ s in Icc 0 R, φ s * (μ.real (Icc 0 s) - ν.real (Icc 0 s))‖
          ≤ ∫ s in Icc 0 R, ‖φ s * (μ.real (Icc 0 s) - ν.real (Icc 0 s))‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ s in Icc 0 R, ε * |φ s| := by
            refine setIntegral_mono_on ((hwt μ hμ R).sub (hwt ν hν R) |>.norm.congr ?_)
              ((hφR R).norm.const_mul ε) measurableSet_Icc fun s hs => ?_
            · exact .of_forall fun s => by simp only [Pi.sub_apply, mul_sub]
            · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
              gcongr
              exact hD s hs.1
        _ = ε * ∫ s in Icc 0 R, |φ s| := integral_const_mul _ _
        _ ≤ ε * C := by
            gcongr
            exact setIntegral_mono_set hφ.norm (.of_forall fun _ => abs_nonneg _)
              (Icc_subset_Ici_self.eventuallyLE)
    calc |q R * (μ.real (Icc 0 R) - ν.real (Icc 0 R)) -
          ∫ s in Icc 0 R, φ s * (μ.real (Icc 0 s) - ν.real (Icc 0 s))|
        ≤ |q R * (μ.real (Icc 0 R) - ν.real (Icc 0 R))| +
          ‖∫ s in Icc 0 R, φ s * (μ.real (Icc 0 s) - ν.real (Icc 0 s))‖ :=
          abs_sub _ _
      _ ≤ q R * ε + ε * C := by
          gcongr
          rw [abs_mul, abs_of_nonneg (hq0 R)]
          exact mul_le_mul_of_nonneg_left (hD R hR) (hq0 R)
      _ = ε * (q R + C) := by ring
  have hqR : ∀ R, IntegrableOn q (Icc 0 R) μ := by
    intro R
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_bound_of_continuousOn
      hqc.continuousOn
    exact Measure.integrableOn_of_bounded (M := M) (hμ R) hqc.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Icc).mpr (.of_forall hM))
  obtain ⟨B, hB⟩ : ∃ B, ∀ n : ℕ, q n ≤ B := by
    obtain ⟨B, hB⟩ := (hqlim.comp tendsto_natCast_atTop_atTop).bddAbove_range
    exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  have hwinμ : ∀ n : ℕ,
      ∫ y in Icc 0 (n : ℝ), q y ∂μ ≤ (∫ y in Ici 0, q y ∂ν) + ε * (B + C) := by
    intro n
    have h1 := (abs_le.mp (hdiff n (Nat.cast_nonneg n))).2
    have h2 : ∫ y in Icc 0 (n : ℝ), q y ∂ν ≤ ∫ y in Ici 0, q y ∂ν :=
      setIntegral_mono_set hqint (.of_forall fun y => hq0 y) Icc_subset_Ici_self.eventuallyLE
    have h3 : ε * (q n + C) ≤ ε * (B + C) := by gcongr; exact hB n
    linarith
  have hunion : (⋃ n : ℕ, Icc (0 : ℝ) n) = Ici 0 := by
    ext y
    simp only [mem_iUnion, mem_Icc, mem_Ici]
    constructor
    · rintro ⟨n, h, _⟩
      exact h
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_ge y
      exact ⟨n, hy, hn⟩
  have hintμ : IntegrableOn q (Ici 0) μ := by
    refine ⟨hqc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal ((ae_restrict_iff' measurableSet_Ici).mpr
      (.of_forall fun y _ => hq0 y)), ← hunion,
      setLIntegral_iUnion_of_directed _ (Monotone.directed_le fun a b hab =>
        Icc_subset_Icc_right (by exact_mod_cast hab))]
    refine lt_of_le_of_lt (iSup_le fun n => ?_)
      (ENNReal.ofReal_lt_top (r := (∫ y in Ici 0, q y ∂ν) + ε * (B + C)))
    rw [← ofReal_integral_eq_lintegral_ofReal (hqR n)
      ((ae_restrict_iff' measurableSet_Icc).mpr (.of_forall fun y _ => hq0 y))]
    exact ENNReal.ofReal_le_ofReal (hwinμ n)
  refine ⟨hintμ, ?_⟩
  have hmono : Monotone fun R : ℝ => Icc (0 : ℝ) R := fun a b hab => Icc_subset_Icc_right hab
  have hlimμ := tendsto_setIntegral_of_monotone (μ := μ) (f := q)
    (fun R => measurableSet_Icc) hmono (by rwa [iUnion_Icc_right])
  have hlimν := tendsto_setIntegral_of_monotone (μ := ν) (f := q)
    (fun R => measurableSet_Icc) hmono (by rwa [iUnion_Icc_right])
  rw [iUnion_Icc_right] at hlimμ hlimν
  have hlim := (hlimμ.sub hlimν).abs
  have hbound := (hqlim.const_add C).const_mul ε
  rw [add_zero] at hbound
  refine le_of_tendsto_of_tendsto hlim hbound ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  rw [add_comm C]
  exact hdiff R hR

/-- The scaled Lebesgue measure `κ · dy` has cumulative function `κ y` on `[0, ∞)`. -/
theorem measureReal_smul_volume_Icc {κ : ℝ} (hκ : 0 ≤ κ) {y : ℝ} (hy : 0 ≤ y) :
    (ENNReal.ofReal κ • (volume : Measure ℝ)).real (Icc 0 y) = κ * y := by
  rw [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hκ, ← measureReal_def, Real.volume_real_Icc_of_le hy, sub_zero]

theorem smul_volume_Icc_ne_top (κ : ℝ) (R : ℝ) :
    (ENNReal.ofReal κ • (volume : Measure ℝ)) (Icc 0 R) ≠ ⊤ := by
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_Icc_lt_top.ne

end GaloisForLFunctions.HTGeometry

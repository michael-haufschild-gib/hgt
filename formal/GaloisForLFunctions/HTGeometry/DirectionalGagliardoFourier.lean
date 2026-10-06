import GaloisForLFunctions.HTGeometry.GagliardoFourierConstant

/-!
# Directional fractional energy of Euclidean Schwartz functions

The corpus scalar Gagliardo constant extends to every signed frequency.
Schwartz Plancherel identifies each translation difference, and nonnegative
Tonelli exchanges the shift and frequency variables without circular
integrability assumptions. A polynomial Schwartz majorant admits the full
spectral integral. The resulting constant is strictly positive.

This is the fractional-energy bridge for the localized logarithmic BAG
transfer. It does not assert the change-of-coordinates bound itself.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology ContDiff
namespace GaloisForLFunctions.HTGeometry

private def directionalConstant (s : ℝ) : ℝ := ∫h in Ioi (0 : ℝ), gagliardoIntegrand s h

private theorem directional_constant_pos (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) :
    0<directionalConstant s.1 := by
  have hi := integrableOn_gagliardoIntegrand_Ioi_zero s.2.1 s.2.2
  have hn : ∀ᵐ h : ℝ ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ gagliardoIntegrand s.1 h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    exact gagliardoIntegrand_nonneg hh
  apply (integral_pos_iff_support_of_nonneg_ae hn hi).mpr
  have hs : Ioo (0 : ℝ) 1⊆Function.support (gagliardoIntegrand s.1) := by
    intro h hh
    exact (gagliardoIntegrand_pos hh.1 hh.2).ne'
  have hm : 0<(volume.restrict (Ioi (0 : ℝ))) (Ioo (0 : ℝ) 1) := by
    rw [Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr (show Ioo (0 : ℝ) 1⊆Ioi (0 : ℝ) from fun h hh => hh.1)]
    norm_num
  exact hm.trans_le (measure_mono hs)

private theorem difference_symbol_sq_abs (h ξ : ℝ) :
    ‖differenceSymbol h ξ‖^2=‖differenceSymbol h |ξ|‖^2 := by
  rw [normSq_differenceSymbol,normSq_differenceSymbol]
  by_cases hξ : 0 ≤ ξ
  · rw [abs_of_nonneg hξ]
  · rw [abs_of_neg (lt_of_not_ge hξ),mul_neg,mul_neg,Real.sin_neg,neg_sq]

private theorem directional_symbol_integrable
    (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) (ξ : ℝ) :
    IntegrableOn (fun h : ℝ => ‖differenceSymbol h ξ‖^2*h^(-(1+2*s.1))) (Ioi (0 : ℝ)) := by
  by_cases hξ : ξ=0
  · simp [hξ,differenceSymbol]
  have hξp : 0 < |ξ| := abs_pos.mpr hξ
  have hi := integrableOn_gagliardoIntegrand_Ioi_zero s.2.1 s.2.2
  have hg : IntegrableOn (fun h : ℝ => gagliardoIntegrand s.1 (|ξ| * h)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff (gagliardoIntegrand s.1) 0 hξp).mpr
    simpa only [mul_zero] using hi
  refine (hg.const_mul (|ξ|^(1+2*s.1))).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  rw [difference_symbol_sq_abs,normSq_differenceSymbol,mul_comm h |ξ|]
  exact (gagliardoIntegrand_scaling hξp hh).symm

private theorem directional_symbol_integral
    (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) (ξ : ℝ) :
    (∫h in Ioi (0 : ℝ), ‖differenceSymbol h ξ‖^2*h^(-(1+2*s.1)))=
      |ξ|^(2*s.1)*directionalConstant s.1 := by
  by_cases hξ : ξ=0
  · have hs : (2 : ℝ)*s.1≠0 := mul_ne_zero (by norm_num) s.2.1.ne'
    simp [hξ,differenceSymbol,Real.zero_rpow hs]
  · have he : (fun h : ℝ => ‖differenceSymbol h ξ‖^2*h^(-(1+2*s.1)))=
        (fun h : ℝ => ‖differenceSymbol h |ξ|‖^2*h^(-(1+2*s.1))) := by
      funext h
      rw [difference_symbol_sq_abs]
    rw [he]
    exact integral_normSq_differenceSymbol (abs_pos.mpr hξ)

private theorem directional_symbol_lintegral
    (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) (ξ : ℝ) :
    (∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal (‖differenceSymbol h ξ‖^2*h^(-(1+2*s.1))))=
      ENNReal.ofReal (directionalConstant s.1)*ENNReal.ofReal (|ξ|^(2*s.1)) := by
  rw [←ofReal_integral_eq_lintegral_ofReal (directional_symbol_integrable s ξ)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      exact mul_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos hh _).le),
    directional_symbol_integral,ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _),mul_comm]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private def directionalDifference (f : SchwartzMap E ℂ) (v : E) (h : ℝ) : SchwartzMap E ℂ :=
  f-f.compSubConstCLM ℂ (-(h • v))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem directional_difference_apply (f : SchwartzMap E ℂ) (v x : E) (h : ℝ) :
    directionalDifference f v h x=f x-f (x+h • v) := by
  simp only [directionalDifference,sub_apply,SchwartzMap.compSubConstCLM_apply,sub_neg_eq_add]

private theorem directional_translate_fourier (f : SchwartzMap E ℂ) (v ξ : E) (h : ℝ) :
    (𝓕 (f.compSubConstCLM ℂ (-(h • v)))) ξ=
      ((Real.fourierChar (h*inner ℝ v ξ) : Circle) : ℂ)*(𝓕 f) ξ := by
  have hh := congrFun (VectorFourier.fourierIntegral_comp_add_right
    (V := E) (W := E) (E := ℂ) Real.fourierChar volume (innerₗ E) (f : E→ℂ) (h • v)) ξ
  have he : ((innerₗ E) (h • v)) ξ=h*inner ℝ v ξ := by
    change inner ℝ (h • v) ξ=h*inner ℝ v ξ
    rw [real_inner_smul_left]
  rw [he,Circle.smul_def,smul_eq_mul] at hh
  change 𝓕 (fun x : E => f (x-(-(h • v)))) ξ= _
  simpa only [sub_neg_eq_add,Function.comp_def] using! hh

private theorem directional_difference_fourier (f : SchwartzMap E ℂ) (v ξ : E) (h : ℝ) :
    (𝓕 (directionalDifference f v h)) ξ=differenceSymbol h (inner ℝ v ξ)*(𝓕 f) ξ := by
  change (SchwartzMap.fourierTransformCLM ℂ (f-f.compSubConstCLM ℂ (-(h • v)))) ξ= _
  rw [map_sub,sub_apply]
  change (𝓕 f) ξ-(𝓕 (f.compSubConstCLM ℂ (-(h • v)))) ξ= _
  rw [directional_translate_fourier]
  unfold differenceSymbol
  ring

private theorem directional_difference_plancherel (f : SchwartzMap E ℂ) (v : E) (h : ℝ) :
    (∫x : E, ‖f x-f (x+h • v)‖^2)=
      ∫ξ : E, ‖differenceSymbol h (inner ℝ v ξ)‖^2*‖(𝓕 f) ξ‖^2 := by
  have hh := (SchwartzMap.integral_norm_sq_fourier (directionalDifference f v h)).symm
  simp_rw [directional_difference_apply,directional_difference_fourier,norm_mul,mul_pow] at hh
  exact hh

private theorem directional_difference_lintegral (f : SchwartzMap E ℂ) (v : E)
    (s : ℝ) (h : {r : ℝ // 0<r}) :
    (∫⁻ x : E, ENNReal.ofReal (‖f x-f (x+h.1 • v)‖^2*h.1^(-(1+2*s))))=
      ∫⁻ ξ : E, ENNReal.ofReal (‖differenceSymbol h.1 (inner ℝ v ξ)‖^2*
        h.1^(-(1+2*s))*‖(𝓕 f) ξ‖^2) := by
  have hi : Integrable (fun x : E => ‖f x-f (x+h.1 • v)‖^2) := by
    have hh := ((directionalDifference f v h.1).memLp 2).integrable_norm_pow (by norm_num : 2≠0)
    simpa only [directional_difference_apply] using hh
  have hj : Integrable (fun ξ : E => ‖differenceSymbol h.1 (inner ℝ v ξ)‖^2*‖(𝓕 f) ξ‖^2) := by
    have hh := ((𝓕 (directionalDifference f v h.1)).memLp 2).integrable_norm_pow (by norm_num : 2≠0)
    simpa only [directional_difference_fourier,norm_mul,mul_pow] using hh
  have hj' : Integrable (fun ξ : E => ‖differenceSymbol h.1 (inner ℝ v ξ)‖^2*
      h.1^(-(1+2*s))*‖(𝓕 f) ξ‖^2) := by
    convert! hj.mul_const (h.1^(-(1+2*s))) using 1
    funext ξ
    ring
  rw [←ofReal_integral_eq_lintegral_ofReal (hi.mul_const _) (Eventually.of_forall (fun x =>
      mul_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos h.2 _).le)),
    ←ofReal_integral_eq_lintegral_ofReal hj' (Eventually.of_forall (fun ξ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos h.2 _).le) (sq_nonneg _)))]
  congr 1
  rw [integral_mul_const,directional_difference_plancherel,←integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with ξ
  ring

private theorem directional_gagliardo_lintegral (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (f : SchwartzMap E ℂ) (v : E) :
    (∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : E,
      ENNReal.ofReal (‖f x-f (x+h • v)‖^2*h^(-(1+2*s.1))))=
      ENNReal.ofReal (directionalConstant s.1)*
        ∫⁻ ξ : E, ENNReal.ofReal (|inner ℝ v ξ|^(2*s.1)*‖(𝓕 f) ξ‖^2) := by
  have he : (∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : E,
      ENNReal.ofReal (‖f x-f (x+h • v)‖^2*h^(-(1+2*s.1))))=
      ∫⁻ h in Ioi (0 : ℝ), ∫⁻ ξ : E,
        ENNReal.ofReal (‖differenceSymbol h (inner ℝ v ξ)‖^2*h^(-(1+2*s.1))*‖(𝓕 f) ξ‖^2) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    exact directional_difference_lintegral f v s.1 ⟨h,hh⟩
  have hm : Measurable (fun z : ℝ×E =>
      ENNReal.ofReal (‖differenceSymbol z.1 (inner ℝ v z.2)‖^2*
        z.1^(-(1+2*s.1))*‖(𝓕 f) z.2‖^2)) := by
    have hf := (𝓕 f).continuous.measurable
    unfold differenceSymbol
    fun_prop
  rw [he,lintegral_lintegral_swap hm.aemeasurable]
  have hi (ξ : E) : (∫⁻ h in Ioi (0 : ℝ),
      ENNReal.ofReal (‖differenceSymbol h (inner ℝ v ξ)‖^2*h^(-(1+2*s.1))*‖(𝓕 f) ξ‖^2))=
      ENNReal.ofReal (directionalConstant s.1)*
        ENNReal.ofReal (|inner ℝ v ξ|^(2*s.1)*‖(𝓕 f) ξ‖^2) := by
    have hp (h : ℝ) :
        ENNReal.ofReal (‖differenceSymbol h (inner ℝ v ξ)‖^2*h^(-(1+2*s.1))*‖(𝓕 f) ξ‖^2)=
        ENNReal.ofReal (‖differenceSymbol h (inner ℝ v ξ)‖^2*h^(-(1+2*s.1)))*
          ENNReal.ofReal (‖(𝓕 f) ξ‖^2) := by
      exact ENNReal.ofReal_mul' (sq_nonneg _)
    simp_rw [hp]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,directional_symbol_lintegral,
      ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _),mul_assoc]
  simp_rw [hi]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem directional_weight_bound (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) (v ξ : E) :
    |inner ℝ v ξ|^(2*s.1) ≤ 1+‖v‖^2*‖ξ‖^2 := by
  have hb : |inner ℝ v ξ| ≤ ‖v‖*‖ξ‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) v ξ
  have hb2 := pow_le_pow_left₀ (abs_nonneg (inner ℝ v ξ)) hb 2
  rw [mul_pow] at hb2
  by_cases hsmall : |inner ℝ v ξ| ≤ 1
  · have hh := Real.rpow_le_one (abs_nonneg (inner ℝ v ξ)) hsmall
      (show 0 ≤ 2*s.1 by linarith [s.2.1])
    exact hh.trans (le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  · calc |inner ℝ v ξ|^(2*s.1) ≤ |inner ℝ v ξ|^(2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hsmall) (by linarith [s.2.2])
      _ = |inner ℝ v ξ|^2 := Real.rpow_two _
      _ ≤ 1+‖v‖^2*‖ξ‖^2 := by linarith only [hb2]

private theorem directional_spectral_integrable
    (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) (f : SchwartzMap E ℂ) (v : E) :
    Integrable (fun ξ : E => |inner ℝ v ξ|^(2*s.1)*‖(𝓕 f) ξ‖^2) := by
  let g := 𝓕 f
  obtain ⟨C,hC,hCb⟩ := g.decay 0 0
  have hg (ξ : E) : ‖g ξ‖ ≤ C := by
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero] using hCb ξ
  have hi : Integrable (fun ξ : E => C*(‖g ξ‖+‖v‖^2*(‖ξ‖^2*‖g ξ‖))) :=
    (g.integrable.norm.add ((g.integrable_pow_mul volume 2).const_mul (‖v‖^2))).const_mul C
  refine hi.mono' ?_ (Eventually.of_forall (fun ξ => ?_))
  · have hf := g.continuous.measurable
    apply Measurable.aestronglyMeasurable
    change Measurable (fun ξ : E => |inner ℝ v ξ|^(2*s.1)*‖g ξ‖^2)
    fun_prop
  · rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _))]
    change |inner ℝ v ξ|^(2*s.1)*‖g ξ‖^2 ≤ _
    have hsq : ‖g ξ‖^2 ≤ C*‖g ξ‖ := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hg ξ) (norm_nonneg _)
    calc |inner ℝ v ξ|^(2*s.1)*‖g ξ‖^2
        ≤ (1+‖v‖^2*‖ξ‖^2)*‖g ξ‖^2 :=
          mul_le_mul_of_nonneg_right (directional_weight_bound s v ξ) (sq_nonneg _)
      _ ≤ (1+‖v‖^2*‖ξ‖^2)*(C*‖g ξ‖) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by ring

/-- Exact directional fractional energy of every Euclidean Schwartz function.
The spectral integral is admitted and the constant is strictly positive. -/
theorem directional_gagliardo_fourier (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) :
    ∃ C : ℝ, 0<C ∧ ∀(f : SchwartzMap E ℂ) (v : E),
      Integrable (fun ξ : E => |inner ℝ v ξ|^(2*s.1)*‖(𝓕 f) ξ‖^2) ∧
      (∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : E,
        ENNReal.ofReal (‖f x-f (x+h • v)‖^2*h^(-(1+2*s.1))))=
        ENNReal.ofReal C*ENNReal.ofReal
          (∫ξ : E, |inner ℝ v ξ|^(2*s.1)*‖(𝓕 f) ξ‖^2) := by
  refine ⟨directionalConstant s.1,directional_constant_pos s,fun f v => ?_⟩
  have hi := directional_spectral_integrable s f v
  refine ⟨hi,?_⟩
  rw [directional_gagliardo_lintegral,←ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun ξ => mul_nonneg
      (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)))]

end GaloisForLFunctions.HTGeometry

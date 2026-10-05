import GaloisForLFunctions.HTGeometry.YoungConvolutionL2

/-!
# Young's convolution inequality `L¹ ⋆ Lᵖ → Lᵖ` for every `1 ≤ p ≤ ∞`

For `K, G ≥ 0` and a real exponent `p ≥ 1`, Hölder's inequality against the weight `K` gives
`(∫ K G)^p ≤ (∫ K)^{p-1} ∫ K G^p`; integrating this in the translation variable and using Tonelli
and translation invariance gives `∫ (K ⋆ G)^p ≤ (∫ K)^p ∫ G^p`.  For a measurable kernel `k` and any
`f` this is `‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p`; the case `p = ∞` is the pointwise bound by `‖k‖₁ ‖f‖_∞`.
-/

open MeasureTheory ENNReal Filter

namespace GaloisForLFunctions.HTGeometry

/-- **Hölder against a weight.**  For `p ≥ 1`, `(∫ K G)^p ≤ (∫ K)^{p-1} ∫ K G^p`. -/
theorem lintegral_weighted_rpow_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {K G : α → ℝ≥0∞} (hK : AEMeasurable K μ) (hG : AEMeasurable G μ) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ y, K y * G y ∂μ) ^ p ≤ (∫⁻ y, K y ∂μ) ^ (p - 1) * ∫⁻ y, K y * G y ^ p ∂μ := by
  rcases eq_or_lt_of_le hp with rfl | hp1
  · simp
  set q := p.conjExponent
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := hpq.symm.pos
  have hsplit : ∀ y, K y * G y = K y ^ (1 / q) * (K y ^ (1 / p) * G y) := fun y => by
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity),
      show 1 / q + 1 / p = 1 by rw [one_div, one_div, add_comm]; exact hpq.inv_add_inv_eq_one,
      ENNReal.rpow_one]
  have hf : AEMeasurable (fun y => K y ^ (1 / q)) μ := hK.pow_const _
  have hg : AEMeasurable (fun y => K y ^ (1 / p) * G y) μ := (hK.pow_const _).mul hG
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq.symm hf hg
  have hA : ∫⁻ y, (K y ^ (1 / q)) ^ q ∂μ = ∫⁻ y, K y ∂μ := by
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
  have hB : ∫⁻ y, (K y ^ (1 / p) * G y) ^ p ∂μ = ∫⁻ y, K y * G y ^ p ∂μ := by
    refine lintegral_congr fun y => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
      ENNReal.rpow_one]
  have hmain : ∫⁻ y, K y * G y ∂μ ≤
      (∫⁻ y, K y ∂μ) ^ (1 / q) * (∫⁻ y, K y * G y ^ p ∂μ) ^ (1 / p) := by
    calc ∫⁻ y, K y * G y ∂μ = ∫⁻ y, K y ^ (1 / q) * (K y ^ (1 / p) * G y) ∂μ :=
          lintegral_congr hsplit
      _ ≤ _ := hholder
      _ = _ := by rw [hA, hB]
  calc (∫⁻ y, K y * G y ∂μ) ^ p
      ≤ ((∫⁻ y, K y ∂μ) ^ (1 / q) * (∫⁻ y, K y * G y ^ p ∂μ) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow hmain hp0.le
    _ = (∫⁻ y, K y ∂μ) ^ (p - 1) * ∫⁻ y, K y * G y ^ p ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
        congr 2
        have := hpq.inv_add_inv_eq_one
        field_simp at this ⊢
        linarith

/-- **Young's inequality in `ℝ≥0∞` form**: `∫ (K ⋆ G)^p ≤ (∫ K)^p ∫ G^p` for `p ≥ 1`. -/
theorem lintegral_convolution_rpow_le {K G : ℝ → ℝ≥0∞} (hK : Measurable K) (hG : Measurable G)
    {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, (∫⁻ y, K y * G (x - y)) ^ p ≤ (∫⁻ y, K y) ^ p * ∫⁻ x, G x ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have hprod : Measurable fun q : ℝ × ℝ => K q.2 * G (q.1 - q.2) ^ p :=
    (hK.comp measurable_snd).mul ((hG.comp (measurable_fst.sub measurable_snd)).pow_const p)
  calc ∫⁻ x, (∫⁻ y, K y * G (x - y)) ^ p
      ≤ ∫⁻ x, (∫⁻ y, K y) ^ (p - 1) * ∫⁻ y, K y * G (x - y) ^ p :=
        lintegral_mono fun x => lintegral_weighted_rpow_le volume hK.aemeasurable
          (hG.comp (measurable_const.sub measurable_id)).aemeasurable hp
    _ = (∫⁻ y, K y) ^ (p - 1) * ∫⁻ x, ∫⁻ y, K y * G (x - y) ^ p := by
        rw [lintegral_const_mul _ (by fun_prop)]
    _ = (∫⁻ y, K y) ^ (p - 1) * ∫⁻ y, ∫⁻ x, K y * G (x - y) ^ p := by
        rw [lintegral_lintegral_swap hprod.aemeasurable]
    _ = (∫⁻ y, K y) ^ (p - 1) * ∫⁻ y, K y * ∫⁻ x, G x ^ p := by
        congr 1
        refine lintegral_congr fun y => ?_
        rw [lintegral_const_mul _ (by fun_prop)]
        congr 1
        exact lintegral_sub_right_eq_self (fun x => G x ^ p) y
    _ = (∫⁻ y, K y) ^ p * ∫⁻ x, G x ^ p := by
        have h : (∫⁻ y, K y) ^ p = (∫⁻ y, K y) ^ (p - 1) * ∫⁻ y, K y := by
          conv_lhs => rw [show p = (p - 1) + 1 by ring]
          rw [ENNReal.rpow_add_of_nonneg (p - 1) 1 (by linarith) zero_le_one, ENNReal.rpow_one]
        rw [lintegral_mul_const _ hK, ← mul_assoc, h]

/-- The convolution `(k ⋆ f)(x) = ∫ k(t) f(x - t) dt` on the line. -/
noncomputable def lineConv (k f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t, k t * f (x - t)

theorem lineConv_congr_ae {k f f' : ℝ → ℂ} (h : f =ᵐ[volume] f') (x : ℝ) :
    lineConv k f x = lineConv k f' x := by
  refine integral_congr_ae ?_
  have h' : (fun t => f (x - t)) =ᵐ[volume] fun t => f' (x - t) :=
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [h'] with t ht
  simp only [ht]

theorem enorm_lineConv_le (k f : ℝ → ℂ) (x : ℝ) :
    ‖lineConv k f x‖ₑ ≤ ∫⁻ t, ‖k t‖ₑ * ‖f (x - t)‖ₑ := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  exact lintegral_congr fun t => enorm_mul _ _

/-- **Young's inequality** `‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p` for every `1 ≤ p ≤ ∞`. -/
theorem eLpNorm_lineConv_le {k f : ℝ → ℂ} (hk : Measurable k) (hf : AEStronglyMeasurable f)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (lineConv k f) p volume ≤ eLpNorm k 1 volume * eLpNorm f p volume := by
  set f' := hf.mk f
  have hf' : StronglyMeasurable f' := hf.stronglyMeasurable_mk
  have hff' : f =ᵐ[volume] f' := hf.ae_eq_mk
  have hconv : lineConv k f = lineConv k f' := funext (lineConv_congr_ae hff')
  rw [hconv, eLpNorm_congr_ae hff', eLpNorm_one_eq_lintegral_enorm]
  rcases eq_or_ne p ⊤ with rfl | hpt
  · rw [eLpNorm_exponent_top, eLpNorm_exponent_top]
    refine eLpNormEssSup_le_of_ae_enorm_bound (Eventually.of_forall fun x => ?_)
    refine (enorm_lineConv_le k f' x).trans ?_
    have hae : ∀ᵐ t ∂volume, ‖f' (x - t)‖ₑ ≤ eLpNormEssSup f' volume :=
      (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae
        (enorm_ae_le_eLpNormEssSup f' volume)
    calc ∫⁻ t, ‖k t‖ₑ * ‖f' (x - t)‖ₑ ≤ ∫⁻ t, ‖k t‖ₑ * eLpNormEssSup f' volume :=
          lintegral_mono_ae (hae.mono fun t ht => by gcongr)
      _ = (∫⁻ t, ‖k t‖ₑ) * eLpNormEssSup f' volume := lintegral_mul_const _ hk.enorm
  · have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
    have hpr : 1 ≤ p.toReal := by
      rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hpt hp
    have hpr0 : 0 < p.toReal := by linarith
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
    have hmain := lintegral_convolution_rpow_le hk.enorm hf'.measurable.enorm hpr
    calc (∫⁻ x, ‖lineConv k f' x‖ₑ ^ p.toReal) ^ (1 / p.toReal)
        ≤ ((∫⁻ y, ‖k y‖ₑ) ^ p.toReal * ∫⁻ x, ‖f' x‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
          refine ENNReal.rpow_le_rpow ((lintegral_mono fun x => ?_).trans hmain) (by positivity)
          exact ENNReal.rpow_le_rpow (enorm_lineConv_le k f' x) hpr0.le
      _ = (∫⁻ y, ‖k y‖ₑ) * (∫⁻ x, ‖f' x‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hpr0.ne', ENNReal.rpow_one]

end GaloisForLFunctions.HTGeometry

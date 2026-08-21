import GaloisForLFunctions.HTGeometry.PoincareHopf.VanishingLemma
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Translation invariance of the degree integral

The degree integral of `f` over `Ω` against a weight `φ` is `∫_Ω φ (f x) · det (Df x) dx`.  If `φ`
vanishes outside the ball of radius `ρ₀`, `‖z‖ ≤ ρ₁`, and `‖f‖ > ρ₀ + ρ₁` on the boundary of `Ω`,
then translating the weight by `z` does not change the integral.

The proof is the fundamental vanishing lemma applied to the one parameter family of fields
`W t w = -φ (w - t z) · z`, whose divergence is exactly the `t`-derivative of `w ↦ φ (w - t z)`.
The fundamental theorem of calculus in `t` and Fubini then turn the difference of the two degree
integrals into `∫₀¹ 0 dt`.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ}

/-- The degree integral of `f` over `Ω` against the weight `φ`. -/
noncomputable def degIntegral (f : (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Set (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x in Ω, φ (f x) * (jac f x).det

/-- The field whose divergence is the `t`-derivative of `w ↦ φ (w - t • z)`. -/
noncomputable def transField (φ : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) (t : ℝ) :
    (Fin n → ℝ) → (Fin n → ℝ) := fun w => (-φ (w - t • z)) • z

/-- The `t`-derivative of `w ↦ φ (w - t • z)`. -/
noncomputable def transDeriv (φ : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) (t : ℝ) (w : Fin n → ℝ) : ℝ :=
  -(fderiv ℝ φ (w - t • z)) z

section

variable {f : (Fin n → ℝ) → (Fin n → ℝ)} {Ω : Set (Fin n → ℝ)} {φ : (Fin n → ℝ) → ℝ}

theorem continuous_det_jac (hf : ContDiff ℝ 2 f) : Continuous fun x => (jac f x).det := by
  simp only [Matrix.det_apply']
  refine continuous_finsetSum _ fun σ _ => ?_
  exact continuous_const.mul
    (continuous_finsetProd _ fun k _ => (contDiff_jacEntry hf (σ k) k).continuous)

theorem hasDerivAt_trans (hφ : Differentiable ℝ φ) (z w : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (w - s • z)) (transDeriv φ z t w) t := by
  have h1 : HasDerivAt (fun s : ℝ => w - s • z) (-z) t := by
    simpa using ((hasDerivAt_id t).smul_const z).const_sub w
  have h2 := (hφ (w - t • z)).hasFDerivAt.comp_hasDerivAt t h1
  simpa [transDeriv, Function.comp_def] using h2

theorem fieldDivergence_transField (hφ : ContDiff ℝ 1 φ) (z : Fin n → ℝ) (t : ℝ)
    (w : Fin n → ℝ) : fieldDivergence (transField φ z t) w = transDeriv φ z t w := by
  have hshift : HasFDerivAt (fun w' : Fin n → ℝ => w' - t • z)
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)) w := (hasFDerivAt_id w).sub_const _
  have hcomp : HasFDerivAt (fun w' => φ (w' - t • z)) (fderiv ℝ φ (w - t • z)) w := by
    have := ((hφ.differentiable (by simp)) (w - t • z)).hasFDerivAt.comp w hshift
    simpa [Function.comp_def] using this
  have hneg : HasFDerivAt (fun w' => -φ (w' - t • z)) (-(fderiv ℝ φ (w - t • z))) w := hcomp.neg
  have hfd : HasFDerivAt (transField φ z t)
      ((-(fderiv ℝ φ (w - t • z))).smulRight z) w := hneg.smul_const z
  have hexp : (fderiv ℝ φ (w - t • z)) z
      = ∑ l, z l * (fderiv ℝ φ (w - t • z)) (Pi.single l 1) := by
    rw [clm_apply_eq_sum (F := ℝ) (fderiv ℝ φ (w - t • z)) z]
    simp [smul_eq_mul]
  rw [fieldDivergence, hfd.fderiv, transDeriv, hexp]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.neg_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem transField_eq_zero {ρ₀ ρ₁ : ℝ} (hφsupp : ∀ w, ρ₀ ≤ ‖w‖ → φ w = 0)
    {z : Fin n → ℝ} (hz : ‖z‖ ≤ ρ₁) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {w : Fin n → ℝ} (hw : ρ₀ + ρ₁ ≤ ‖w‖) : transField φ z t w = 0 := by
  have hzt : ‖t • z‖ ≤ ρ₁ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc t * ‖z‖ ≤ 1 * ‖z‖ := by
          have := norm_nonneg z
          nlinarith
      _ = ‖z‖ := one_mul _
      _ ≤ ρ₁ := hz
  have : ρ₀ ≤ ‖w - t • z‖ := by
    have h := norm_sub_norm_le w (t • z)
    have : ‖w‖ - ‖t • z‖ ≤ ‖w - t • z‖ := h
    linarith
  simp [transField, hφsupp _ this]

theorem contDiff_transField (hφ : ContDiff ℝ 1 φ) (z : Fin n → ℝ) (t : ℝ) :
    ContDiff ℝ 1 (transField φ z t) :=
  ContDiff.smul ((hφ.comp (contDiff_id.sub contDiff_const)).neg) contDiff_const

theorem integrableOn_of_continuous {g : (Fin n → ℝ) → ℝ} (hg : Continuous g)
    (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) : IntegrableOn g Ω := by
  have hK : IsCompact (closure Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hΩb.closure
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  haveI : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hΩb.measure_lt_top⟩
  refine Integrable.mono' (g := fun _ => C) (integrable_const C)
    (hg.aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem hΩm] with x hx
  exact hC x (subset_closure hx)

/-- Each slice of the one parameter family integrates to zero. -/
theorem integral_transDeriv_slice_eq_zero {ρ₀ ρ₁ : ℝ}
    (hf : ContDiff ℝ 2 f) (hφ : ContDiff ℝ 1 φ)
    (hφsupp : ∀ w, ρ₀ ≤ ‖w‖ → φ w = 0)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {z : Fin n → ℝ} (hz : ‖z‖ ≤ ρ₁)
    (hfront : ∀ x ∈ frontier Ω, ρ₀ + ρ₁ < ‖f x‖)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ x in Ω, transDeriv φ z t (f x) * (jac f x).det = 0 := by
  have h := integral_divergence_comp_det_eq_zero (u := f) (W := transField φ z t)
    (ρ := ρ₀ + ρ₁) hf (contDiff_transField hφ z t)
    (fun w hw => transField_eq_zero hφsupp hz ht0 ht1 hw) hΩ hΩb hfront
  simpa [fieldDivergence_transField hφ] using h

/-- **Translation invariance of the degree integral.** -/
theorem degIntegral_translate {ρ₀ ρ₁ : ℝ}
    (hf : ContDiff ℝ 2 f) (hφ : ContDiff ℝ 1 φ)
    (hφsupp : ∀ w, ρ₀ ≤ ‖w‖ → φ w = 0)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {z : Fin n → ℝ} (hz : ‖z‖ ≤ ρ₁)
    (hfront : ∀ x ∈ frontier Ω, ρ₀ + ρ₁ < ‖f x‖) :
    degIntegral f Ω (fun w => φ (w - z)) = degIntegral f Ω φ := by
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hfc : Continuous f := hf.continuous
  have hφc : Continuous φ := hφ.continuous
  have hdetc : Continuous fun x => (jac f x).det := continuous_det_jac hf
  have hfdc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  set G : (Fin n → ℝ) → ℝ → ℝ := fun x t => transDeriv φ z t (f x) * (jac f x).det with hGdef
  have hGcont : Continuous (Function.uncurry G) := by
    have h1 : Continuous fun p : (Fin n → ℝ) × ℝ => f p.1 - p.2 • z :=
      (hfc.comp continuous_fst).sub (continuous_snd.smul continuous_const)
    have h3 : Continuous fun p : (Fin n → ℝ) × ℝ => (fderiv ℝ φ (f p.1 - p.2 • z)) z :=
      (hfdc.comp h1).clm_apply continuous_const
    exact h3.neg.mul (hdetc.comp continuous_fst)
  -- every slice vanishes
  have hslice : ∀ t ∈ Ioc (0:ℝ) 1, (∫ x in Ω, G x t) = 0 := fun t ht =>
    integral_transDeriv_slice_eq_zero hf hφ hφsupp hΩ hΩb hz hfront ht.1.le ht.2
  -- the fundamental theorem of calculus in the parameter
  have hFTC : ∀ x, (∫ t in Ioc (0:ℝ) 1, G x t)
      = φ (f x - z) * (jac f x).det - φ (f x) * (jac f x).det := by
    intro x
    have hsc : Continuous fun s : ℝ => transDeriv φ z s (f x) := by
      have h1 : Continuous fun s : ℝ => f x - s • z :=
        continuous_const.sub (continuous_id.smul continuous_const)
      exact ((hfdc.comp h1).clm_apply continuous_const).neg
    have hd : ∀ s ∈ uIcc (0:ℝ) 1, HasDerivAt (fun s : ℝ => φ (f x - s • z))
        (transDeriv φ z s (f x)) s :=
      fun s _ => hasDerivAt_trans (hφ.differentiable (by simp)) z (f x) s
    have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hsc.intervalIntegrable 0 1)
    rw [intervalIntegral.integral_of_le zero_le_one] at hsub
    have hpull : (∫ t in Ioc (0:ℝ) 1, G x t)
        = (∫ t in Ioc (0:ℝ) 1, transDeriv φ z t (f x)) * (jac f x).det := by
      simp only [hGdef]
      exact MeasureTheory.integral_mul_const _ _
    rw [hpull, hsub]
    simp [sub_mul]
  -- joint integrability
  have hint : Integrable (Function.uncurry G)
      ((volume.restrict Ω).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
    have hK : IsCompact ((closure Ω) ×ˢ (Icc (0:ℝ) 1)) :=
      (Metric.isCompact_of_isClosed_isBounded isClosed_closure hΩb.closure).prod isCompact_Icc
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hGcont.continuousOn
    rw [Measure.prod_restrict]
    haveI : IsFiniteMeasure ((volume.prod volume).restrict (Ω ×ˢ Ioc (0:ℝ) 1)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ, Measure.prod_prod]
      exact ENNReal.mul_lt_top hΩb.measure_lt_top measure_Ioc_lt_top
    refine Integrable.mono' (g := fun _ => C) (integrable_const C)
      hGcont.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem (hΩm.prod measurableSet_Ioc)] with p hp
    exact hC p ⟨subset_closure hp.1, Ioc_subset_Icc_self hp.2⟩
  -- assemble
  have hI1 : IntegrableOn (fun x => φ (f x - z) * (jac f x).det) Ω :=
    integrableOn_of_continuous (((hφc.comp (hfc.sub continuous_const))).mul hdetc) hΩm hΩb
  have hI2 : IntegrableOn (fun x => φ (f x) * (jac f x).det) Ω :=
    integrableOn_of_continuous ((hφc.comp hfc).mul hdetc) hΩm hΩb
  have hdiff : degIntegral f Ω (fun w => φ (w - z)) - degIntegral f Ω φ
      = ∫ x in Ω, (φ (f x - z) * (jac f x).det - φ (f x) * (jac f x).det) := by
    rw [degIntegral, degIntegral, ← MeasureTheory.integral_sub hI1 hI2]
  have hswap : (∫ x in Ω, ∫ t in Ioc (0:ℝ) 1, G x t)
      = ∫ t in Ioc (0:ℝ) 1, ∫ x in Ω, G x t := MeasureTheory.integral_integral_swap hint
  have hzero : (∫ t in Ioc (0:ℝ) 1, ∫ x in Ω, G x t) = 0 := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hslice]
    simp
  have : degIntegral f Ω (fun w => φ (w - z)) - degIntegral f Ω φ = 0 := by
    rw [hdiff, ← MeasureTheory.setIntegral_congr_fun hΩm (fun x (_ : x ∈ Ω) => hFTC x),
      hswap, hzero]
  linarith [this]

end

end GaloisForLFunctions.HTGeometry.PoincareHopf

import GaloisForLFunctions.HTGeometry.WeightedDensityL2
import GaloisForLFunctions.HTGeometry.FourierTranslationModulation
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# The Mellin unitary of the half line

On `H = L²((0,∞), dr)` the substitution `r = eˣ` with half-density `e^{x/2}`,

`(U f)(x) = e^{x/2} f(eˣ)`,

is a unitary onto `L²(ℝ)`: the measure `eˣ dx` is carried by `exp` onto Lebesgue measure on
`(0,∞)`, and multiplication by `e^{x/2}` is the weighted-density unitary.  Composing with the
Fourier–Plancherel unitary gives the Mellin unitary `𝓜 = 𝓕 ∘ U`.

For an integrable half-density pullback, `𝓜 f(ξ) = ∫₀^∞ f(r) r^{s-1} dr` at `s = 1/2 - 2πiξ`, so
`𝓜` is the Mellin transform on the unitary line `Re s = 1/2`.  For the Gamma profiles
`r^α e^{-tr}` one has `mellin (r^α e^{-tr}) s = t^{-(s+α)} Γ(s+α)` when `Re(s+α) > 0`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- `H = L²((0,∞), dr)`. -/
abbrev HalfLineL2 : Type := Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

/-- The measure `eˣ dx` on the line. -/
abbrev expWeightMeasure : Measure ℝ := (volume : Measure ℝ).withDensity (realDensity Real.exp)

theorem map_exp_expWeightMeasure :
    Measure.map Real.exp expWeightMeasure = volume.restrict (Ioi (0 : ℝ)) := by
  ext A hA
  rw [Measure.map_apply Real.measurable_exp hA, expWeightMeasure,
    withDensity_apply _ (Real.measurable_exp hA), Measure.restrict_apply hA]
  have himg : Real.exp '' (Real.exp ⁻¹' A) = A ∩ Ioi 0 := by
    rw [Set.image_preimage_eq_inter_range, Real.range_exp]
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
    (Real.measurable_exp hA) (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn (fun _ => 1)
  rw [himg] at hcv
  simp only [lintegral_one, mul_one, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter] at hcv
  rw [hcv]
  refine lintegral_congr fun x => ?_
  simp [realDensity, abs_of_pos (Real.exp_pos x)]

theorem measurePreserving_exp_expWeightMeasure :
    MeasurePreserving Real.exp expWeightMeasure (volume.restrict (Ioi (0 : ℝ))) :=
  ⟨Real.measurable_exp, map_exp_expWeightMeasure⟩

theorem map_log_restrict_Ioi :
    Measure.map Real.log (volume.restrict (Ioi (0 : ℝ))) = expWeightMeasure := by
  rw [← map_exp_expWeightMeasure, Measure.map_map Real.measurable_log Real.measurable_exp]
  have h : Real.log ∘ Real.exp = id := funext Real.log_exp
  rw [h, Measure.map_id]

theorem measurePreserving_log_restrict_Ioi :
    MeasurePreserving Real.log (volume.restrict (Ioi (0 : ℝ))) expWeightMeasure :=
  ⟨Real.measurable_log, map_log_restrict_Ioi⟩

/-- Pullback by `exp`, from `L²((0,∞), dr)` onto `L²(eˣ dx)`. -/
def halfLineExpPullback : HalfLineL2 ≃ₗᵢ[ℂ] Lp ℂ 2 expWeightMeasure where
  toFun f := Lp.compMeasurePreserving Real.exp measurePreserving_exp_expWeightMeasure f
  invFun g := Lp.compMeasurePreserving Real.log measurePreserving_log_restrict_Ioi g
  map_add' f g := map_add _ f g
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_compMeasurePreserving (c • f) measurePreserving_exp_expWeightMeasure,
      Lp.coeFn_smul c (Lp.compMeasurePreserving Real.exp measurePreserving_exp_expWeightMeasure f),
      Lp.coeFn_compMeasurePreserving f measurePreserving_exp_expWeightMeasure,
      measurePreserving_exp_expWeightMeasure.quasiMeasurePreserving.ae
        (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
    simp only [RingHom.id_apply] at *
    rw [h1, h2, Pi.smul_apply, h3]
    simpa using h4
  left_inv f := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_compMeasurePreserving
        (Lp.compMeasurePreserving Real.exp measurePreserving_exp_expWeightMeasure f)
        measurePreserving_log_restrict_Ioi,
      measurePreserving_log_restrict_Ioi.quasiMeasurePreserving.ae
        (Lp.coeFn_compMeasurePreserving f measurePreserving_exp_expWeightMeasure),
      ae_restrict_mem measurableSet_Ioi] with r h1 h2 hr
    rw [h1, Function.comp_apply, h2, Function.comp_apply, Real.exp_log hr]
  right_inv g := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_compMeasurePreserving
        (Lp.compMeasurePreserving Real.log measurePreserving_log_restrict_Ioi g)
        measurePreserving_exp_expWeightMeasure,
      measurePreserving_exp_expWeightMeasure.quasiMeasurePreserving.ae
        (Lp.coeFn_compMeasurePreserving g measurePreserving_log_restrict_Ioi)] with x h1 h2
    rw [h1, Function.comp_apply, h2, Function.comp_apply, Real.log_exp]
  norm_map' f := Lp.norm_compMeasurePreserving f measurePreserving_exp_expWeightMeasure

/-- The half-density exponential unitary `U f(x) = e^{x/2} f(eˣ)` of `L²((0,∞), dr)` onto
`L²(ℝ)`. -/
def halfLineExpUnitary : HalfLineL2 ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  halfLineExpPullback.trans
    (weightedDensityUnitary (μ := volume) Real.exp Real.measurable_exp Real.exp_pos)

theorem halfLineExpUnitary_ae (f : HalfLineL2) :
    (halfLineExpUnitary f : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.sqrt (Real.exp x) : ℂ) * (f : ℝ → ℂ) (Real.exp x) := by
  have h1 := densityMul_ae (μ := volume) Real.exp Real.measurable_exp Real.exp_pos
    (halfLineExpPullback f)
  have h2 : (halfLineExpPullback f : ℝ → ℂ) =ᵐ[volume] fun x => (f : ℝ → ℂ) (Real.exp x) := by
    have h := Lp.coeFn_compMeasurePreserving f measurePreserving_exp_expWeightMeasure
    exact (withDensity_realDensity_ae_eq Real.measurable_exp Real.exp_pos).1 h
  change (densityMul (μ := volume) Real.exp Real.measurable_exp Real.exp_pos
    (halfLineExpPullback f) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2]
  rfl

/-- The Mellin unitary `𝓜 = 𝓕 ∘ U` of `L²((0,∞), dr)` onto `L²(ℝ)`. -/
def halfLineMellinUnitary : HalfLineL2 ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  halfLineExpUnitary.trans (Lp.fourierTransformₗᵢ ℝ ℂ)

/-- The half-density pullback of a function on `(0,∞)`. -/
def halfDensityPullback (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.sqrt (Real.exp x) : ℂ) * g (Real.exp x)

/-- `𝓕(e^{x/2} g(eˣ))(ξ) = mellin g (1/2 - 2πiξ)`. -/
theorem fourier_halfDensityPullback (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (halfDensityPullback g) ξ =
      mellin g (1 / 2 - 2 * Real.pi * ξ * Complex.I) := by
  rw [mellin_eq_fourier]
  have hre : (1 / 2 - 2 * Real.pi * ξ * Complex.I : ℂ).re = 1 / 2 := by simp
  have him : (1 / 2 - 2 * Real.pi * ξ * Complex.I : ℂ).im / (2 * Real.pi) = -ξ := by
    simp
    field_simp [Real.pi_ne_zero]
  rw [hre, him, Real.fourier_real_eq, Real.fourier_real_eq]
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [halfDensityPullback]
  have hs : (Real.sqrt (Real.exp (-v)) : ℂ) = ((Real.exp (-(1 / 2) * v) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 2
    ring
  rw [hs]
  simp only [neg_mul, neg_neg, mul_neg, Circle.smul_def, smul_eq_mul, Complex.real_smul]

/-- For an integrable half-density pullback, `𝓜 f(ξ) = mellin f (1/2 - 2πiξ)` a.e. -/
theorem halfLineMellinUnitary_ae_eq_mellin (f : HalfLineL2) (g : ℝ → ℂ)
    (hfg : (f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] g)
    (hint : Integrable (halfDensityPullback g)) :
    (halfLineMellinUnitary f : ℝ → ℂ) =ᵐ[volume]
      fun ξ => mellin g (1 / 2 - 2 * Real.pi * ξ * Complex.I) := by
  have hU : (halfLineExpUnitary f : ℝ → ℂ) =ᵐ[volume] halfDensityPullback g := by
    have hfg' : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), (f : ℝ → ℂ) r = g r := hfg
    have hpull : ∀ᵐ x ∂expWeightMeasure, (f : ℝ → ℂ) (Real.exp x) = g (Real.exp x) :=
      measurePreserving_exp_expWeightMeasure.quasiMeasurePreserving.ae hfg'
    have hpull' : ∀ᵐ x ∂(volume : Measure ℝ), (f : ℝ → ℂ) (Real.exp x) = g (Real.exp x) :=
      (withDensity_realDensity_ae_eq (μ := volume) Real.measurable_exp Real.exp_pos
        (f := fun x => (f : ℝ → ℂ) (Real.exp x)) (g := fun x => g (Real.exp x))).1 hpull
    filter_upwards [halfLineExpUnitary_ae f, hpull'] with x hx1 hx2
    rw [hx1, halfDensityPullback, hx2]
  have hUint : Integrable (halfLineExpUnitary f : ℝ → ℂ) := hint.congr hU.symm
  have hF := coeFn_fourierTransform_eq_fourierIntegral (halfLineExpUnitary f) hUint
  change ((𝓕 (halfLineExpUnitary f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [hF] with ξ hξ
  rw [hξ, ← fourier_halfDensityPullback]
  exact Real.fourier_congr_ae hU ξ

/-! ## Gamma profiles -/

/-- `mellin (e^{-tr}) s = t^{-s} Γ(s)` for `Re s > 0`. -/
theorem mellin_exp_neg_scale {t : ℝ} (ht : 0 < t) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun r : ℝ => ((Real.exp (-(t * r)) : ℝ) : ℂ)) s =
      (t : ℂ) ^ (-s) * Complex.Gamma s := by
  have h := mellin_comp_mul_left (fun r : ℝ => ((Real.exp (-r) : ℝ) : ℂ)) s ht
  rw [h, ← Complex.GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral hs, smul_eq_mul]

/-- `mellin (r^α e^{-tr}) s = t^{-(s+α)} Γ(s+α)` for `Re(s+α) > 0`. -/
theorem mellin_cpow_mul_exp_neg_mul {t : ℝ} (ht : 0 < t) (α s : ℂ) (hs : 0 < (s + α).re) :
    mellin (fun r : ℝ => (r : ℂ) ^ α * ((Real.exp (-(t * r)) : ℝ) : ℂ)) s =
      (t : ℂ) ^ (-(s + α)) * Complex.Gamma (s + α) := by
  have h := mellin_cpow_smul (fun r : ℝ => ((Real.exp (-(t * r)) : ℝ) : ℂ)) s α
  simp only [smul_eq_mul] at h
  rw [h, mellin_exp_neg_scale ht hs]

end GaloisForLFunctions.HTGeometry

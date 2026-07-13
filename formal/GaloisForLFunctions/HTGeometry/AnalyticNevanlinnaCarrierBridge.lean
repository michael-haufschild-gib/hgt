import GaloisForLFunctions.HTGeometry.NevanlinnaPositiveCarrierCapstone
import GaloisForLFunctions.HTGeometry.NevanlinnaClassicalInterface
import GaloisForLFunctions.HTGeometry.CauchyJetFrame

/-!
# Analytic Nevanlinna carrier bridge

The projective boundary kernel records the classical extremal measures and their support labels,
but it deliberately does not postulate their analytic Cauchy-transform formula.  This file adds a
source-faithful interface for precisely that classical formula and proves the project-specific
consequence: a positive bounded reweighting has Cauchy transform equal to the full affine
Nevanlinna family `m₀ + a/(τ-q)` averaged against the density.  No part of the affine reduction or
the barycentric integration argument is left as an external assumption.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint Filter Measure Metric Complex
open scoped ENNReal OnePoint Topology ComplexOrder

noncomputable section

/-- Classical analytic data in the carrier convention.  The base family is the source-faithful
classical N-extremal family.  The four entire functions extend its determinant-one real carrier
matrix, and the two transform fields are exactly the finite and infinite parts of the classical
Nevanlinna parametrization. -/
structure ClassicalAnalyticNevanlinnaCarrierFamily (s : ℕ → ℝ) where
  base : ClassicalNevanlinnaExtremalFamily s
  a : ℂ → ℂ
  b : ℂ → ℂ
  c : ℂ → ℂ
  d : ℂ → ℂ
  differentiable_a : Differentiable ℂ a
  differentiable_b : Differentiable ℂ b
  differentiable_c : Differentiable ℂ c
  differentiable_d : Differentiable ℂ d
  det_one : ∀ z, a z * d z - b z * c z = 1
  a_real : ∀ x : ℝ, a x = base.toBoundaryFamily.matrix.a x
  b_real : ∀ x : ℝ, b x = base.toBoundaryFamily.matrix.b x
  c_real : ∀ x : ℝ, c x = base.toBoundaryFamily.matrix.c x
  d_real : ∀ x : ℝ, d x = base.toBoundaryFamily.matrix.d x
  finite_cauchy : ∀ (tau : ℝ) (z : ℂ), 0 < z.im →
    (∫ x, ((x : ℂ) - z)⁻¹ ∂(base.leaf tau : Measure ℝ)) =
      (a z * tau + b z) / (c z * tau + d z)
  infinity_cauchy : ∀ z : ℂ, 0 < z.im → c z ≠ 0 →
    (∫ x, ((x : ℂ) - z)⁻¹ ∂(base.leaf ∞ : Measure ℝ)) = a z / c z

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- The background, amplitude, and projective pole of the analytic carrier chart. -/
def background (z : ℂ) : ℂ := F.a z / F.c z

def amplitude (z : ℂ) : ℂ := -1 / F.c z ^ 2

def quotient (z : ℂ) : ℂ := -F.d z / F.c z

/-- Complex determinant-one Mobius subtraction. -/
theorem complex_mobius_difference
    {A B C D tau : ℂ} (hdet : A * D - B * C = 1)
    (hC : C ≠ 0) (hden : C * tau + D ≠ 0) :
    (A * tau + B) / (C * tau + D) =
      A / C + (-1 / C ^ 2) / (tau - (-D / C)) := by
  have hden' : tau * C + D ≠ 0 := by simpa [mul_comm] using hden
  field_simp [hC, hden, hden']
  linear_combination -(C * tau + D) * hdet

/-- A real parameter cannot meet an upper-half-plane projective pole, so the finite Mobius
denominator is nonzero on the analytic chart. -/
theorem finite_denominator_ne_zero_of_quotient_upper
    (z : ℂ) (hc : F.c z ≠ 0) (hq : 0 < (F.quotient z).im) (tau : ℝ) :
    F.c z * (tau : ℂ) + F.d z ≠ 0 := by
  have htauq : (tau : ℂ) ≠ F.quotient z := by
    intro h
    have him := congrArg Complex.im h
    simp only [ofReal_im] at him
    linarith
  have hfactor : F.c z * (tau : ℂ) + F.d z =
      F.c z * ((tau : ℂ) - F.quotient z) := by
    simp only [quotient]
    field_simp [hc]
    ring
  rw [hfactor]
  exact mul_ne_zero hc (sub_ne_zero.mpr htauq)

/-- The two classical transform clauses combine into one continuous projective affine formula.
The value at the point at infinity is exactly the background because the projective Cauchy term
vanishes there. -/
theorem leaf_cauchy_eq_background_add_projective
    (t : OnePoint ℝ) (z : ℂ) (hz : 0 < z.im)
    (hc : F.c z ≠ 0) (hq : 0 < (F.quotient z).im) :
    (∫ x, ((x : ℂ) - z)⁻¹ ∂(F.base.leaf t : Measure ℝ)) =
      F.background z + F.amplitude z * projectiveCauchyPower (F.quotient z) 0 t := by
  induction t using OnePoint.rec with
  | coe tau =>
      rw [F.finite_cauchy tau z hz]
      rw [complex_mobius_difference (F.det_one z) hc
        (F.finite_denominator_ne_zero_of_quotient_upper z hc hq tau)]
      simp [background, amplitude, quotient, projectiveCauchyPower, div_eq_mul_inv]
  | infty =>
      rw [F.infinity_cauchy z hz hc]
      simp [background, amplitude, quotient, projectiveCauchyPower]

/-- The projective affine leaf transform is continuous in the compactified real parameter. -/
theorem continuous_leaf_cauchy
    (z : ℂ) (hz : 0 < z.im) (hc : F.c z ≠ 0)
    (hq : 0 < (F.quotient z).im) :
    Continuous (fun t : OnePoint ℝ =>
      ∫ x, ((x : ℂ) - z)⁻¹ ∂(F.base.leaf t : Measure ℝ)) := by
  have hproj : Continuous (projectiveCauchyPower (F.quotient z) 0) :=
    continuous_projectiveCauchyPower (F.quotient z) hq.ne' 0
  apply (continuous_const.add (continuous_const.mul hproj)).congr
  intro t
  exact (F.leaf_cauchy_eq_background_add_projective t z hz hc hq).symm

/-- The Cauchy kernel at an upper-half-plane point is integrable against every finite real
measure. -/
theorem integrable_cauchyKernel_of_im_pos
    (mu : Measure ℝ) [IsFiniteMeasure mu] (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) mu := by
  have hzsupport : z ∉ algebraMap ℝ ℂ '' mu.support := by
    rintro ⟨x, _hx, hzx⟩
    have him := congrArg Complex.im hzx
    simp only [map_eq_ofReal, ofReal_im] at him
    linarith
  simpa [resolvent, pow_one] using
    (integrable_resolvent_pow (mu := mu) hzsupport 1)

/-- Integrating the Cauchy kernel through a positive bounded boundary reweighting is exactly
integration of the leaf Cauchy transforms against that density.  This is the complex-valued
Fubini step underlying the carrier bridge. -/
theorem weightedBoundaryCarrier_cauchy_eq_parameterIntegral
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]
    (w : Lp ℝ (⊤ : ENNReal) eta) (hw : LinftyStrictlyPositive eta w)
    (hint : ∫ t, w t ∂eta = 1)
    (z : ℂ) (hz : 0 < z.im) (hc : F.c z ≠ 0)
    (hq : 0 < (F.quotient z).im) :
    (∫ x, ((x : ℂ) - z)⁻¹
        ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta w) =
      ∫ t, (w t) •
        (∫ x, ((x : ℂ) - z)⁻¹ ∂(F.base.leaf t : Measure ℝ)) ∂eta := by
  letI : IsProbabilityMeasure (linftyDensityMeasure eta w) :=
    linftyDensityMeasure_isProbabilityMeasure eta w hw hint
  letI (t : OnePoint ℝ) : IsProbabilityMeasure
      (F.base.leaf t : Measure ℝ) := (F.base.leaf t).prop
  letI : IsProbabilityMeasure
      (weightedBoundaryCarrier F.base.toBoundaryFamily eta w) := by
    dsimp only [weightedBoundaryCarrier]
    exact boundaryBarycenter_isProbabilityMeasure
      (linftyDensityMeasure eta w)
      (fun t => (F.base.toBoundaryFamily.leaf t : Measure ℝ))
      F.base.toBoundaryFamily.measurable_leaf
      (fun t => (F.base.toBoundaryFamily.leaf t).prop)
  let inner : OnePoint ℝ → ℂ := fun t =>
    ∫ x, ((x : ℂ) - z)⁻¹ ∂(F.base.leaf t : Measure ℝ)
  have hinner : Continuous inner := F.continuous_leaf_cauchy z hz hc hq
  have hinnerLp : MemLp inner 1 eta :=
    hinner.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hparam : Integrable (fun t => (w t) • inner t) eta :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).integrable_of_bilin_of_bdd_left
      ‖w‖ (Lp.memLp w).1 (linfty_ae_abs_le_norm eta w)
      (hinnerLp.integrable (by norm_num))
  have hcarrier : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹)
      (weightedBoundaryCarrier F.base.toBoundaryFamily eta w) :=
    integrable_cauchyKernel_of_im_pos
      (weightedBoundaryCarrier F.base.toBoundaryFamily eta w) z hz
  apply Complex.ext
  · rw [← integral_re hcarrier, ← integral_re hparam]
    rw [weightedBoundaryCarrier, boundaryBarycenter, integral_bind_real
      (linftyDensityMeasure eta w)
      (fun t => (F.base.toBoundaryFamily.leaf t : Measure ℝ))
      (fun x : ℝ => (((x : ℂ) - z)⁻¹).re)
      F.base.toBoundaryFamily.measurable_leaf
      ((continuous_ofReal.sub continuous_const).inv₀
        (fun x hzero => by
          have him := congrArg Complex.im hzero
          simp only [sub_im, ofReal_im, zero_sub] at him
          linarith)).re.measurable hcarrier.re]
    rw [linftyDensityMeasure]
    have hmeas : AEMeasurable (fun t => ENNReal.ofReal (w t)) eta :=
      (Lp.memLp w).1.aemeasurable.ennreal_ofReal
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hw] with t ht
    rw [ENNReal.toReal_ofReal ht.le]
    have hleaf := integrable_cauchyKernel_of_im_pos
      (F.base.leaf t : Measure ℝ) z hz
    rw [integral_re hleaf]
    rfl
  · rw [← integral_im hcarrier, ← integral_im hparam]
    rw [weightedBoundaryCarrier, boundaryBarycenter, integral_bind_real
      (linftyDensityMeasure eta w)
      (fun t => (F.base.toBoundaryFamily.leaf t : Measure ℝ))
      (fun x : ℝ => (((x : ℂ) - z)⁻¹).im)
      F.base.toBoundaryFamily.measurable_leaf
      ((continuous_ofReal.sub continuous_const).inv₀
        (fun x hzero => by
          have him := congrArg Complex.im hzero
          simp only [sub_im, ofReal_im, zero_sub] at him
          linarith)).im.measurable hcarrier.im]
    rw [linftyDensityMeasure]
    have hmeas : AEMeasurable (fun t => ENNReal.ofReal (w t)) eta :=
      (Lp.memLp w).1.aemeasurable.ennreal_ofReal
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hw] with t ht
    rw [ENNReal.toReal_ofReal ht.le]
    have hleaf := integrable_cauchyKernel_of_im_pos
      (F.base.leaf t : Measure ℝ) z hz
    rw [integral_im hleaf]
    rfl

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry

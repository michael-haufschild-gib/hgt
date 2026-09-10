import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundaryEigenvectors

/-! Genuine rational generator rates on the open left unit semicircle.
Normalization preserves actual eigenvectors and permits imaginary endpoint limits. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem boundary_rate_ne_zero (b ω : ℝ) : (causalBoundaryRate b ω).val ≠ 0 := by
  intro h
  have he : (causalBoundaryRate b ω).val.re = 0 := congrArg Complex.re h
  exact (ne_of_lt (causalBoundaryRate b ω).property) he

/-- Actual left-half-plane rates normalized to the unit circle, with unrestricted real parameters. -/
def causalUnitBoundaryRate (b ω : ℝ) : {z : ℂ // z.re < 0} :=
  ⟨(causalBoundaryRate b ω).val / (‖(causalBoundaryRate b ω).val‖ : ℂ), by
    rw [Complex.div_ofReal_re]
    exact div_neg_of_neg_of_pos (causalBoundaryRate b ω).property
      (norm_pos_iff.mpr (boundary_rate_ne_zero b ω))⟩

/-- The genuine normalized rate has modulus exactly one. -/
theorem norm_causalUnitBoundaryRate (b ω : ℝ) : ‖(causalUnitBoundaryRate b ω).val‖ = 1 := by
  change ‖(causalBoundaryRate b ω).val / (‖(causalBoundaryRate b ω).val‖ : ℂ)‖ = _
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (boundary_rate_ne_zero b ω))]

/-- The real coordinate of the normalized rate records its genuine damping. -/
theorem causalUnitBoundaryRate_re (b ω : ℝ) :
    (causalUnitBoundaryRate b ω).val.re = -Real.exp b / ‖(causalBoundaryRate b ω).val‖ := by
  change ((causalBoundaryRate b ω).val / (‖(causalBoundaryRate b ω).val‖ : ℂ)).re = _
  rw [Complex.div_ofReal_re]
  simp only [causalBoundaryRate, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero,
    zero_mul, sub_zero, add_zero]

/-- The imaginary coordinate retains the normalized actual boundary frequency. -/
theorem causalUnitBoundaryRate_im (b ω : ℝ) :
    (causalUnitBoundaryRate b ω).val.im = ω / ‖(causalBoundaryRate b ω).val‖ := by
  change ((causalBoundaryRate b ω).val / (‖(causalBoundaryRate b ω).val‖ : ℂ)).im = _
  rw [Complex.div_ofReal_im]
  simp only [causalBoundaryRate, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
    neg_zero, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, add_zero, zero_add]

/-- All normalized negative real rates are exactly minus one. -/
theorem causalUnitBoundaryRate_real (b : ℝ) : (causalUnitBoundaryRate b 0).val = -1 := by
  have hn : ‖(causalBoundaryRate b 0).val‖ = Real.exp b := by
    change ‖-(Real.exp b : ℂ) + (0 : ℂ)*I‖ = _
    rw [zero_mul, add_zero, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Complex.ext
  · rw [causalUnitBoundaryRate_re, hn, neg_div, div_self (Real.exp_ne_zero b)]
    rfl
  · rw [causalUnitBoundaryRate_im, zero_div]
    simp only [Complex.neg_im, Complex.one_im, neg_zero]

private theorem boundary_rate_tendsto (ω : ℝ) :
    Tendsto (fun b : ℝ => (causalBoundaryRate b ω).val) atBot (𝓝 ((ω : ℂ)*I)) := by
  have h : Tendsto (fun b : ℝ => -(Real.exp b : ℂ) + (ω : ℂ)*I) atBot
      (𝓝 (-(0 : ℂ) + (ω : ℂ)*I)) :=
    ((Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_atBot).neg.add_const _
  simpa only [causalBoundaryRate, neg_zero, zero_add] using! h

/-- Genuine normalized left rates approach the upper imaginary unit endpoint. -/
theorem causalUnitBoundaryRate_tendsto_pos :
    Tendsto (fun b : ℝ => (causalUnitBoundaryRate b 1).val) atBot (𝓝 I) := by
  have h : Tendsto (fun b : ℝ => (causalBoundaryRate b 1).val) atBot (𝓝 I) := by
    simpa only [Complex.ofReal_one, one_mul] using boundary_rate_tendsto 1
  have hn : Tendsto (fun b : ℝ => (‖(causalBoundaryRate b 1).val‖ : ℂ)) atBot (𝓝 1) := by
    simpa only [Function.comp_def, Complex.norm_I, Complex.ofReal_one] using!
      (Complex.continuous_ofReal.tendsto ‖I‖).comp h.norm
  have hd := h.div hn (one_ne_zero : (1 : ℂ) ≠ 0)
  simpa only [causalUnitBoundaryRate, Pi.div_apply, div_one] using! hd

/-- Genuine normalized left rates approach the lower imaginary unit endpoint. -/
theorem causalUnitBoundaryRate_tendsto_neg :
    Tendsto (fun b : ℝ => (causalUnitBoundaryRate b (-1)).val) atBot (𝓝 (-I)) := by
  have h : Tendsto (fun b : ℝ => (causalBoundaryRate b (-1)).val) atBot (𝓝 (-I)) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul] using boundary_rate_tendsto (-1)
  have hn : Tendsto (fun b : ℝ => (‖(causalBoundaryRate b (-1)).val‖ : ℂ)) atBot (𝓝 1) := by
    simpa only [Function.comp_def, norm_neg, Complex.norm_I, Complex.ofReal_one] using!
      (Complex.continuous_ofReal.tendsto ‖-I‖).comp h.norm
  have hd := h.div hn (one_ne_zero : (1 : ℂ) ≠ 0)
  simpa only [causalUnitBoundaryRate, Pi.div_apply, div_one] using! hd

/-- A normalized genuine domain eigenvector at the actual unit rate. -/
def causalUnitBoundaryEigenvector (b ω : ℝ) : causalGeneratorDomain :=
  ((‖causalLeftEigenvector (causalUnitBoundaryRate b ω)‖ : ℝ) : ℂ)⁻¹ •
    causalLeftEigenvector (causalUnitBoundaryRate b ω)

/-- The actual rational test datum has unit Hilbert norm. -/
theorem norm_causalUnitBoundaryEigenvector (b ω : ℝ) : ‖causalUnitBoundaryEigenvector b ω‖ = 1 := by
  have hn := norm_ne_zero_iff.mpr (causalLeftEigenvector_ne_zero (causalUnitBoundaryRate b ω))
  rw [causalUnitBoundaryEigenvector, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]

/-- Normalization retains the exact actual maximal-generator eigenvalue. -/
theorem causalGenerator_unitBoundaryEigenvector (b ω : ℝ) :
    causalGenerator (causalUnitBoundaryEigenvector b ω) =
      (causalUnitBoundaryRate b ω).val • (causalUnitBoundaryEigenvector b ω).val := by
  change causalGenerator (_ • causalLeftEigenvector (causalUnitBoundaryRate b ω)) = _
  rw [map_smul, causalGenerator_leftEigenvector]
  change _ • ((causalUnitBoundaryRate b ω).val • _) =
    (causalUnitBoundaryRate b ω).val • (_ • _)
  exact smul_comm _ _ _

end
end RHTower.FokasLenells

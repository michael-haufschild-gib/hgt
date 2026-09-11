import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyChart
import Mathlib.Topology.Homeomorph.Defs

/-! Intrinsic scalar coordinates for actual unit generator rates. The scalar rate
chart is a homeomorphism; no continuity of bounded eigenchains is asserted. -/
open Complex Set Topology
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The intrinsic space of unit generator rates with strictly negative real part. -/
def causalUnitFrequency : Set ℂ := {z | z.re < 0 ∧ ‖z‖ = 1}

/-- Actual normalized generator rates, carrying their exact intrinsic constraints. -/
def causalUnitFrequencyRate (b ω : ℝ) : causalUnitFrequency :=
  ⟨(causalUnitBoundaryRate b ω).val,
    (causalUnitBoundaryRate b ω).property, norm_causalUnitBoundaryRate b ω⟩

/-- Real frequency recovered from an intrinsic unit rate in the damping chart `b`. -/
def causalUnitFrequencyCoordinate (b : ℝ) (z : causalUnitFrequency) : ℝ :=
  -Real.exp b * z.val.im / z.val.re

private theorem raw_ne_zero (b ω : ℝ) : (causalBoundaryRate b ω).val ≠ 0 := by
  intro h
  exact (ne_of_lt (causalBoundaryRate b ω).property) (congrArg Complex.re h)

/-- Recovering the coordinate of an actual rate returns its original frequency. -/
theorem causalUnitFrequencyCoordinate_rate (b ω : ℝ) :
    causalUnitFrequencyCoordinate b (causalUnitFrequencyRate b ω) = ω := by
  change -Real.exp b * (causalUnitBoundaryRate b ω).val.im /
    (causalUnitBoundaryRate b ω).val.re = ω
  rw [causalUnitBoundaryRate_im, causalUnitBoundaryRate_re]
  have hn := norm_ne_zero_iff.mpr (raw_ne_zero b ω)
  field_simp [hn, Real.exp_ne_zero b]

private theorem raw_coordinate (b : ℝ) (z : causalUnitFrequency) :
    (causalBoundaryRate b (causalUnitFrequencyCoordinate b z)).val =
      ((-Real.exp b / z.val.re : ℝ) : ℂ) * z.val := by
  apply Complex.ext
  · change (-(Real.exp b : ℂ) + (causalUnitFrequencyCoordinate b z : ℂ) * I).re = _
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
      add_zero]
    exact (div_mul_cancel₀ (-Real.exp b) (ne_of_lt z.property.1)).symm
  · change (-(Real.exp b : ℂ) + (causalUnitFrequencyCoordinate b z : ℂ) * I).im = _
    simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
      mul_zero, add_zero, zero_add, zero_mul, causalUnitFrequencyCoordinate]
    ring

/-- Every intrinsic unit rate is realized exactly by its explicit real coordinate. -/
theorem causalUnitFrequencyRate_coordinate (b : ℝ) (z : causalUnitFrequency) :
    causalUnitFrequencyRate b (causalUnitFrequencyCoordinate b z) = z := by
  apply Subtype.ext
  change (causalBoundaryRate b (causalUnitFrequencyCoordinate b z)).val /
    (‖(causalBoundaryRate b (causalUnitFrequencyCoordinate b z)).val‖ : ℂ) = z.val
  rw [raw_coordinate, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (div_pos_of_neg_of_neg
      (neg_neg_of_pos (Real.exp_pos b)) z.property.1).le, z.property.2, mul_one]
  simpa only [mul_one, div_one] using
    (mul_div_mul_left z.val (1 : ℂ) (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (div_pos_of_neg_of_neg (neg_neg_of_pos (Real.exp_pos b)) z.property.1))))

/-- Scalar normalization varies continuously with the actual real frequency. -/
theorem continuous_causalUnitFrequencyRate (b : ℝ) :
    Continuous (causalUnitFrequencyRate b) := by
  have hr : Continuous (fun ω : ℝ => (causalBoundaryRate b ω).val) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have h := hr.div (Complex.continuous_ofReal.comp hr.norm)
    (fun ω => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (raw_ne_zero b ω)))
  exact h.subtype_mk (fun ω => (causalUnitFrequencyRate b ω).property)

/-- The explicit inverse chart is continuous on the entire intrinsic rate carrier. -/
theorem continuous_causalUnitFrequencyCoordinate (b : ℝ) :
    Continuous (causalUnitFrequencyCoordinate b) := by
  exact (continuous_const.mul (Complex.continuous_im.comp continuous_subtype_val)).div
    (Complex.continuous_re.comp continuous_subtype_val) (fun z => ne_of_lt z.property.1)

/-- Every damping chart identifies the real line with the intrinsic unit-rate space. -/
def causalUnitFrequencyHomeomorph (b : ℝ) : ℝ ≃ₜ causalUnitFrequency where
  toEquiv :=
    { toFun := causalUnitFrequencyRate b
      invFun := causalUnitFrequencyCoordinate b
      left_inv := causalUnitFrequencyCoordinate_rate b
      right_inv := causalUnitFrequencyRate_coordinate b }
  continuous_toFun := continuous_causalUnitFrequencyRate b
  continuous_invFun := continuous_causalUnitFrequencyCoordinate b

/-- The actual normalized-rate range is exactly the open left unit semicircle. -/
theorem causalUnitBoundaryRate_range (b : ℝ) :
    Set.range (fun ω : ℝ => (causalUnitBoundaryRate b ω).val) = causalUnitFrequency := by
  ext z
  constructor
  · rintro ⟨ω, rfl⟩
    exact (causalUnitFrequencyRate b ω).property
  · intro hz
    exact ⟨causalUnitFrequencyCoordinate b ⟨z, hz⟩,
      congrArg Subtype.val (causalUnitFrequencyRate_coordinate b ⟨z, hz⟩)⟩

/-- Changing damping charts rescales the real coordinate by the exact positive factor. -/
theorem causalUnitFrequencyHomeomorph_relabel (b c ω : ℝ) :
    (causalUnitFrequencyHomeomorph c).symm (causalUnitFrequencyHomeomorph b ω) =
      Real.exp (c - b) * ω := by
  have hr : causalUnitFrequencyRate c (Real.exp (c - b) * ω) =
      causalUnitFrequencyRate b ω := by
    apply Subtype.ext
    exact congrArg (fun z : {z : ℂ // z.re < 0} => z.val)
      (causalUnitBoundaryRate_rescale b c ω)
  have hc := congrArg (causalUnitFrequencyCoordinate c) hr
  rw [causalUnitFrequencyCoordinate_rate] at hc
  exact hc.symm

end
end RHTower.FokasLenells

import GaloisForLFunctions.HTGeometry.ComplexAnalysis.HolomorphicL2Flatness
import GaloisForLFunctions.SelbergClass.MultipleStandardTwistGammaClearing

/-!
# Flat lines of reciprocal-Gamma denominators

An affine reciprocal-Gamma function is locally L² flat precisely when its affine argument is
constant at a nonpositive integer. Applied to the denominators of multiple standard twists,
this says that the flat complex lines are exactly the lines contained in a Gamma zero
hyperplane. Transverse lines never have infinite-order local squared-mass vanishing.
-/

open Complex Set

namespace GaloisForLFunctions.SelbergClass

open GaloisForLFunctions.HTGeometry

/-- Exact classification of infinite-order local mass vanishing for affine reciprocal Gamma. -/
theorem l2FlatAt_reciprocalGamma_affine_iff (a b c : ℂ) :
    L2FlatAt (fun w => (Complex.Gamma (a * w + b))⁻¹) c ↔
      a = 0 ∧ ∃ n : ℕ, b = -(n : ℂ) := by
  have hf : AnalyticOnNhd ℂ (fun w => (Complex.Gamma (a * w + b))⁻¹) univ := by
    have hGamma : AnalyticOnNhd ℂ (fun s => (Complex.Gamma s)⁻¹) univ :=
      Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ
    intro w _
    exact (hGamma (a * w + b) (mem_univ _)).comp
      ((analyticAt_const.mul analyticAt_id).add analyticAt_const)
  rw [l2FlatAt_iff_eq_zero_of_entire hf]
  constructor
  · intro hzero
    have ha : a = 0 := by
      by_contra ha
      have hz := congrFun hzero ((1 - b) / a)
      have heq : a * ((1 - b) / a) + b = 1 := by field_simp; ring
      simp only [heq, Complex.Gamma_one, inv_one, Pi.zero_apply] at hz
      exact one_ne_zero hz
    refine ⟨ha, ?_⟩
    have hb := congrFun hzero 0
    simpa only [mul_zero, zero_add, Pi.zero_apply, inv_eq_zero,
      Complex.Gamma_eq_zero_iff] using hb
  · rintro ⟨rfl, n, hn⟩
    funext w
    simp only [zero_mul, zero_add, Pi.zero_apply, inv_eq_zero]
    exact Complex.Gamma_eq_zero_iff.mpr ⟨n, hn⟩

/-- A slice of a multiple-twist denominator is flat exactly along a contained zero hyperplane. -/
theorem l2FlatAt_reciprocalGammaAffineEntire_line_iff
    (N : ℕ) (L : (Fin N → ℂ) →L[ℂ] ℂ) (b : ℂ)
    (x v : Fin N → ℂ) (c : ℂ) :
    L2FlatAt (fun w => reciprocalGammaAffineEntire N L b (x + w • v)) c ↔
      L v = 0 ∧ ∃ n : ℕ, L x + b = -(n : ℂ) := by
  have heq : (fun w => reciprocalGammaAffineEntire N L b (x + w • v)) =
      fun w => (Complex.Gamma (L v * w + (L x + b)))⁻¹ := by
    funext w
    change (Complex.Gamma (L (x + w • v) + b))⁻¹ = _
    rw [map_add, map_smul, smul_eq_mul]
    congr 2
    ring
  rw [heq, l2FlatAt_reciprocalGamma_affine_iff]

end GaloisForLFunctions.SelbergClass

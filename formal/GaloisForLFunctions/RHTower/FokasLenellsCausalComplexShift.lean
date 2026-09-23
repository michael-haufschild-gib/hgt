import GaloisForLFunctions.RHTower.FokasLenellsCausalSharpResolvent

/-! Complex shifts of the actual maximal causal generator. The paper's causal Cauchy evolution
has a dissipative completion; this identifies its coercive open right half-plane directly. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
local instance fokasLenellsCausalComplexShiftInst1 : InnerProductSpace ℝ (hardyL2ᗮ) :=
  InnerProductSpace.rclikeToReal ℂ (hardyL2ᗮ)

/-- Complex spectral shift on the actual unchanged maximal generator domain. -/
def causalComplexGeneratorShift (z : ℂ) : causalGeneratorDomain →ₗ[ℂ] hardyL2ᗮ :=
  z • causalGeneratorDomain.subtype - causalGenerator

/-- The previously constructed positive shifts are the real restrictions of the complex family. -/
theorem causalComplexGeneratorShift_positive (a : ℝ) :
    causalComplexGeneratorShift (Real.exp a : ℂ) = causalGeneratorShift a := rfl

/-- Dissipation controls the real part of the actual complex generator pairing. -/
theorem causalGenerator_re_inner_nonpos (u : causalGeneratorDomain) :
    (inner ℂ u.val (causalGenerator u)).re ≤ 0 := by
  exact causalGenerator_dissipative u

/-- The actual shifted energy pairing separates damping from generator dissipation. -/
theorem causalComplexGeneratorShift_re_inner (z : ℂ) (u : causalGeneratorDomain) :
    (inner ℂ u.val (causalComplexGeneratorShift z u)).re =
      z.re * ‖u.val‖^(2 : ℕ) - (inner ℂ u.val (causalGenerator u)).re := by
  change (inner ℂ u.val (z • u.val - causalGenerator u)).re = _
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
  change (z * ((‖u.val‖ : ℝ) : ℂ)^(2 : ℕ) - inner ℂ u.val (causalGenerator u)).re = _
  simp only [← Complex.ofReal_pow, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

/-- Every point of the open right half-plane gives a quantitative lower bound in the data norm. -/
theorem causalComplexGeneratorShift_norm_lowerBound (z : {z : ℂ // 0 < z.re})
    (u : causalGeneratorDomain) :
    z.val.re * ‖u.val‖ ≤ ‖causalComplexGeneratorShift z.val u‖ := by
  have he := causalComplexGeneratorShift_re_inner z.val u
  have hd := causalGenerator_re_inner_nonpos u
  have hc := re_inner_le_norm (𝕜 := ℂ) u.val (causalComplexGeneratorShift z.val u)
  change (inner ℂ u.val (causalComplexGeneratorShift z.val u)).re ≤
    ‖u.val‖ * ‖causalComplexGeneratorShift z.val u‖ at hc
  by_cases hu : ‖u.val‖ = 0
  · simp only [hu, mul_zero]
    exact norm_nonneg _
  have hp : 0 < ‖u.val‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
  nlinarith

/-- The actual complex generator shift is injective throughout the open right half-plane. -/
theorem causalComplexGeneratorShift_injective (z : {z : ℂ // 0 < z.re}) :
    Function.Injective (causalComplexGeneratorShift z.val) := by
  intro u v h
  have hb := causalComplexGeneratorShift_norm_lowerBound z (u-v)
  rw [map_sub, h, sub_self, norm_zero] at hb
  have hn : ‖u.val-v.val‖ = 0 := by
    change z.val.re * ‖u.val-v.val‖ ≤ 0 at hb
    nlinarith [norm_nonneg (u.val-v.val), z.property]
  exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp hn))

end
end RHTower.FokasLenells

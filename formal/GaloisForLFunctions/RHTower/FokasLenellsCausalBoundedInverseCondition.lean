import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedSharpGrowth

/-! Exact forward/inverse amplification of the genuine entire bounded-chain automorphism. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance fokasLenellsCausalBoundedInverseConditionInst1 : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance fokasLenellsCausalBoundedInverseConditionInst2 : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance fokasLenellsCausalBoundedInverseConditionInst3 : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance fokasLenellsCausalBoundedInverseConditionInst4 : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance fokasLenellsCausalBoundedInverseConditionInst5 : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance fokasLenellsCausalBoundedInverseConditionInst6 : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance fokasLenellsCausalBoundedInverseConditionInst7 : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing


/-- The actual continuous inverse is evolution by negative complex time. -/
theorem causalBoundedEntireGroup_inverse (z : ℂ) :
    (causalBoundedEntireGroup z).symm.toContinuousLinearMap =
      causalBoundedChainExponential (-z) := by
  ext u
  rfl

/-- The condition number uses the actual forward and inverse continuous operators. -/
def causalBoundedEntireCondition (z : ℂ) : ℝ :=
  ‖(causalBoundedEntireGroup z).toContinuousLinearMap‖ *
    ‖(causalBoundedEntireGroup z).symm.toContinuousLinearMap‖

private theorem norm_of_zero_real (z : ℂ) (hz : z.re = 0) : ‖z‖ = |z.im| := by
  have he : z = (z.im : ℂ)*I := by
    have h := Complex.re_add_im z
    simpa only [hz, Complex.ofReal_zero, zero_add] using h.symm
  exact (congrArg (fun w : ℂ => ‖w‖) he).trans
    (by rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs])

/-- Forward and reverse sharp exponents add to the norm plus the imaginary displacement. -/
theorem causalBoundedGrowthExponent_add_neg (z : ℂ) :
    causalBoundedGrowthExponent z + causalBoundedGrowthExponent (-z) = ‖z‖ + |z.im| := by
  by_cases hp : 0 < z.re
  · simp only [causalBoundedGrowthExponent, Complex.neg_re, Complex.neg_im, norm_neg,
      if_pos (le_of_lt hp), if_neg (not_le.mpr (neg_lt_zero.mpr hp)), add_comm]
  · by_cases hn : z.re < 0
    · simp only [causalBoundedGrowthExponent, Complex.neg_re, Complex.neg_im, norm_neg,
        if_neg (not_le.mpr hn), if_pos (le_of_lt (neg_pos.mpr hn)), abs_neg]
    · have hz : z.re = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
      simp only [causalBoundedGrowthExponent, hz, Complex.neg_re, Complex.neg_im, neg_zero,
        if_pos (le_refl (0 : ℝ)), abs_neg, norm_of_zero_real z hz]

/-- Exact inverse operator norm at every complex time. -/
theorem norm_causalBoundedEntireGroup_inverse (z : ℂ) :
    ‖(causalBoundedEntireGroup z).symm.toContinuousLinearMap‖ =
      Real.exp (causalBoundedGrowthExponent (-z)) :=
  (congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    (causalBoundedEntireGroup_inverse z)).trans (norm_causalBoundedChainExponential (-z))

/-- The exact condition number records the price of reversibility on the genuine chain space. -/
theorem causalBoundedEntireCondition_eq (z : ℂ) :
    causalBoundedEntireCondition z = Real.exp (‖z‖ + |z.im|) := by
  change ‖causalBoundedChainExponential z‖ * ‖causalBoundedChainExponential (-z)‖ = _
  have he := congrArg₂ (fun a b : ℝ => a*b)
    (norm_causalBoundedChainExponential z) (norm_causalBoundedChainExponential (-z))
  exact he.trans ((Real.exp_add _ _).symm.trans
    (congrArg Real.exp (causalBoundedGrowthExponent_add_neg z)))

/-- Real-time reversal costs exactly exponential growth in the absolute elapsed time. -/
theorem causalBoundedEntireCondition_real (r : ℝ) :
    causalBoundedEntireCondition (r : ℂ) = Real.exp |r| := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_im, abs_zero, add_zero]
    using causalBoundedEntireCondition_eq (r : ℂ)

/-- Imaginary time doubles the exponent in the forward/inverse condition number. -/
theorem causalBoundedEntireCondition_imaginary (r : ℝ) :
    causalBoundedEntireCondition ((r : ℂ)*I) = Real.exp (2*|r|) := by
  have he : ‖(r : ℂ)*I‖ + |((r : ℂ)*I).im| = 2*|r| := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re,
      mul_zero, add_zero]
    ring
  exact (causalBoundedEntireCondition_eq ((r : ℂ)*I)).trans (congrArg Real.exp he)

/-- Every complex displacement pays at least the exponential of its length in condition number. -/
theorem causalBoundedEntireCondition_lower (z : ℂ) :
    Real.exp ‖z‖ ≤ causalBoundedEntireCondition z :=
  (Real.exp_le_exp.mpr (le_add_of_nonneg_right (abs_nonneg z.im))).trans_eq
    (causalBoundedEntireCondition_eq z).symm

/-- The exact condition number is at most the exponential of twice the displacement length. -/
theorem causalBoundedEntireCondition_upper (z : ℂ) :
    causalBoundedEntireCondition z ≤ Real.exp (2*‖z‖) := by
  have h : ‖z‖ + |z.im| ≤ 2*‖z‖ := by nlinarith only [Complex.abs_im_le_norm z]
  exact (causalBoundedEntireCondition_eq z).trans_le (Real.exp_le_exp.mpr h)

/-- Perfect conditioning occurs precisely at zero complex time. -/
theorem causalBoundedEntireCondition_eq_one_iff (z : ℂ) :
    causalBoundedEntireCondition z = 1 ↔ z = 0 := by
  constructor
  · intro h
    have he : Real.exp (‖z‖ + |z.im|) = 1 := (causalBoundedEntireCondition_eq z).symm.trans h
    have hs := (Real.exp_eq_one_iff _).mp he
    have hn : ‖z‖ = 0 := by nlinarith only [norm_nonneg z, abs_nonneg z.im, hs]
    exact Complex.norm_eq_zero_iff.mp hn
  · intro h
    subst z
    simpa only [norm_zero, Complex.zero_im, abs_zero, add_zero, Real.exp_zero]
      using causalBoundedEntireCondition_eq (0 : ℂ)

/-- The exact reverse growth bounds reconstruction of every actual chain from its evolved state. -/
theorem causalBoundedChainExponential_reconstruction_bound (z : ℂ) (u : causalBoundedChain) :
    ‖u‖ ≤ Real.exp (causalBoundedGrowthExponent (-z)) * ‖causalBoundedChainExponential z u‖ := by
  have he := congrArg (fun v : causalBoundedChain => ‖v‖)
    (causalBoundedChainExponential_neg_apply z u)
  have hn := congrArg (fun r : ℝ => r * ‖causalBoundedChainExponential z u‖)
    (norm_causalBoundedChainExponential (-z))
  exact he.symm.trans_le (((causalBoundedChainExponential (-z)).le_opNorm _).trans_eq hn)

end
end RHTower.FokasLenells

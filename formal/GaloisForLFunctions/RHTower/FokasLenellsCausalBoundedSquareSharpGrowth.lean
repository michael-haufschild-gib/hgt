import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedSquareExponential

/-! Sharp isotropic complex growth and exact inverse conditioning for the actual second-derivative evolution. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


open ComplexConjugate
local instance : NormedAlgebra ℚ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  .restrictScalars ℚ ℂ _

private theorem square_aligned_rate_norm (z : ℂ) (hz : z ≠ 0) :
    ‖conj z / (‖z‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    div_self (norm_ne_zero_iff.mpr hz)]

private theorem square_aligned_character (z : ℂ) (hz : z ≠ 0) :
    (z*(conj z / (‖z‖ : ℂ))).re = ‖z‖ := by
  have hn := norm_ne_zero_iff.mpr hz
  calc
    _ = (z*conj z).re / ‖z‖ := by rw [← mul_div_assoc, Complex.div_ofReal_re]
    _ = ‖z‖^2 / ‖z‖ := by rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    _ = ‖z‖ * (‖z‖/‖z‖) := by rw [pow_two, mul_div_assoc]
    _ = ‖z‖ := by rw [div_self hn, mul_one]

/-- The actual second-derivative evolution has exact exponential norm in every complex-time direction. -/
theorem norm_causalBoundedSquareExponential (z : ℂ) :
    ‖causalBoundedSquareExponential z‖ = Real.exp ‖z‖ := by
  apply le_antisymm (norm_causalBoundedSquareExponential_le z)
  by_cases hz : z = 0
  · simp only [hz, norm_zero, Real.exp_zero, causalBoundedSquareExponential_zero, norm_one, le_refl]
  · have hr : conj z / (‖z‖ : ℂ) ∈ spectrum ℂ (causalBoundedChainShift^2) :=
      (causalBoundedChainShift_square_mem_spectrum_iff _).mpr (square_aligned_rate_norm z hz).le
    have hs : z*(conj z / (‖z‖ : ℂ)) ∈ spectrum ℂ (z • causalBoundedChainShift^2) := by
      simpa only [Units.smul_def, Units.val_mk0, smul_eq_mul] using!
        (spectrum.smul_mem_smul_iff (r := Units.mk0 z hz) (a := causalBoundedChainShift^2)).mpr hr
    have hm : Complex.exp (z*(conj z / (‖z‖ : ℂ))) ∈ spectrum ℂ (causalBoundedSquareExponential z) := by
      simpa only [← Complex.exp_eq_exp_ℂ] using!
        spectrum.exp_mem_exp (z • causalBoundedChainShift^2) hs
    have hn : ‖Complex.exp (z*(conj z / (‖z‖ : ℂ)))‖ = Real.exp ‖z‖ :=
      (Complex.norm_exp _).trans (congrArg Real.exp (square_aligned_character z hz))
    exact hn.symm.trans_le (spectrum.norm_le_norm_of_mem hm)

/-- Both real time directions grow at the same sharp exponential rate for the genuine second derivative. -/
theorem norm_causalBoundedSquareExponential_real (r : ℝ) :
    ‖causalBoundedSquareExponential (r : ℂ)‖ = Real.exp |r| := by
  simpa only [Complex.norm_real, Real.norm_eq_abs] using norm_causalBoundedSquareExponential (r : ℂ)

/-- Pure imaginary second-derivative time also has exact exponential norm growth. -/
theorem norm_causalBoundedSquareExponential_imaginary (r : ℝ) :
    ‖causalBoundedSquareExponential ((r : ℂ)*I)‖ = Real.exp |r| := by
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    using norm_causalBoundedSquareExponential ((r : ℂ)*I)

/-- The actual second-derivative exponential obeys the complex additive group law. -/
theorem causalBoundedSquareExponential_add (z w : ℂ) :
    causalBoundedSquareExponential (z+w) = causalBoundedSquareExponential z * causalBoundedSquareExponential w := by
  have he : (z+w) • causalBoundedChainShift^2 =
      z • causalBoundedChainShift^2 + w • causalBoundedChainShift^2 := add_smul z w _
  exact (congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => NormedSpace.exp A) he).trans
    (NormedSpace.exp_add_of_commute (((Commute.refl (causalBoundedChainShift^2)).smul_left z).smul_right w))

/-- Negative complex time recovers every genuine chain from its second-derivative evolution. -/
theorem causalBoundedSquareExponential_neg_apply (z : ℂ) (u : causalBoundedChain) :
    causalBoundedSquareExponential (-z) (causalBoundedSquareExponential z u) = u := by
  have h := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u)
    (causalBoundedSquareExponential_add (-z) z)
  have hz : causalBoundedSquareExponential 0 u = u :=
    congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u) causalBoundedSquareExponential_zero
  have hs : causalBoundedSquareExponential (-z+z) u = u :=
    (congrArg (fun q : ℂ => causalBoundedSquareExponential q u) (neg_add_cancel z)).trans hz
  exact h.symm.trans hs

/-- Reversing the composition order also gives the actual identity. -/
theorem causalBoundedSquareExponential_apply_neg (z : ℂ) (u : causalBoundedChain) :
    causalBoundedSquareExponential z (causalBoundedSquareExponential (-z) u) = u := by
  simpa only [neg_neg] using causalBoundedSquareExponential_neg_apply (-z) u

/-- The actual second-derivative evolution is a continuous linear automorphism at every complex time. -/
def causalBoundedSquareEntireGroup (z : ℂ) : causalBoundedChain ≃L[ℂ] causalBoundedChain where
  toLinearMap := (causalBoundedSquareExponential z).toLinearMap
  invFun := causalBoundedSquareExponential (-z)
  left_inv := causalBoundedSquareExponential_neg_apply z
  right_inv := causalBoundedSquareExponential_apply_neg z
  continuous_toFun := (causalBoundedSquareExponential z).continuous
  continuous_invFun := (causalBoundedSquareExponential (-z)).continuous

/-- Conditioning measured using the genuine forward and inverse second-derivative operators. -/
def causalBoundedSquareEntireCondition (z : ℂ) : ℝ :=
  ‖(causalBoundedSquareEntireGroup z).toContinuousLinearMap‖ *
    ‖(causalBoundedSquareEntireGroup z).symm.toContinuousLinearMap‖

/-- Actual second-derivative inverse conditioning has exact doubled radial exponential growth. -/
theorem causalBoundedSquareEntireCondition_eq (z : ℂ) :
    causalBoundedSquareEntireCondition z = Real.exp (2*‖z‖) := by
  change ‖causalBoundedSquareExponential z‖ * ‖causalBoundedSquareExponential (-z)‖ = _
  have he := congrArg₂ (fun a b : ℝ => a*b)
    (norm_causalBoundedSquareExponential z) (norm_causalBoundedSquareExponential (-z))
  have hn : ‖z‖ + ‖-z‖ = 2*‖z‖ := by rw [norm_neg]; ring
  exact he.trans ((Real.exp_add _ _).symm.trans (congrArg Real.exp hn))

end
end RHTower.FokasLenells

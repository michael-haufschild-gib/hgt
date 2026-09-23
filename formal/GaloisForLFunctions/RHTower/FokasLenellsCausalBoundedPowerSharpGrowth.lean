import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedPowerExponential

/-! Sharp isotropic complex growth and exact inverse conditioning for the actual higher-derivative evolution. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalPowerSharpLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalPowerSharpChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalPowerSharpChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalPowerSharpChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalPowerSharpEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance causalPowerSharpEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalPowerSharpEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance causalPowerSharpEndNormedAlgebra : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance causalPowerSharpEndNormOne : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


open ComplexConjugate
local instance causalPowerSharpEndRationalAlgebra : NormedAlgebra ℚ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  .restrictScalars ℚ ℂ _

private theorem power_aligned_rate_norm (z : ℂ) (hz : z ≠ 0) :
    ‖conj z / (‖z‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    div_self (norm_ne_zero_iff.mpr hz)]

private theorem power_aligned_character (z : ℂ) (hz : z ≠ 0) :
    (z*(conj z / (‖z‖ : ℂ))).re = ‖z‖ := by
  have hn := norm_ne_zero_iff.mpr hz
  calc
    _ = (z*conj z).re / ‖z‖ := by rw [← mul_div_assoc, Complex.div_ofReal_re]
    _ = ‖z‖^(2 : ℕ) / ‖z‖ := by rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    _ = ‖z‖ * (‖z‖/‖z‖) := by rw [pow_two, mul_div_assoc]
    _ = ‖z‖ := by rw [div_self hn, mul_one]

/-- The actual higher-derivative evolution has exact exponential norm in every complex-time direction. -/
theorem norm_causalBoundedPowerExponential (n : ℕ) (z : ℂ) :
    ‖causalBoundedPowerExponential (n+2) z‖ = Real.exp ‖z‖ := by
  apply le_antisymm (norm_causalBoundedPowerExponential_le (n+2) z)
  by_cases hz : z = 0
  · simp only [hz, norm_zero, Real.exp_zero, causalBoundedPowerExponential_zero, norm_one, le_refl]
  · have hr : conj z / (‖z‖ : ℂ) ∈ spectrum ℂ (causalBoundedChainShift^(n+2)) :=
      (causalBoundedChainShift_higher_mem_spectrum_iff n _).mpr (power_aligned_rate_norm z hz).le
    have hs : z*(conj z / (‖z‖ : ℂ)) ∈ spectrum ℂ (z • causalBoundedChainShift^(n+2)) := by
      simpa only [Units.smul_def, Units.val_mk0, smul_eq_mul] using!
        (spectrum.smul_mem_smul_iff (r := Units.mk0 z hz) (a := causalBoundedChainShift^(n+2))).mpr hr
    have hm : Complex.exp (z*(conj z / (‖z‖ : ℂ))) ∈ spectrum ℂ (causalBoundedPowerExponential (n+2) z) := by
      simpa only [← Complex.exp_eq_exp_ℂ] using!
        spectrum.exp_mem_exp (z • causalBoundedChainShift^(n+2)) hs
    have hn : ‖Complex.exp (z*(conj z / (‖z‖ : ℂ)))‖ = Real.exp ‖z‖ :=
      (Complex.norm_exp _).trans (congrArg Real.exp (power_aligned_character z hz))
    exact hn.symm.trans_le (spectrum.norm_le_norm_of_mem hm)

/-- Both real time directions grow at the same sharp exponential rate for the genuine chosen derivative power. -/
theorem norm_causalBoundedPowerExponential_real (n : ℕ) (r : ℝ) :
    ‖causalBoundedPowerExponential (n+2) (r : ℂ)‖ = Real.exp |r| := by
  simpa only [Complex.norm_real, Real.norm_eq_abs] using norm_causalBoundedPowerExponential n (r : ℂ)

/-- Pure imaginary higher-derivative time also has exact exponential norm growth. -/
theorem norm_causalBoundedPowerExponential_imaginary (n : ℕ) (r : ℝ) :
    ‖causalBoundedPowerExponential (n+2) ((r : ℂ)*I)‖ = Real.exp |r| := by
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    using norm_causalBoundedPowerExponential n ((r : ℂ)*I)

/-- The actual higher-derivative exponential obeys the complex additive group law. -/
theorem causalBoundedPowerExponential_add (m : ℕ) (z w : ℂ) :
    causalBoundedPowerExponential m (z+w) = causalBoundedPowerExponential m z * causalBoundedPowerExponential m w := by
  have he : (z+w) • causalBoundedChainShift^m =
      z • causalBoundedChainShift^m + w • causalBoundedChainShift^m := add_smul z w _
  exact (congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => NormedSpace.exp A) he).trans
    (NormedSpace.exp_add_of_commute (((Commute.refl (causalBoundedChainShift^m)).smul_left z).smul_right w))

/-- Negative complex time recovers every genuine chain from its higher-derivative evolution. -/
theorem causalBoundedPowerExponential_neg_apply (m : ℕ) (z : ℂ) (u : causalBoundedChain) :
    causalBoundedPowerExponential m (-z) (causalBoundedPowerExponential m z u) = u := by
  have h := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u)
    (causalBoundedPowerExponential_add m (-z) z)
  have hz : causalBoundedPowerExponential m 0 u = u :=
    congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u) (causalBoundedPowerExponential_zero m)
  have hs : causalBoundedPowerExponential m (-z+z) u = u :=
    (congrArg (fun q : ℂ => causalBoundedPowerExponential m q u) (neg_add_cancel z)).trans hz
  exact h.symm.trans hs

/-- Reversing the composition order also gives the actual identity. -/
theorem causalBoundedPowerExponential_apply_neg (m : ℕ) (z : ℂ) (u : causalBoundedChain) :
    causalBoundedPowerExponential m z (causalBoundedPowerExponential m (-z) u) = u := by
  simpa only [neg_neg] using causalBoundedPowerExponential_neg_apply m (-z) u

/-- The actual higher-derivative evolution is a continuous linear automorphism at every complex time. -/
def causalBoundedPowerEntireGroup (m : ℕ) (z : ℂ) : causalBoundedChain ≃L[ℂ] causalBoundedChain where
  toLinearMap := (causalBoundedPowerExponential m z).toLinearMap
  invFun := causalBoundedPowerExponential m (-z)
  left_inv := causalBoundedPowerExponential_neg_apply m z
  right_inv := causalBoundedPowerExponential_apply_neg m z
  continuous_toFun := (causalBoundedPowerExponential m z).continuous
  continuous_invFun := (causalBoundedPowerExponential m (-z)).continuous

/-- Conditioning measured using the genuine forward and inverse higher-derivative operators. -/
def causalBoundedPowerEntireCondition (m : ℕ) (z : ℂ) : ℝ :=
  ‖(causalBoundedPowerEntireGroup m z).toContinuousLinearMap‖ *
    ‖(causalBoundedPowerEntireGroup m z).symm.toContinuousLinearMap‖

/-- Actual higher-derivative inverse conditioning has exact doubled radial exponential growth. -/
theorem causalBoundedPowerEntireCondition_eq (n : ℕ) (z : ℂ) :
    causalBoundedPowerEntireCondition (n+2) z = Real.exp (2*‖z‖) := by
  change ‖causalBoundedPowerExponential (n+2) z‖ * ‖causalBoundedPowerExponential (n+2) (-z)‖ = _
  have he := congrArg₂ (fun a b : ℝ => a*b)
    (norm_causalBoundedPowerExponential n z) (norm_causalBoundedPowerExponential n (-z))
  have hn : ‖z‖ + ‖-z‖ = 2*‖z‖ := by rw [norm_neg]; ring
  exact he.trans ((Real.exp_add _ _).symm.trans (congrArg Real.exp hn))

end
end RHTower.FokasLenells

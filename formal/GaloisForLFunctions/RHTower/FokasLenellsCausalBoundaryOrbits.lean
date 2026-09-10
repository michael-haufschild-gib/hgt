import GaloisForLFunctions.RHTower.FokasLenellsCausalSharpComplexResolvent

/-! Exact evolution and resolvent action on the actual rational boundary test vectors. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- Every actual left-half-plane eigenvector has its exact exponential causal orbit. -/
theorem causalLowerCauchyEvolution_leftEigenvector (t : ℝ≥0) (w : {z : ℂ // z.re < 0}) :
    causalLowerCauchyEvolution t (causalLeftEigenvector w).val =
      Complex.exp (((t : ℝ) : ℂ)*w.val) • (causalLeftEigenvector w).val := by
  change causalLowerCauchyEvolution t (causalCauchyEigenvector (causalEigenPole w)) = _
  rw [causalLowerCauchyEvolution_eigenvector, causalAnalyticPhase_rate, causalPoleRate_eigenPole]
  rfl

/-- Normalized rational boundary vectors retain their exact exponential orbit. -/
theorem causalLowerCauchyEvolution_boundaryEigenvector (t : ℝ≥0) (b ω : ℝ) :
    causalLowerCauchyEvolution t (causalBoundaryEigenvector b ω).val =
      Complex.exp (((t : ℝ) : ℂ)*(causalBoundaryRate b ω).val) •
        (causalBoundaryEigenvector b ω).val := by
  change causalLowerCauchyEvolution t (_ • (causalLeftEigenvector (causalBoundaryRate b ω)).val) = _
  rw [map_smul, causalLowerCauchyEvolution_leftEigenvector]
  exact smul_comm _ _ _

/-- The unit rational boundary orbit loses norm by exactly its positive real damping. -/
theorem norm_causalLowerCauchyEvolution_boundaryEigenvector (t : ℝ≥0) (b ω : ℝ) :
    ‖causalLowerCauchyEvolution t (causalBoundaryEigenvector b ω).val‖ =
      Real.exp (-(t : ℝ)*Real.exp b) := by
  rw [causalLowerCauchyEvolution_boundaryEigenvector, norm_smul, Complex.norm_exp]
  change Real.exp _ * ‖causalBoundaryEigenvector b ω‖ = _
  rw [norm_causalBoundaryEigenvector, mul_one]
  congr 1
  simp only [causalBoundaryRate, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.neg_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero]
  ring

/-- The true maximal-domain resolvent acts on every normalized rational boundary vector. -/
theorem causalComplexResolvent_boundaryEigenvector (z : {z : ℂ // 0 < z.re}) (b ω : ℝ) :
    causalComplexResolvent z (causalBoundaryEigenvector b ω).val =
      (z.val-(causalBoundaryRate b ω).val)⁻¹ • causalBoundaryEigenvector b ω := by
  change causalComplexResolvent z (_ • (causalLeftEigenvector (causalBoundaryRate b ω)).val) = _
  rw [map_smul, causalComplexResolvent_leftEigenvector]
  exact smul_comm _ _ _

end
end RHTower.FokasLenells

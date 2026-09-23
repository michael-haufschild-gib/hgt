import GaloisForLFunctions.RHTower.FokasLenellsCausalSharpResolvent

/-! An explicit positive real resolvent center for every complex point with positive real part. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- A real center whose resolvent disk contains the given open-right-half-plane point. -/
def causalNeumannCenter (z : {z : ℂ // 0 < z.re}) : ℝ :=
  1 + Complex.normSq z.val / (2*z.val.re)

/-- The chosen center is strictly positive for every actual right-half-plane point. -/
theorem causalNeumannCenter_pos (z : {z : ℂ // 0 < z.re}) :
    0 < causalNeumannCenter z := by
  unfold causalNeumannCenter
  have hn := Complex.normSq_nonneg z.val
  have hp := z.property
  positivity

/-- The exact disk condition needed to invert the bounded perturbation of a real resolvent. -/
theorem causalNeumannCenter_distance (z : {z : ℂ // 0 < z.re}) :
    ‖z.val-(causalNeumannCenter z : ℂ)‖ < causalNeumannCenter z := by
  have hp := causalNeumannCenter_pos z
  have hz := z.property
  have hc : 2 * causalNeumannCenter z * z.val.re = 2*z.val.re + Complex.normSq z.val := by
    unfold causalNeumannCenter
    field_simp
  have hd : ‖z.val-(causalNeumannCenter z : ℂ)‖^(2 : ℕ) =
      Complex.normSq z.val - 2 * causalNeumannCenter z * z.val.re +
        (causalNeumannCenter z)^(2 : ℕ) := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    ring
  nlinarith [norm_nonneg (z.val-(causalNeumannCenter z : ℂ))]

/-- Logarithmic parameter for the already constructed positive real Laplace resolvent. -/
def causalNeumannParameter (z : {z : ℂ // 0 < z.re}) : ℝ := Real.log (causalNeumannCenter z)

/-- The real resolvent's exponential damping equals the selected center. -/
theorem exp_causalNeumannParameter (z : {z : ℂ // 0 < z.re}) :
    Real.exp (causalNeumannParameter z) = causalNeumannCenter z :=
  Real.exp_log (causalNeumannCenter_pos z)

/-- The perturbation of the actual positive resolvent, acting on the completed lower Hardy space. -/
def causalNeumannPerturbation (z : {z : ℂ // 0 < z.re}) : hardyL2ᗮ →L[ℂ] hardyL2ᗮ :=
  (z.val-(causalNeumannCenter z : ℂ)) • causalLaplaceIntegral (causalNeumannParameter z)

/-- The explicit complex perturbation is strictly contractive, without a smallness assumption. -/
theorem norm_causalNeumannPerturbation_lt_one (z : {z : ℂ // 0 < z.re}) :
    ‖causalNeumannPerturbation z‖ < 1 := by
  have hp := causalNeumannCenter_pos z
  have hd := causalNeumannCenter_distance z
  calc ‖causalNeumannPerturbation z‖
      ≤ ‖z.val-(causalNeumannCenter z : ℂ)‖ *
        ‖causalLaplaceIntegral (causalNeumannParameter z)‖ := by
          exact ContinuousLinearMap.opNorm_smul_le (z.val-(causalNeumannCenter z : ℂ))
            (causalLaplaceIntegral (causalNeumannParameter z))
    _ = ‖z.val-(causalNeumannCenter z : ℂ)‖ * (causalNeumannCenter z)⁻¹ := by
      rw [norm_causalLaplaceIntegral, exp_causalNeumannParameter]
    _ < causalNeumannCenter z * (causalNeumannCenter z)⁻¹ :=
        mul_lt_mul_of_pos_right hd (inv_pos.mpr hp)
    _ = 1 := mul_inv_cancel₀ hp.ne'

end
end RHTower.FokasLenells

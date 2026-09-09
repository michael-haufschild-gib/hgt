import GaloisForLFunctions.RHTower.FokasLenellsCausalGeneratorEigenvectors
import GaloisForLFunctions.RHTower.FokasLenellsCausalResolvent

/-!
# Exact action and sharp norm of actual positive causal resolvents

Every rational generator eigenvector remains an eigenvector of the actual
Laplace resolvent, with the expected reciprocal scalar. Negative rates tending
to zero force the reciprocal damping upper bound to be attained as an operator
norm supremum. This applies both to the maximal-domain resolvent and to its
original lower Hardy vector integral.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual positive resolvent has the exact reciprocal action on every left-half-plane eigenvector. -/
theorem causalResolvent_leftEigenvector (a : ℝ) (z : {z : ℂ // z.re < 0}) :
    causalResolvent a (causalLeftEigenvector z).val =
      (((Real.exp a : ℝ):ℂ)-z.val)⁻¹ • causalLeftEigenvector z := by
  have hne : (((Real.exp a : ℝ):ℂ)-z.val) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re,Complex.ofReal_re,Complex.zero_re] at hre
    have hz := z.property
    linarith [Real.exp_pos a]
  apply causalGeneratorShift_injective a
  rw [causalGeneratorShift_resolvent,map_smul]
  change (causalLeftEigenvector z).val = (((Real.exp a : ℝ):ℂ)-z.val)⁻¹ •
    (((Real.exp a : ℝ):ℂ) • (causalLeftEigenvector z).val-causalGenerator (causalLeftEigenvector z))
  rw [causalGenerator_leftEigenvector,← sub_smul,inv_smul_smul₀ hne]

/-- The actual resolvent norm on each rational eigenvector is exactly its reciprocal spectral distance. -/
theorem norm_causalResolvent_leftEigenvector (a : ℝ) (z : {z : ℂ // z.re < 0}) :
    ‖causalResolvent a (causalLeftEigenvector z).val‖ =
      ‖((Real.exp a : ℝ):ℂ)-z.val‖⁻¹ * ‖causalLeftEigenvector z‖ := by
  rw [causalResolvent_leftEigenvector,norm_smul,norm_inv]

/-- The actual maximal-domain resolvent has exactly the reciprocal damping operator norm. -/
theorem norm_causalResolvent (a : ℝ) : ‖causalResolvent a‖ = (Real.exp a)⁻¹ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.exp_pos a).le)
    intro u
    exact causalResolvent_norm_le a u
  · have hb (b : ℝ) : (Real.exp a+Real.exp b)⁻¹ ≤ ‖causalResolvent a‖ := by
      let z : {z : ℂ // z.re < 0} :=
        ⟨-((Real.exp b : ℝ):ℂ),by
          simpa only [Complex.neg_re,Complex.ofReal_re] using neg_neg_of_pos (Real.exp_pos b)⟩
      have he : ‖((Real.exp a : ℝ):ℂ)-z.val‖ = Real.exp a+Real.exp b := by
        change ‖((Real.exp a : ℝ):ℂ)-(-((Real.exp b : ℝ):ℂ))‖ = _
        rw [sub_neg_eq_add,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos (add_pos (Real.exp_pos a) (Real.exp_pos b))]
      have h := (causalResolvent a).le_opNorm (causalLeftEigenvector z).val
      rw [norm_causalResolvent_leftEigenvector,he] at h
      have hn := norm_pos_iff.mpr (causalLeftEigenvector_ne_zero z)
      change (Real.exp a+Real.exp b)⁻¹ * ‖causalLeftEigenvector z‖ ≤
        ‖causalResolvent a‖ * ‖causalLeftEigenvector z‖ at h
      exact (mul_le_mul_iff_of_pos_right hn).mp h
    have ht0 : Tendsto (fun b : ℝ => Real.exp a+Real.exp b) atBot (𝓝 (Real.exp a)) := by
      simpa only [add_zero] using tendsto_const_nhds.add Real.tendsto_exp_atBot
    have ht := ht0.inv₀ (Real.exp_ne_zero a)
    exact le_of_tendsto ht (Eventually.of_forall hb)

/-- The same reciprocal damping constant is sharp for the literal lower Hardy Laplace integral. -/
theorem norm_causalLaplaceIntegral (a : ℝ) : ‖causalLaplaceIntegral a‖ = (Real.exp a)⁻¹ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.exp_pos a).le)
    intro u
    exact causalLaplaceIntegral_norm_le a u
  · have h : ‖causalResolvent a‖ ≤ ‖causalLaplaceIntegral a‖ := by
      apply ContinuousLinearMap.opNorm_le_bound (causalResolvent a) (norm_nonneg (causalLaplaceIntegral a))
      intro u
      exact (causalLaplaceIntegral a).le_opNorm u
    rw [norm_causalResolvent] at h
    exact h

end
end RHTower.FokasLenells

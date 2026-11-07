import GaloisForLFunctions.SelbergClass.Primon.PrincipalHilbertInverse
import GaloisForLFunctions.HTGeometry.DiagonalCompactOperator
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import Mathlib.Topology.Instances.ZMultiples

/-!
# Compact inverse ladders in the conformal principal series

The raising and lowering coefficients grow linearly in the integer weight.
Their reciprocal diagonals vanish at infinity, so the bounded inverse ladders
are compact operators on the full weight Hilbert space.
-/

open Filter Topology GaloisForLFunctions.HTGeometry HilbertSchmidt

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private theorem tendsto_abs_weight :
    Tendsto (fun m : ℤ => |(m : ℝ)|) cofinite atTop := by
  simpa only [Function.comp_def, Real.norm_eq_abs] using
    tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Int.isClosedEmbedding_coe_real

/-- Raising amplitudes escape every bounded window on the integer weight lattice. -/
theorem tendsto_norm_principalRaiseCoefficient (ε : ℝ) :
    Tendsto (fun m : ℤ => ‖principalRaiseCoefficient ε m‖) cofinite atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [tendsto_abs_weight.eventually (eventually_ge_atTop (b + 1 / 2))] with m hm
  have hb : |(m : ℝ)| ≤ ‖principalRaiseCoefficient ε m‖ + 1 / 2 := by
    calc |(m : ℝ)| = |(principalRaiseCoefficient ε m).re + 1 / 2| := by
          simp [principalRaiseCoefficient]
      _ ≤ |(principalRaiseCoefficient ε m).re| + 1 / 2 := by
          simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
            abs_add_le (principalRaiseCoefficient ε m).re (1 / 2)
      _ ≤ ‖principalRaiseCoefficient ε m‖ + 1 / 2 :=
        by linarith only [Complex.abs_re_le_norm (principalRaiseCoefficient ε m)]
  linarith only [hm, hb]

/-- Lowering amplitudes escape every bounded window as well. -/
theorem tendsto_norm_principalLowerCoefficient (ε : ℝ) :
    Tendsto (fun m : ℤ => ‖principalLowerCoefficient ε m‖) cofinite atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [tendsto_abs_weight.eventually (eventually_ge_atTop (b + 1 / 2))] with m hm
  have hb : |(m : ℝ)| ≤ ‖principalLowerCoefficient ε m‖ + 1 / 2 := by
    calc |(m : ℝ)| = |(principalLowerCoefficient ε m).re + 1 / 2| := by
          simp [principalLowerCoefficient]
      _ ≤ |(principalLowerCoefficient ε m).re| + 1 / 2 := by
          simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
            abs_add_le (principalLowerCoefficient ε m).re (1 / 2)
      _ ≤ ‖principalLowerCoefficient ε m‖ + 1 / 2 :=
        by linarith only [Complex.abs_re_le_norm (principalLowerCoefficient ε m)]
  linarith only [hm, hb]

/-- Reciprocal raising amplitudes vanish at both ends of the weight lattice. -/
theorem tendsto_norm_inv_principalRaiseCoefficient (ε : ℝ) :
    Tendsto (fun m : ℤ => ‖(principalRaiseCoefficient ε m)⁻¹‖) cofinite (𝓝 0) := by
  simpa only [norm_inv, Function.comp_def] using
    tendsto_inv_atTop_zero.comp (tendsto_norm_principalRaiseCoefficient ε)

/-- Reciprocal lowering amplitudes vanish at both ends of the weight lattice. -/
theorem tendsto_norm_inv_principalLowerCoefficient (ε : ℝ) :
    Tendsto (fun m : ℤ => ‖(principalLowerCoefficient ε m)⁻¹‖) cofinite (𝓝 0) := by
  simpa only [norm_inv, Function.comp_def] using
    tendsto_inv_atTop_zero.comp (tendsto_norm_principalLowerCoefficient ε)

/-- The full Hilbert-space raising inverse is compact. -/
theorem isCompactOperator_principalRaisingInverseL2 (ε : ℝ) :
    IsCompactOperator (principalRaisingInverseL2 ε) := by
  rw [principalRaisingInverseL2, ContinuousLinearMap.coe_comp]
  apply IsCompactOperator.comp_clm
  apply isCompactOperator_of_diag_tendsto_cofinite (lpBasis ℤ)
    (c := fun m => (principalRaiseCoefficient ε m)⁻¹)
  · intro m
    rw [lpBasis_apply, lpDiagonalCLM_single, ← lp.single_smul]
    simp only [smul_eq_mul, mul_one]
  · exact tendsto_norm_inv_principalRaiseCoefficient ε

/-- The full Hilbert-space lowering inverse is compact. -/
theorem isCompactOperator_principalLoweringInverseL2 (ε : ℝ) :
    IsCompactOperator (principalLoweringInverseL2 ε) := by
  rw [principalLoweringInverseL2, ContinuousLinearMap.coe_comp]
  apply IsCompactOperator.comp_clm
  apply isCompactOperator_of_diag_tendsto_cofinite (lpBasis ℤ)
    (c := fun m => (principalLowerCoefficient ε m)⁻¹)
  · intro m
    rw [lpBasis_apply, lpDiagonalCLM_single, ← lp.single_smul]
    simp only [smul_eq_mul, mul_one]
  · exact tendsto_norm_inv_principalLowerCoefficient ε

end
end GaloisForLFunctions.SelbergClass.Primon

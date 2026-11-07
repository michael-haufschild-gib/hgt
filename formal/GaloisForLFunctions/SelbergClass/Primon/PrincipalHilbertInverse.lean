import GaloisForLFunctions.SelbergClass.Primon.PrincipalHermitian
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicAffineProjection

/-!
# Bounded inverse ladders on the principal-series Hilbert space

The nonvanishing ladder coefficients have minimum modulus
`sqrt (1/4 + ε²)`. Their reciprocal shifts therefore extend to bounded
operators on `ℓ²(ℤ)`. These operators invert the finite-vector ladders and
have the exact norm `1 / sqrt (1/4 + ε²)`.
-/

open GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Standard Hilbert space of the integer principal-series weights. -/
abbrev PrincipalHilbert := lp (fun _ : ℤ => ℂ) 2

/-- Sharp norm of either inverse ladder. -/
def principalInverseBound (ε : ℝ) : ℝ := (Real.sqrt (principalEnergy ε))⁻¹

private theorem principalEnergy_pos (ε : ℝ) : 0 < principalEnergy ε :=
  lt_of_lt_of_le (by norm_num) (principalEnergy_ge_quarter ε)

private theorem principalInverseBound_pos (ε : ℝ) : 0 < principalInverseBound ε :=
  inv_pos.mpr (Real.sqrt_pos.mpr (principalEnergy_pos ε))

/-- Uniform reciprocal raising bound, obtained from the exact energy gap. -/
theorem norm_inv_principalRaiseCoefficient_le (ε : ℝ) (m : ℤ) :
    ‖(principalRaiseCoefficient ε m)⁻¹‖ ≤ principalInverseBound ε := by
  rw [norm_inv, principalInverseBound]
  apply (inv_le_inv₀ (norm_pos_iff.mpr (principalRaiseCoefficient_ne_zero ε m))
    (Real.sqrt_pos.mpr (principalEnergy_pos ε))).mpr
  simpa only [← Complex.sq_norm, Real.sqrt_sq (norm_nonneg _)] using
    Real.sqrt_le_sqrt (normSq_principalRaiseCoefficient_ge_energy ε m)

/-- Uniform reciprocal lowering bound, obtained from the exact energy gap. -/
theorem norm_inv_principalLowerCoefficient_le (ε : ℝ) (m : ℤ) :
    ‖(principalLowerCoefficient ε m)⁻¹‖ ≤ principalInverseBound ε := by
  rw [norm_inv, principalInverseBound]
  apply (inv_le_inv₀ (norm_pos_iff.mpr (principalLowerCoefficient_ne_zero ε m))
    (Real.sqrt_pos.mpr (principalEnergy_pos ε))).mpr
  simpa only [← Complex.sq_norm, Real.sqrt_sq (norm_nonneg _)] using
    Real.sqrt_le_sqrt (normSq_principalLowerCoefficient_ge_energy ε m)

/-- Raising inverse on the full weight Hilbert space. -/
def principalRaisingInverseL2 (ε : ℝ) : PrincipalHilbert →L[ℂ] PrincipalHilbert :=
  (lpDiagonalCLM (fun m => (principalRaiseCoefficient ε m)⁻¹)
    (principalInverseBound_pos ε).le (norm_inv_principalRaiseCoefficient_le ε)).comp
    ((_root_.RHTower.lpReindexEquiv (Equiv.addRight (-1 : ℤ))).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Lowering inverse on the full weight Hilbert space. -/
def principalLoweringInverseL2 (ε : ℝ) : PrincipalHilbert →L[ℂ] PrincipalHilbert :=
  (lpDiagonalCLM (fun m => (principalLowerCoefficient ε m)⁻¹)
    (principalInverseBound_pos ε).le (norm_inv_principalLowerCoefficient_le ε)).comp
    ((_root_.RHTower.lpReindexEquiv (Equiv.addRight (1 : ℤ))).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem principalRaisingInverseL2_apply (ε : ℝ) (v : PrincipalHilbert) (m : ℤ) :
    principalRaisingInverseL2 ε v m = (principalRaiseCoefficient ε m)⁻¹ * v (m + 1) := by
  simp [principalRaisingInverseL2, _root_.RHTower.lpReindexEquiv_apply]

@[simp] theorem principalLoweringInverseL2_apply (ε : ℝ) (v : PrincipalHilbert) (m : ℤ) :
    principalLoweringInverseL2 ε v m = (principalLowerCoefficient ε m)⁻¹ * v (m - 1) := by
  simp [principalLoweringInverseL2, _root_.RHTower.lpReindexEquiv_apply, sub_eq_add_neg]

/-- The Hilbert-space inverse agrees with the algebraic raising inverse. -/
theorem principalRaisingInverseL2_finite (ε : ℝ) (v : SphericalKFiniteModel) :
    principalRaisingInverseL2 ε (principalToL2 v) =
      principalToL2 (principalRaisingInverse ε v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single m z =>
    ext n
    simp only [principalRaisingInverse, weightedShift_single, principalToL2_single,
      principalRaisingInverseL2_apply, lp.single_apply, Pi.single_apply]
    by_cases h : m = n + 1
    · subst m
      simp
    · have hn : m + -1 ≠ n := by omega
      simp [Ne.symm h, Ne.symm hn]

/-- The Hilbert-space inverse agrees with the algebraic lowering inverse. -/
theorem principalLoweringInverseL2_finite (ε : ℝ) (v : SphericalKFiniteModel) :
    principalLoweringInverseL2 ε (principalToL2 v) =
      principalToL2 (principalLoweringInverse ε v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single m z =>
    ext n
    simp only [principalLoweringInverse, weightedShift_single, principalToL2_single,
      principalLoweringInverseL2_apply, lp.single_apply, Pi.single_apply]
    by_cases h : m = n - 1
    · subst m
      simp
    · have hn : m + 1 ≠ n := by omega
      simp [Ne.symm h, Ne.symm hn]

/-- The extended raising inverse has the energy-gap bound. -/
theorem norm_principalRaisingInverseL2_apply_le (ε : ℝ) (v : PrincipalHilbert) :
    ‖principalRaisingInverseL2 ε v‖ ≤ principalInverseBound ε * ‖v‖ := by
  have h := norm_lpDiagonalLM_le (fun m => (principalRaiseCoefficient ε m)⁻¹)
    (principalInverseBound_pos ε).le (norm_inv_principalRaiseCoefficient_le ε)
    (_root_.RHTower.lpReindexEquiv (Equiv.addRight (-1 : ℤ)) v)
  have he : principalRaisingInverseL2 ε v =
      lpDiagonalLM (fun m => (principalRaiseCoefficient ε m)⁻¹)
        (principalInverseBound_pos ε).le (norm_inv_principalRaiseCoefficient_le ε)
        (_root_.RHTower.lpReindexEquiv (Equiv.addRight (-1 : ℤ)) v) := by
    ext m
    rfl
  rw [he]
  simpa only [LinearIsometryEquiv.norm_map] using h

/-- The extended lowering inverse has the same energy-gap bound. -/
theorem norm_principalLoweringInverseL2_apply_le (ε : ℝ) (v : PrincipalHilbert) :
    ‖principalLoweringInverseL2 ε v‖ ≤ principalInverseBound ε * ‖v‖ := by
  have h := norm_lpDiagonalLM_le (fun m => (principalLowerCoefficient ε m)⁻¹)
    (principalInverseBound_pos ε).le (norm_inv_principalLowerCoefficient_le ε)
    (_root_.RHTower.lpReindexEquiv (Equiv.addRight (1 : ℤ)) v)
  have he : principalLoweringInverseL2 ε v =
      lpDiagonalLM (fun m => (principalLowerCoefficient ε m)⁻¹)
        (principalInverseBound_pos ε).le (norm_inv_principalLowerCoefficient_le ε)
        (_root_.RHTower.lpReindexEquiv (Equiv.addRight (1 : ℤ)) v) := by
    ext m
    rfl
  rw [he]
  simpa only [LinearIsometryEquiv.norm_map] using h

/-- Raising cannot decrease a finite vector's norm below the spectral gap. -/
theorem principalRaising_norm_coercive (ε : ℝ) (v : SphericalKFiniteModel) :
    ‖principalToL2 v‖ ≤ principalInverseBound ε * ‖principalToL2 (principalRaising ε v)‖ := by
  have h := norm_principalRaisingInverseL2_apply_le ε (principalToL2 (principalRaising ε v))
  rw [principalRaisingInverseL2_finite] at h
  have hi := LinearMap.congr_fun (principalRaisingInverse_comp ε) v
  change principalRaisingInverse ε (principalRaising ε v) = v at hi
  rwa [hi] at h

/-- Lowering has the identical quantitative injectivity bound. -/
theorem principalLowering_norm_coercive (ε : ℝ) (v : SphericalKFiniteModel) :
    ‖principalToL2 v‖ ≤ principalInverseBound ε * ‖principalToL2 (principalLowering ε v)‖ := by
  have h := norm_principalLoweringInverseL2_apply_le ε (principalToL2 (principalLowering ε v))
  rw [principalLoweringInverseL2_finite] at h
  have hi := LinearMap.congr_fun (principalLoweringInverse_comp ε) v
  change principalLoweringInverse ε (principalLowering ε v) = v at hi
  rwa [hi] at h

/-- The raising inverse bound is attained on the weight-one unit vector. -/
theorem norm_principalRaisingInverseL2 (ε : ℝ) :
    ‖principalRaisingInverseL2 ε‖ = principalInverseBound ε := by
  apply le_antisymm
  · exact (principalRaisingInverseL2 ε).opNorm_le_bound
      (principalInverseBound_pos ε).le (norm_principalRaisingInverseL2_apply_le ε)
  · have hg : ‖principalRaiseCoefficient ε 0‖ = Real.sqrt (principalEnergy ε) := by
      rw [← (principal_ladder_ground_energy ε).1, ← Complex.sq_norm,
        Real.sqrt_sq (norm_nonneg _)]
    calc principalInverseBound ε =
        ‖principalRaisingInverseL2 ε (lp.single 2 1 (1 : ℂ)) 0‖ := by
          simp [principalRaisingInverseL2_apply, lp.single_apply, hg, principalInverseBound]
      _ ≤ ‖principalRaisingInverseL2 ε (lp.single 2 1 (1 : ℂ))‖ :=
        lp.norm_apply_le_norm (by norm_num) _ _
      _ ≤ ‖principalRaisingInverseL2 ε‖ := by
        simpa only [lp.norm_single (by norm_num : (0 : ENNReal) < 2), norm_one, mul_one] using
          (principalRaisingInverseL2 ε).le_opNorm (lp.single 2 1 (1 : ℂ))

/-- The lowering inverse bound is attained on the weight-minus-one unit vector. -/
theorem norm_principalLoweringInverseL2 (ε : ℝ) :
    ‖principalLoweringInverseL2 ε‖ = principalInverseBound ε := by
  apply le_antisymm
  · exact (principalLoweringInverseL2 ε).opNorm_le_bound
      (principalInverseBound_pos ε).le (norm_principalLoweringInverseL2_apply_le ε)
  · have hg : ‖principalLowerCoefficient ε 0‖ = Real.sqrt (principalEnergy ε) := by
      rw [← (principal_ladder_ground_energy ε).2, ← Complex.sq_norm,
        Real.sqrt_sq (norm_nonneg _)]
    calc principalInverseBound ε =
        ‖principalLoweringInverseL2 ε (lp.single 2 (-1) (1 : ℂ)) 0‖ := by
          simp [principalLoweringInverseL2_apply, lp.single_apply, hg, principalInverseBound]
      _ ≤ ‖principalLoweringInverseL2 ε (lp.single 2 (-1) (1 : ℂ))‖ :=
        lp.norm_apply_le_norm (by norm_num) _ _
      _ ≤ ‖principalLoweringInverseL2 ε‖ := by
        simpa only [lp.norm_single (by norm_num : (0 : ENNReal) < 2), norm_one, mul_one] using
          (principalLoweringInverseL2 ε).le_opNorm (lp.single 2 (-1) (1 : ℂ))

end
end GaloisForLFunctions.SelbergClass.Primon

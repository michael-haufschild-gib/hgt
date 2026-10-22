import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMModularSpacetimeCoordinates

/-! The original BM background is an isometry under the actual modular coordinate action. -/

open Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

/-- The actual modular Jacobian scale cancels exactly against the transported hyperbolic height. -/
theorem modular_height_scale (A : SL(2,ℤ)) (z : UpperHalfPlane) :
    ((A • z).im:ℂ)⁻¹^(2 : ℕ) *
      (((1/(denom A z)^(2 : ℕ)).re:ℂ)^(2 : ℕ)+((1/(denom A z)^(2 : ℕ)).im:ℂ)^(2 : ℕ)) = (z.im:ℂ)⁻¹^(2 : ℕ) := by
  have hd : (Complex.normSq (denom A z):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (UpperHalfPlane.normSq_denom_ne_zero (A : GL (Fin 2) ℝ) z.im_ne_zero)
  have hy : (z.im:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_ne_zero
  have hc : (((1/(denom A z)^(2 : ℕ)).re:ℂ)^(2 : ℕ)+((1/(denom A z)^(2 : ℕ)).im:ℂ)^(2 : ℕ)) =
      (Complex.normSq (1/(denom A z)^(2 : ℕ)):ℂ) := by
    simp [Complex.normSq_apply,pow_two]
  rw [hc,ModularGroup.im_smul_eq_div_normSq,Complex.ofReal_div,
    Complex.normSq_div,Complex.normSq_one,map_pow]
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_pow]
  field_simp [hd,hy]

/-- The original BM background is preserved by the actual full modular coordinate differential. -/
theorem backgroundMetric_modular (A : SL(2,ℤ)) (z : UpperHalfPlane) (r : ℂ) :
    modularTensorPullback A z (D4BMBackground.metric r (A • z).im) = D4BMBackground.metric r z.im := by
  have hs := modular_height_scale A z
  simp only [modularTensorPullback,modularJacobian]
  generalize 1/(denom A z)^(2 : ℕ) = c at hs ⊢
  simp only [sl_moeb] at hs
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [D4BMBackground.metric,Matrix.mul_apply,Fin.sum_univ_succ]
  all_goals first | linear_combination (r^(2 : ℕ))*hs | ring

end
end RHTower.D4BMModularCore

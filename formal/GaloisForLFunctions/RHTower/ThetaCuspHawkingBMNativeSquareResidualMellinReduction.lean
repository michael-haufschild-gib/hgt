import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeSquareResidualUnfolding

/-! Exact Mellin reduction of the native residual integral, with the full actual source mean. -/
open Set Filter Topology MeasureTheory UpperHalfPlane
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
noncomputable section

/-- Actual horizontal mean of the constructed global source. -/
def residualStripMean (q : XiZeroCopy) (y : ℝ) : ℂ :=
  ∫ x in Ico (0:ℝ) 1, globalSquareResidual q (ofComplex (⟨x,y⟩:ℂ))

/-- The original quotient integral equals its convergent Mellin integral, with the original completion. -/
theorem scalarResidualPeriod_eq_mellin (q : XiZeroCopy)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    scalarResidualPeriod q (P.s-1/2) = reflectedCompletedLambda (2*P.s)*
      ∫ y in Ioi (0:ℝ), (y:ℂ)^(P.s-2)*residualStripMean q y := by
  rw [scalarResidualPeriod_eq_strip,
    setIntegral_modularStrip_eq_iterated _ (residualMellinSeed_integrable q P)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only
  have he (x : ℝ) : residualMellinSeed q P.s (ofComplex (⟨x,y⟩:ℂ)) =
      (y:ℂ)^P.s*globalSquareResidual q (ofComplex (⟨x,y⟩:ℂ)) := by
    unfold residualMellinSeed
    rw [ofComplex_apply_of_im_pos (by simpa using hy)]
    rfl
  simp_rw [he]
  rw [integral_const_mul]
  change (y^2)⁻¹ • ((y:ℂ)^P.s*residualStripMean q y) = _
  have hn : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (show 0 < y from hy).ne'
  have htwo : (y:ℂ)^(2:ℂ)=(y:ℂ)^2 := by norm_cast
  rw [Complex.cpow_sub _ _ hn,htwo]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow]
  ring

end
end RHTower.D4BMJointSource

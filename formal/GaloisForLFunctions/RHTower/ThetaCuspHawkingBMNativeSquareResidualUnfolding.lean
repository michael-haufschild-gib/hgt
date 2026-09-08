import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareResidualMellinAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinCoprimeRowSum

/-! Actual unfolding of the original admitted square-residual period, with exact normalization. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup EisensteinSeries
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMGlobalAngularResponse
noncomputable section

private theorem scalar_residual_eq_sum (q : XiZeroCopy)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (z : UpperHalfPlane) :
    scalar (P.s-1/2) (coordinates z)*globalSquareResidual q z =
      reflectedCompletedLambda (2*P.s)*(1/2:ℂ)*
        ∑' v : gammaSet 1 1 0, residualMellinSeed q P.s (gammaSetMatrix v • z) := by
  rw [scalar_eq_coprime_row_sum]
  have he (v : gammaSet 1 1 0) : residualMellinSeed q P.s (gammaSetMatrix v • z) =
      ((gammaSetMatrix v • z).im:ℂ)^P.s*globalSquareResidual q z := by
    unfold residualMellinSeed
    congr 1
    exact globalSquareResidual_invariant q (QuotientGroup.mk (gammaSetMatrix v)) z
  simp_rw [he,tsum_mul_right]
  ring

/-- Absolute translate-integral summability is derived from the actual source's strip admission. -/
theorem residualMellinSeed_translated_norm_summable (q : XiZeroCopy)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable (fun v : gammaSet 1 1 0 =>
      ∫ z : UpperHalfPlane in fd, ‖residualMellinSeed q P.s (gammaSetMatrix v • z)‖) := by
  have hi := residualMellinSeed_integrable q P
  have hnorm := summable_fdUnfoldTerm
    (φ := fun z => ((‖residualMellinSeed q P.s z‖:ℝ):ℂ))
    (fun n z => by rw [residualMellinSeed_periodic]) hi.norm.ofReal
  have he : fdUnfoldTerm (fun z => ((‖residualMellinSeed q P.s z‖:ℝ):ℂ)) =
      fun v => ((∫ z : UpperHalfPlane in fd, ‖residualMellinSeed q P.s (gammaSetMatrix v • z)‖:ℝ):ℂ) := by
    funext v
    rw [fdUnfoldTerm]
    exact integral_ofReal
  rw [he] at hnorm
  exact Complex.summable_ofReal.mp hnorm

/-- The native fundamental-domain integral unfolds to the original strip source, for every Xi copy. -/
theorem scalarResidualPeriod_eq_strip (q : XiZeroCopy)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    scalarResidualPeriod q (P.s-1/2) = reflectedCompletedLambda (2*P.s)*
      ∫ z : UpperHalfPlane in modularStrip, residualMellinSeed q P.s z := by
  have hper := residualMellinSeed_periodic q P.s
  have hi := residualMellinSeed_integrable q P
  have he : (∫ z : UpperHalfPlane in fd,
      ∑' v : gammaSet 1 1 0, residualMellinSeed q P.s (gammaSetMatrix v • z)) =
      ∑' v : gammaSet 1 1 0, ∫ z : UpperHalfPlane in fd,
        residualMellinSeed q P.s (gammaSetMatrix v • z) := by
    symm
    apply integral_tsum_of_summable_integral_norm
    · intro v
      exact (integrableOn_smul_set_iff (gammaSetMatrix v) _ fd).mp
        (integrableOn_smul_fd_of_periodic hper hi _)
    · exact residualMellinSeed_translated_norm_summable q P
  rw [scalarResidualPeriod_eq_global]
  simp_rw [scalar_residual_eq_sum]
  rw [integral_const_mul,he,
    tsum_setIntegral_fd_eq_two_mul_setIntegral_modularStrip _ hper hi]
  ring

end
end RHTower.D4BMJointSource

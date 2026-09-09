import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspWindowAbsoluteRegrouping
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinCoprimeRowSum

/-! The full windowed height-power orbit sum is the actual normalized Eisenstein field. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup EisensteinSeries
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups
namespace RHTower.D4BMModularCore
open D4BMJointSource D4BMGlobalAngularResponse
noncomputable section

/-- Negating a coprime row preserves its transformed height exactly. -/
theorem cuspRow_neg_height (v : gammaSet 1 1 0) (z : UpperHalfPlane) :
    (gammaSetMatrix (gammaSetNeg v) • z).im = (gammaSetMatrix v • z).im := by
  obtain ⟨n,hn⟩ := gammaSetMatrix_gammaSetNeg_smul v z
  rw [hn,ModularGroup.im_T_zpow_smul]

/-- Every admitted height-row sum has exactly two copies of its projective half-row sum. -/
theorem cuspHeight_full_sum_eq_two_half (h : ℝ → ℂ) (z : UpperHalfPlane)
    (hs : Summable (fun v : gammaSet 1 1 0 => h (gammaSetMatrix v • z).im)) :
    (∑' v : gammaSet 1 1 0, h (gammaSetMatrix v • z).im) =
      2*(∑' v : gammaSetHalf, h (gammaSetMatrix v.1 • z).im) := by
  have he : (∑' v : (gammaSetHalfᶜ : Set (gammaSet 1 1 0)), h (gammaSetMatrix v.1 • z).im) =
      ∑' v : gammaSetHalf, h (gammaSetMatrix v.1 • z).im := by
    rw [← gammaSetHalfNegEquiv.tsum_eq]
    apply tsum_congr
    intro v
    exact congrArg h (cuspRow_neg_height v.1 z)
  rw [← hs.tsum_subtype_add_tsum_subtype_compl gammaSetHalf,he,two_mul]

/-- The actual primitive Eisenstein convergence theorem admits all coprime height-power rows. -/
theorem cuspHeightPower_full_rows_summable (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (z : UpperHalfPlane) :
    Summable (fun v : gammaSet 1 1 0 => ((gammaSetMatrix v • z).im:ℂ)^P.s) := by
  apply primitiveRowEquiv.summable_iff.mp
  exact (summable_d4BMPoincareSeed ⟨z.re,z.im,z.im_pos⟩ P).congr
    (fun p => poincareSeed_eq_row_height z P.s p)

/-- Projective height-power rows inherit the original admitted sum. -/
theorem cuspHeightPower_rows_summable (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (z : UpperHalfPlane) :
    Summable (fun v : gammaSetHalf => ((gammaSetMatrix v.1 • z).im:ℂ)^P.s) :=
  (cuspHeightPower_full_rows_summable P z).subtype (fun v => v ∈ gammaSetHalf)

/-- The unchanged translation window and entire modular sum recover the original completed field. -/
theorem cuspHeightPower_periodize_completed (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (z : UpperHalfPlane) :
    reflectedCompletedLambda (2*P.s)*periodize (cuspHeightSeed (fun y : ℝ => (y:ℂ)^P.s)) z =
      scalar (P.s-1/2) (coordinates z) := by
  have hp := periodize_cuspHeightSeed_eq_rows_of_rows_summable
    (fun y : ℝ => (y:ℂ)^P.s) z (cuspHeightPower_rows_summable P z)
  have hr := cuspHeight_full_sum_eq_two_half (fun y : ℝ => (y:ℂ)^P.s) z
    (cuspHeightPower_full_rows_summable P z)
  rw [hp,scalar_eq_coprime_row_sum P z,hr]
  ring

end
end RHTower.D4BMModularCore

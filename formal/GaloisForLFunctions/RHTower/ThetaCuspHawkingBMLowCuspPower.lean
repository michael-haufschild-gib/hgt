import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspPowerPeriodization
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspNonparabolicHeight

/-! The reverse lower-height power sum is the actual Eisenstein field with its parabolic power removed. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse
noncomputable section

/-- The Mellin test restricted to the original lower-height correction region. -/
def lowCuspPower (s : ℂ) (y : ℝ) : ℂ := if y ≤ 1/2 then (y:ℂ)^s else 0

/-- The complete lower-height row norms are dominated by the original Eisenstein height powers. -/
theorem lowCuspPower_row_norm_le (s : ℂ) (v : gammaSetHalf) (z : UpperHalfPlane) :
    ‖lowCuspPower s (gammaSetMatrix v.1 • z).im‖ ≤ ‖((gammaSetMatrix v.1 • z).im:ℂ)^s‖ := by
  unfold lowCuspPower
  split_ifs
  · exact le_rfl
  · simp only [norm_zero]
    exact norm_nonneg _

/-- Every lower-height row is admitted throughout the original Eisenstein convergence chamber. -/
theorem lowCuspPower_rows_summable (P : D4BMEisensteinAbsoluteConvergenceParameter) (z : UpperHalfPlane) :
    Summable (fun v : gammaSetHalf => lowCuspPower P.s (gammaSetMatrix v.1 • z).im) :=
  ((cuspHeightPower_rows_summable P z).norm.of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun v => lowCuspPower_row_norm_le P.s v z)).of_norm

/-- The lower-height cutoff also admits its full original projective orbit sum. -/
theorem lowCuspPower_orbit_summable (P : D4BMEisensteinAbsoluteConvergenceParameter) (z : UpperHalfPlane) :
    Summable (fun γ : PSL2Z => cuspHeightSeed (lowCuspPower P.s) (γ • z)) :=
  cuspHeightSeed_orbit_summable_of_rows _ z (lowCuspPower_rows_summable P z)

/-- On the actual high support, every nonparabolic row is retained and the parabolic row is absent. -/
theorem lowCuspPower_periodize_eq_nonparabolic (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (z : UpperHalfPlane) (hz : 2 ≤ z.im) :
    periodize (cuspHeightSeed (lowCuspPower P.s)) z =
      cuspNonparabolicHeightSum (fun y : ℝ => (y:ℂ)^P.s) z := by
  classical
  rw [periodize_cuspHeightSeed_eq_rows_of_rows_summable (lowCuspPower P.s) z
    (lowCuspPower_rows_summable P z),cuspNonparabolicHeightSum]
  apply tsum_congr
  intro v
  by_cases hv : v = cuspIdentityRow
  · subst v
    rw [cuspIdentityRow_height,lowCuspPower,if_neg (by linarith : ¬ z.im ≤ 1/2),if_pos rfl]
  · have hy : (gammaSetMatrix v.1 • z).im ≤ 1/2 :=
      (cuspRow_nonparabolic_height_le v hv z).trans
        ((div_le_iff₀ z.im_pos).mpr (by linarith))
    rw [lowCuspPower,if_pos hy,if_neg hv]

/-- The reverse test is the full actual completed Eisenstein field minus its original parabolic power. -/
theorem lowCuspPower_periodize_completed (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (z : UpperHalfPlane) (hz : 2 ≤ z.im) :
    reflectedCompletedLambda (2*P.s)*periodize (cuspHeightSeed (lowCuspPower P.s)) z =
      scalar (P.s-1/2) (coordinates z)-reflectedCompletedLambda (2*P.s)*(z.im:ℂ)^P.s := by
  classical
  have hp := periodize_cuspHeightSeed_eq_rows_of_rows_summable
    (fun y : ℝ => (y:ℂ)^P.s) z (cuspHeightPower_rows_summable P z)
  have he := cuspHeightPower_periodize_completed P z
  rw [hp,(cuspHeightPower_rows_summable P z).tsum_eq_add_tsum_ite cuspIdentityRow,
    cuspIdentityRow_height] at he
  rw [lowCuspPower_periodize_eq_nonparabolic P z hz]
  change reflectedCompletedLambda (2*P.s)*cuspNonparabolicHeightSum (fun y : ℝ => (y:ℂ)^P.s) z = _
  change reflectedCompletedLambda (2*P.s)*((z.im:ℂ)^P.s+
    cuspNonparabolicHeightSum (fun y : ℝ => (y:ℂ)^P.s) z) = _ at he
  rw [← he]
  ring

end
end RHTower.D4BMModularCore

import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspHeightOrbitFinite

/-! Exact coprime-row regrouping of the original full high-cusp periodization. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups
namespace RHTower.D4BMModularCore
noncomputable section

/-- Each row retains the full translation partition with no position restriction. -/
theorem cuspHeightSeed_translation_sum (h : ℝ → ℂ) (v : gammaSetHalf) (z : UpperHalfPlane) :
    (∑' n : ℤ, cuspHeightSeed h (cuspOrbitEquiv (v,n) • z)) =
      h (gammaSetMatrix v.1 • z).im := by
  simp_rw [cuspOrbitEquiv_smul,cuspHeightSeed,ModularGroup.re_T_zpow_smul,ModularGroup.im_T_zpow_smul]
  rw [tsum_mul_right,← Complex.ofReal_tsum,cuspWindow_partition_all]
  simp

/-- Admitted full orbit sums regroup into exactly one copy of each coprime half-row. -/
theorem periodize_cuspHeightSeed_eq_rows_of_summable (h : ℝ → ℂ) (z : UpperHalfPlane)
    (hs : Summable (fun γ : PSL2Z => cuspHeightSeed h (γ • z))) :
    periodize (cuspHeightSeed h) z = ∑' v : gammaSetHalf, h (gammaSetMatrix v.1 • z).im := by
  have hp : Summable (fun p : gammaSetHalf × ℤ => cuspHeightSeed h (cuspOrbitEquiv p • z)) :=
    cuspOrbitEquiv.summable_iff.mpr hs
  rw [periodize,← cuspOrbitEquiv.tsum_eq (fun γ : PSL2Z => cuspHeightSeed h (γ • z)),hp.tsum_prod]
  exact tsum_congr (fun v => cuspHeightSeed_translation_sum h v z)

/-- The actual high-cusp profile supplies every summability input needed for the regrouping. -/
theorem periodize_cuspHeightSeed_eq_rows (h : ℝ → ℂ) (hh : ∀ y ≤ 2, h y = 0)
    (z : UpperHalfPlane) :
    periodize (cuspHeightSeed h) z = ∑' v : gammaSetHalf, h (gammaSetMatrix v.1 • z).im :=
  periodize_cuspHeightSeed_eq_rows_of_summable h z (cuspHeightSeed_orbit_summable h hh z)

/-- The complete coprime-row height sum is summable for the original noncompact profile. -/
theorem cuspHeight_rows_summable (h : ℝ → ℂ) (hh : ∀ y ≤ 2, h y = 0) (z : UpperHalfPlane) :
    Summable (fun v : gammaSetHalf => h (gammaSetMatrix v.1 • z).im) := by
  have hp : Summable (fun p : gammaSetHalf × ℤ => cuspHeightSeed h (cuspOrbitEquiv p • z)) :=
    cuspOrbitEquiv.summable_iff.mpr (cuspHeightSeed_orbit_summable h hh z)
  exact hp.prod.congr (fun v => cuspHeightSeed_translation_sum h v z)

end
end RHTower.D4BMModularCore

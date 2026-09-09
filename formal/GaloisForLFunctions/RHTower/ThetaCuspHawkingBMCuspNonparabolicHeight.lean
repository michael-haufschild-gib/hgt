import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspHeightRowPeriodization
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceOverlap

/-! Exact parabolic separation retains the full lower-height modular correction. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup EisensteinSeries
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups
namespace RHTower.D4BMModularCore
noncomputable section

/-- The unique parabolic half-row. -/
def cuspIdentityRow : gammaSetHalf :=
  ⟨⟨![0,1],by rw [gammaSet_one_mem_iff]; norm_num⟩,Or.inr ⟨rfl,rfl⟩⟩

/-- The parabolic matrix preserves the original height. -/
theorem cuspIdentityRow_height (z : UpperHalfPlane) :
    (gammaSetMatrix cuspIdentityRow.1 • z).im = z.im := by
  rw [ModularGroup.im_smul_eq_div_normSq,denom_apply,
    gammaSetMatrix_apply_one_zero,gammaSetMatrix_apply_one_one]
  simp [cuspIdentityRow]

/-- Every other half-row has strictly positive lower-left matrix entry. -/
theorem cuspRow_c_pos {v : gammaSetHalf} (hv : v ≠ cuspIdentityRow) : 0 < v.1.1 0 := by
  rcases v.2 with hc | ⟨hc,hd⟩
  · exact hc
  · apply False.elim
    apply hv
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i
    · exact hc
    · exact hd

/-- Every nonparabolic half-row sends the original height below its reciprocal. -/
theorem cuspRow_nonparabolic_height_le (v : gammaSetHalf) (hv : v ≠ cuspIdentityRow)
    (z : UpperHalfPlane) : (gammaSetMatrix v.1 • z).im ≤ 1/z.im := by
  apply nonparabolic_height_le
  rw [gammaSetMatrix_apply_one_zero]
  exact (cuspRow_c_pos hv).ne'

/-- The full nonparabolic correction, without dropping any lower-height image. -/
def cuspNonparabolicHeightSum (h : ℝ → ℂ) (z : UpperHalfPlane) : ℂ :=
  ∑' v : gammaSetHalf, if v = cuspIdentityRow then 0 else h (gammaSetMatrix v.1 • z).im

/-- The original high-cusp periodization separates into one parabolic profile and all other rows. -/
theorem periodize_cuspHeightSeed_eq_height_add_nonparabolic (h : ℝ → ℂ)
    (hh : ∀ y ≤ 2, h y = 0) (z : UpperHalfPlane) :
    periodize (cuspHeightSeed h) z = h z.im + cuspNonparabolicHeightSum h z := by
  classical
  rw [periodize_cuspHeightSeed_eq_rows h hh z,
    (cuspHeight_rows_summable h hh z).tsum_eq_add_tsum_ite cuspIdentityRow,cuspIdentityRow_height]
  rfl

/-- The complete nonparabolic correction vanishes at every height at least one-half. -/
theorem cuspNonparabolicHeightSum_zero (h : ℝ → ℂ) (hh : ∀ y ≤ 2, h y = 0)
    (z : UpperHalfPlane) (hy : 1/2 ≤ z.im) : cuspNonparabolicHeightSum h z = 0 := by
  classical
  suffices ∀ v : gammaSetHalf,
      (if v = cuspIdentityRow then (0:ℂ) else h (gammaSetMatrix v.1 • z).im) = 0 by
    simp only [cuspNonparabolicHeightSum,this,tsum_zero]
  intro v
  split_ifs with hv
  · rfl
  · apply hh
    exact (cuspRow_nonparabolic_height_le v hv z).trans
      ((div_le_iff₀ z.im_pos).mpr (by linarith))

/-- Above the orbit-height threshold the original profile is exact at every horizontal point. -/
theorem periodize_cuspHeightSeed_eq_height (h : ℝ → ℂ) (hh : ∀ y ≤ 2, h y = 0)
    (z : UpperHalfPlane) (hy : 1/2 ≤ z.im) : periodize (cuspHeightSeed h) z = h z.im := by
  rw [periodize_cuspHeightSeed_eq_height_add_nonparabolic h hh z,
    cuspNonparabolicHeightSum_zero h hh z hy,add_zero]

end
end RHTower.D4BMModularCore

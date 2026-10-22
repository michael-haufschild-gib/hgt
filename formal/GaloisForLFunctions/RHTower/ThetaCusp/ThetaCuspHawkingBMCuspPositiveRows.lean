import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLowCuspPowerMean
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeCutoffMellinAdmission

/-! Nonnegative real row sums dominate the unchanged complex cutoff orbit sums. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMModularCore
open D4BMJointSource D4BMGlobalAngularResponse
noncomputable section

/-- The full positive height-power sum over the original coprime half-rows. -/
def positiveCuspRows (r : ℝ) (z : UpperHalfPlane) : ℝ :=
  ∑' v : gammaSetHalf, (gammaSetMatrix v.1 • z).im ^ r

/-- The same positive row sum restricted by the original lower-height test. -/
def positiveLowCuspRows (r : ℝ) (z : UpperHalfPlane) : ℝ :=
  ∑' v : gammaSetHalf, if (gammaSetMatrix v.1 • z).im ≤ 1/2 then
    (gammaSetMatrix v.1 • z).im ^ r else 0

theorem positiveCuspRows_nonneg (r : ℝ) (z : UpperHalfPlane) : 0 ≤ positiveCuspRows r z :=
  tsum_nonneg (fun v => Real.rpow_nonneg (gammaSetMatrix v.1 • z).im_pos.le r)

theorem positiveLowCuspRows_nonneg (r : ℝ) (z : UpperHalfPlane) : 0 ≤ positiveLowCuspRows r z := by
  apply tsum_nonneg
  intro v
  split_ifs
  · exact Real.rpow_nonneg (gammaSetMatrix v.1 • z).im_pos.le r
  · exact le_rfl

theorem positiveCuspRows_summable (r : ℝ) (hr : 1 < r) (z : UpperHalfPlane) :
    Summable (fun v : gammaSetHalf => (gammaSetMatrix v.1 • z).im ^ r) := by
  have hs := (cuspHeightPower_rows_summable ⟨(r:ℂ),hr⟩ z).norm
  exact hs.congr (fun v => by rw [Complex.norm_cpow_eq_rpow_re_of_pos (gammaSetMatrix v.1 • z).im_pos]; rfl)

theorem positiveLowCuspRows_summable (r : ℝ) (hr : 1 < r) (z : UpperHalfPlane) :
    Summable (fun v : gammaSetHalf => if (gammaSetMatrix v.1 • z).im ≤ 1/2 then
      (gammaSetMatrix v.1 • z).im ^ r else 0) := by
  apply (positiveCuspRows_summable r hr z).of_nonneg_of_le
  · intro v
    split_ifs
    · exact Real.rpow_nonneg (gammaSetMatrix v.1 • z).im_pos.le r
    · exact le_rfl
  · intro v
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (gammaSetMatrix v.1 • z).im_pos.le r

theorem lowCuspPower_norm (s : ℂ) {y : ℝ} (hy : 0 < y) :
    ‖lowCuspPower s y‖ = if y ≤ 1/2 then y ^ s.re else 0 := by
  unfold lowCuspPower
  split_ifs
  · exact Complex.norm_cpow_eq_rpow_re_of_pos hy s
  · exact norm_zero

/-- Every complex lower-kernel orbit is controlled by the positive sum at its actual real part. -/
theorem lowCuspPower_periodize_norm_le (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (z : UpperHalfPlane) :
    ‖periodize (cuspHeightSeed (lowCuspPower P.s)) z‖ ≤ positiveLowCuspRows P.s.re z := by
  rw [periodize_cuspHeightSeed_eq_rows_of_rows_summable (lowCuspPower P.s) z (lowCuspPower_rows_summable P z)]
  have hn := norm_tsum_le_tsum_norm (lowCuspPower_rows_summable P z).norm
  simpa only [positiveLowCuspRows,lowCuspPower_norm (s := P.s) (gammaSetMatrix _ • z).im_pos] using hn

/-- Complexification of the positive full sum is exactly the admitted original power orbit. -/
theorem positiveCuspRows_coe (r : ℝ) (hr : 1 < r) (z : UpperHalfPlane) :
    (positiveCuspRows r z : ℂ) = periodize (cuspHeightSeed (fun y : ℝ => (y:ℂ)^(r:ℂ))) z := by
  rw [periodize_cuspHeightSeed_eq_rows_of_rows_summable (fun y : ℝ => (y:ℂ)^(r:ℂ)) z (cuspHeightPower_rows_summable ⟨(r:ℂ),hr⟩ z),
    positiveCuspRows,Complex.ofReal_tsum]
  exact tsum_congr (fun v => Complex.ofReal_cpow (gammaSetMatrix v.1 • z).im_pos.le r)

/-- Complexification also preserves the full original lower-height cutoff. -/
theorem positiveLowCuspRows_coe (r : ℝ) (hr : 1 < r) (z : UpperHalfPlane) :
    (positiveLowCuspRows r z : ℂ) = periodize (cuspHeightSeed (lowCuspPower (r:ℂ))) z := by
  rw [periodize_cuspHeightSeed_eq_rows_of_rows_summable (lowCuspPower (r:ℂ)) z (lowCuspPower_rows_summable ⟨(r:ℂ),hr⟩ z),
    positiveLowCuspRows,Complex.ofReal_tsum]
  apply tsum_congr
  intro v
  unfold lowCuspPower
  split_ifs
  · exact Complex.ofReal_cpow (gammaSetMatrix v.1 • z).im_pos.le r
  · rfl

/-- The real positive majorant retains the actual completed Eisenstein normalization. -/
theorem positiveCuspRows_completed (r : ℝ) (hr : 1 < r) (z : UpperHalfPlane) :
    reflectedCompletedLambda (2*(r:ℂ))*(positiveCuspRows r z:ℂ) =
      D4BMGlobalAngularResponse.scalar ((r:ℂ)-1/2) (coordinates z) := by
  rw [positiveCuspRows_coe r hr]
  exact cuspHeightPower_periodize_completed ⟨(r:ℂ),hr⟩ z

/-- A genuine bound on the original high profile controls its entire orbit, with no image removed. -/
theorem highCuspHeight_periodize_norm_le (h : ℝ → ℂ) (hh : ∀ y ≤ 2, h y = 0)
    (C : ℝ) (hb : ∀ y : ℝ, ‖h y‖ ≤ C*y^(2 : ℕ)) (z : UpperHalfPlane) :
    ‖periodize (cuspHeightSeed h) z‖ ≤ C*positiveCuspRows 2 z := by
  rw [periodize_cuspHeightSeed_eq_rows h hh z]
  calc
    _ ≤ ∑' v : gammaSetHalf, ‖h (gammaSetMatrix v.1 • z).im‖ :=
      norm_tsum_le_tsum_norm (cuspHeight_rows_summable h hh z).norm
    _ ≤ ∑' v : gammaSetHalf, C*(gammaSetMatrix v.1 • z).im^(2:ℝ) := by
      apply Summable.tsum_le_tsum
      · intro v
        simpa only [Real.rpow_two] using hb (gammaSetMatrix v.1 • z).im
      · exact (cuspHeight_rows_summable h hh z).norm
      · exact (positiveCuspRows_summable 2 (by norm_num) z).mul_left C
    _ = C*positiveCuspRows 2 z := tsum_mul_left

end
end RHTower.D4BMModularCore

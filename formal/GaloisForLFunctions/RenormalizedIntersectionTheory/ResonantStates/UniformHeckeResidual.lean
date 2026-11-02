import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.HeckeCutoffSource

/-!
# A Hecke residual gap uniform in cutoff height

Near cutoff one, the central-return rectangle retains its full residual. At
larger cutoffs, a high cusp band has no modular return and carries a single
Weyl term. These two regions prevent cutoff choices from producing Hecke
quasimodes at a fixed negative real parameter.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

private theorem core_return_height_margin {z : ℍ} (hz : z ∈ coreRectangle) :
    33 / 32 < returnHeight 0 z := by
  have hx := abs_le.mp hz.1
  have hylo := hz.2.1
  have hyhi := hz.2.2
  have hx2 : z.re ^ 2 ≤ 1 / 16 := by nlinarith only [hx.1, hx.2]
  have hc := mul_nonpos_of_nonneg_of_nonpos
    (sub_nonneg.mpr hylo) (sub_nonpos.mpr hyhi)
  have hd : 0 < z.re ^ 2 + z.im ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos z.im_pos)
  simp only [returnHeight, Int.cast_zero, add_zero]
  rw [lt_div_iff₀ hd]
  nlinarith only [hc, hx2, hyhi]

/-- A whole interval of cutoffs leaves the core residual unchanged. -/
theorem dyadicEigenResidualAt_eq_one_on_core {u : ℂ} (hAu : msA u = 0)
    {Y : ℝ} (hY : 1 ≤ Y) (hYhi : Y ≤ 33 / 32)
    {z : ℍ} (hz : z ∈ coreRectangle) :
    dyadicEigenResidualAt u Y z = dyadicEigenResidual u z := by
  have h0 : Y < returnHeight 0 z := hYhi.trans_lt (core_return_height_margin hz)
  obtain ⟨_, h1, hm⟩ := coreRectangle_returns hz
  have hs : dyadicReturnSource u Y z = dyadicReturnDefect u z := by
    rw [dyadicReturnDefect_on_core hAu hz]
    simp only [dyadicReturnSource, dyadicReturnPower, if_pos h0,
      if_neg (not_lt.mpr (h1.trans hY)), if_neg (not_lt.mpr (hm.trans hY)), add_zero]
  rw [dyadicEigenResidualAt_eq hAu hY (coreRectangle_subset_fd hz), hs,
    heckeRemainder_eq_upperBand (p := 2) (by norm_num) u (by linarith)
      (by linarith [hz.2.1]) (by linarith [hz.2.2]),
    upperBandRemainder_resonant (by norm_num) hAu,
    dyadicEigenResidual_on_core hAu hz]

private theorem returnHeight_le_one_of_two_le (k : ℤ) {z : ℍ} (hz : 2 ≤ z.im) :
    returnHeight k z ≤ 1 := by
  have hd : 0 < (z.re + k) ^ 2 + z.im ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos z.im_pos)
  rw [returnHeight, div_le_one hd]
  have hm := mul_nonneg (sub_nonneg.mpr hz) z.im_pos.le
  nlinarith only [hm, sq_nonneg (z.re + k)]

/-- Above height two, an upper-band residual is exactly its direct Weyl source. -/
theorem dyadicEigenResidualAt_eq_upperBand {u : ℂ} (hAu : msA u = 0)
    {Y : ℝ} (hY : 1 ≤ Y) {z : ℍ} (hz : z ∈ fd) (hz2 : 2 ≤ z.im)
    (hylo : Y < z.im) (hyhi : z.im ≤ 2 * Y) :
    dyadicEigenResidualAt u Y z = upperBandRemainder 2 u z.im := by
  rw [dyadicEigenResidualAt_eq hAu hY hz,
    heckeRemainder_eq_upperBand (p := 2) (by norm_num) u (by linarith) hylo (by linarith)]
  have hn (k : ℤ) : ¬ Y < returnHeight k z :=
    not_lt.mpr ((returnHeight_le_one_of_two_le k hz2).trans hY)
  simp only [dyadicReturnSource, dyadicReturnPower, if_neg (hn 0), if_neg (hn 1),
    if_neg (hn (-1)), add_zero, mul_zero, sub_zero]

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

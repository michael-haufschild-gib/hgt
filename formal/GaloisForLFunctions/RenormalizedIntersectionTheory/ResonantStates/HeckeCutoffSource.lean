import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.CoreHeckeResidual

/-!
# The automorphic dyadic source at every cutoff height

At any cutoff at least one, the correction to the coordinate Hecke formula has
the same three modular return branches. Their heights are at most two on the
fundamental domain, so the correction disappears at cutoffs at least two.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup EisensteinSeries
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-- The genuine Hecke eigen-equation residual at an arbitrary cutoff. -/
def dyadicEigenResidualAt (u : ℂ) (Y : ℝ) (z : ℍ) : ℂ :=
  dyadicHecke (automorphicTruncation u Y) z -
    ((2 : ℂ) ^ u + (2 : ℂ) ^ (-u)) * automorphicTruncation u Y z

theorem dyadicEigenResidualAt_one (u : ℂ) (z : ℍ) :
    dyadicEigenResidualAt u 1 z = dyadicEigenResidual u z := rfl

private theorem dyadicHecke_sub (F G : ℍ → ℂ) (z : ℍ) :
    dyadicHecke (fun w => F w - G w) z = dyadicHecke F z - dyadicHecke G z := by
  unfold dyadicHecke
  ring

private theorem dyadicHecke_height (f : ℝ → ℂ) (z : ℍ) :
    dyadicHecke (fun w => f w.im) z =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (f (2 * z.im) + 2 * f (z.im / 2)) := by
  simp [dyadicHecke, dyadicUpper, dyadicLower]
  ring

/-- The three modular returns are independent of the chosen height profile. -/
theorem dyadicHecke_cuspLift (f : ℝ → ℂ) (hf : ∀ y ≤ 1, f y = 0)
    {z : ℍ} (hz : z ∈ fd) :
    dyadicHecke (cuspLift f) z = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
      (f (2 * z.im) + 2 * f (z.im / 2) +
        (f (returnHeight 0 z) + f (returnHeight 1 z) + f (returnHeight (-1) z))) := by
  rw [dyadicHecke, cuspLift_upper f hf hz, cuspLift_lower_zero f hf hz,
    cuspLift_lower_one f hf hz]
  ring

/-- Exact automorphic correction for every cutoff at least one. -/
theorem automorphic_dyadic_correction_at (u : ℂ) {Y : ℝ} (hY : 1 ≤ Y)
    {z : ℍ} (hz : z ∈ fd) :
    dyadicHecke (automorphicTruncation u Y) z = heckeTruncated 2 u Y z -
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
        ((if Y < returnHeight 0 z then
            d4BMCompletedEisensteinCuspConstantPart .scalar u (returnHeight 0 z) else 0) +
          (if Y < returnHeight 1 z then
            d4BMCompletedEisensteinCuspConstantPart .scalar u (returnHeight 1 z) else 0) +
          (if Y < returnHeight (-1) z then
            d4BMCompletedEisensteinCuspConstantPart .scalar u (returnHeight (-1) z) else 0)) := by
  let f : ℝ → ℂ := fun y =>
    if Y < y then d4BMCompletedEisensteinCuspConstantPart .scalar u y else 0
  have hf (y : ℝ) (hy : y ≤ 1) : f y = 0 := if_neg (not_lt.mpr (hy.trans hY))
  rw [← dyadicHecke_coordinate]
  change dyadicHecke (fun w => eisensteinLineModel u w - cuspLift f w) z =
    dyadicHecke (fun w => eisensteinLineModel u w - f w.im) z -
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
        (f (returnHeight 0 z) + f (returnHeight 1 z) + f (returnHeight (-1) z))
  rw [dyadicHecke_sub, dyadicHecke_sub, dyadicHecke_cuspLift f hf hz, dyadicHecke_height]
  ring

/-- A surviving cusp power at one modular return. -/
def dyadicReturnPower (u : ℂ) (Y : ℝ) (k : ℤ) (z : ℍ) : ℂ :=
  if Y < returnHeight k z then (returnHeight k z : ℂ) ^ (1 / 2 - u) else 0

/-- The complete modular return source at cutoff `Y`. -/
def dyadicReturnSource (u : ℂ) (Y : ℝ) (z : ℍ) : ℂ :=
  ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * msB u) *
    (dyadicReturnPower u Y 0 z + dyadicReturnPower u Y 1 z + dyadicReturnPower u Y (-1) z)

/-- The actual residual is the coordinate remainder minus the modular return source. -/
theorem dyadicEigenResidualAt_eq {u : ℂ} (hAu : msA u = 0) {Y : ℝ} (hY : 1 ≤ Y)
    {z : ℍ} (hz : z ∈ fd) :
    dyadicEigenResidualAt u Y z = heckeRemainder 2 u Y z.im - dyadicReturnSource u Y z := by
  rw [dyadicEigenResidualAt, automorphic_dyadic_correction_at u hY hz,
    automorphicTruncation_eq_of_mem_fd u hY hz, heckeTruncated_eq Nat.prime_two]
  simp only [cuspConstantPart_eq_msAB, hAu, zero_mul, add_zero,
    dyadicReturnSource, dyadicReturnPower]
  split_ifs <;> ring

theorem returnHeight_pos (k : ℤ) (z : ℍ) : 0 < returnHeight k z :=
  div_pos (mul_pos (by norm_num) z.im_pos)
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos z.im_pos))

/-- Every dyadic modular return from the fundamental domain has height at most two. -/
theorem returnHeight_le_two (k : ℤ) {z : ℍ} (hz : z ∈ fd) : returnHeight k z ≤ 2 := by
  let v : gammaSet 1 1 0 := ⟨![1, k], (gammaSet_one_mem_iff 1 _).mpr (by simp)⟩
  have hv : v.1 0 ≠ 0 := by simp [v]
  have hb := rowHeight_le_one_of_mem_fd hz hv
  have he : returnHeight k z = 2 * rowHeight v z := by
    rw [rowHeight_eq_div, normSq_int_mul_add]
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Int.cast_one, one_mul, returnHeight]
    ring
  rw [he]
  linarith

theorem returnHeight_continuous (k : ℤ) : Continuous (returnHeight k) :=
  (continuous_const.mul UpperHalfPlane.continuous_im).div
    (((UpperHalfPlane.continuous_re.add continuous_const).pow 2).add
      (UpperHalfPlane.continuous_im.pow 2))
    (fun z => (add_pos_of_nonneg_of_pos (sq_nonneg _)
      (sq_pos_of_pos z.im_pos)).ne')

/-- At cutoffs at least two the coordinate and automorphic remainders coincide. -/
theorem dyadicEigenResidualAt_eq_heckeRemainder {u : ℂ} (hAu : msA u = 0)
    {Y : ℝ} (hY : 2 ≤ Y) {z : ℍ} (hz : z ∈ fd) :
    dyadicEigenResidualAt u Y z = heckeRemainder 2 u Y z.im := by
  rw [dyadicEigenResidualAt_eq hAu (by linarith) hz]
  have hn (k : ℤ) : ¬ Y < returnHeight k z := not_lt.mpr ((returnHeight_le_two k hz).trans hY)
  simp only [dyadicReturnSource, dyadicReturnPower, if_neg (hn 0), if_neg (hn 1),
    if_neg (hn (-1)), add_zero, mul_zero, sub_zero]

theorem dyadicReturnPower_measurable (u : ℂ) (Y : ℝ) (k : ℤ) :
    Measurable (dyadicReturnPower u Y k) := by
  unfold dyadicReturnPower
  exact Measurable.ite
    (measurableSet_lt measurable_const (returnHeight_continuous k).measurable)
    (((Complex.continuous_ofReal.comp (returnHeight_continuous k)).measurable).pow_const _)
    measurable_const

theorem dyadicReturnSource_measurable (u : ℂ) (Y : ℝ) : Measurable (dyadicReturnSource u Y) :=
  measurable_const.mul (((dyadicReturnPower_measurable u Y 0).add
    (dyadicReturnPower_measurable u Y 1)).add (dyadicReturnPower_measurable u Y (-1)))

private theorem dyadicReturnPower_norm_le {u : ℂ} (hur : u.re < 0)
    (Y : ℝ) (k : ℤ) {z : ℍ} (hz : z ∈ fd) :
    ‖dyadicReturnPower u Y k z‖ ≤ (2 : ℝ) ^ (1 / 2 - u.re) := by
  unfold dyadicReturnPower
  split_ifs
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos (returnHeight_pos k z), half_sub_re]
    exact Real.rpow_le_rpow (returnHeight_pos k z).le (returnHeight_le_two k hz) (by linarith)
  · rw [norm_zero]
    exact (Real.rpow_pos_of_pos (by norm_num) _).le

private theorem dyadicReturnSource_norm_le {u : ℂ} (hur : u.re < 0)
    (Y : ℝ) {z : ℍ} (hz : z ∈ fd) :
    ‖dyadicReturnSource u Y z‖ ≤ ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * msB u‖ *
      (3 * (2 : ℝ) ^ (1 / 2 - u.re)) := by
  have hb0 := dyadicReturnPower_norm_le hur Y 0 hz
  have hb1 := dyadicReturnPower_norm_le hur Y 1 hz
  have hbm := dyadicReturnPower_norm_le hur Y (-1) hz
  have hs : ‖dyadicReturnPower u Y 0 z + dyadicReturnPower u Y 1 z +
      dyadicReturnPower u Y (-1) z‖ ≤ 3 * (2 : ℝ) ^ (1 / 2 - u.re) := by
    have h0 := norm_add_le (dyadicReturnPower u Y 0 z) (dyadicReturnPower u Y 1 z)
    have h1 := norm_add_le (dyadicReturnPower u Y 0 z + dyadicReturnPower u Y 1 z)
      (dyadicReturnPower u Y (-1) z)
    linarith
  rw [dyadicReturnSource, norm_mul]
  exact mul_le_mul_of_nonneg_left hs (norm_nonneg _)

/-- The full automorphic residual is square integrable on the fundamental domain. -/
theorem dyadicEigenResidualAt_integrable_norm_sq {u : ℂ}
    (hur : u.re < 0) (hAu : msA u = 0) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun z => ‖dyadicEigenResidualAt u Y z‖ ^ 2) fd := by
  obtain ⟨M, _, hM⟩ := exists_bound_heckeRemainder (p := 2) (by norm_num) u
    (show 0 < Y by linarith)
  let C : ℝ := ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * msB u‖ *
    (3 * (2 : ℝ) ^ (1 / 2 - u.re))
  let q : ℍ → ℂ := fun z => heckeRemainder 2 u Y z.im - dyadicReturnSource u Y z
  have hq : Measurable q := (measurable_heckeRemainder_im 2 u Y).sub
    (dyadicReturnSource_measurable u Y)
  have hb (z : ℍ) (hz : z ∈ fd) : ‖q z‖ ≤ M + C :=
    (norm_sub_le _ _).trans (add_le_add (hM z.im) (dyadicReturnSource_norm_le hur Y hz))
  have hi : IntegrableOn (fun z => ‖q z‖ ^ 2) fd := by
    refine Measure.integrableOn_of_bounded volume_fd_ne_top
      (hq.norm.pow_const (2 : ℕ)).aestronglyMeasurable (M := (M + C) ^ 2) ?_
    refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr
      (Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb z hz) 2
  refine hi.congr ((ae_restrict_iff' isClosed_fd.measurableSet).mpr
    (Eventually.of_forall fun z hz => ?_))
  rw [dyadicEigenResidualAt_eq hAu hY hz]

/-- Above cutoff two, the normalized full residual has an exact height-independent mass. -/
theorem dyadicEigenResidualAt_mass_of_two_le {u : ℂ}
    (hu : u ∈ eisensteinLineDomain) (hur : u.re < 0) (hAu : msA u = 0)
    {Y : ℝ} (hY : 2 ≤ Y) :
    (∫ z in fd, ‖dyadicEigenResidualAt u Y z‖ ^ 2) =
      (∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2) *
        ((2 : ℝ) ^ (-2 * u.re) - (2 : ℝ) ^ (2 * u.re)) := by
  calc
    _ = ∫ z in fd, ‖heckeRemainder 2 u Y z.im‖ ^ 2 :=
      setIntegral_congr_fun isClosed_fd.measurableSet
        (fun z hz => by rw [dyadicEigenResidualAt_eq_heckeRemainder hAu hY hz])
    _ = _ := by
      have hc := setIntegral_fd_normSq_heckeRemainder (p := 2) (by norm_num) hur hAu hY
      rw [integral_complex_ofReal] at hc
      rw [integral_norm_sq_of_msA_eq_zero hu hur hAu (by linarith)]
      exact Complex.ofReal_injective hc

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

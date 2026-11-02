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
      (by linarith [hz.2.1]) (by norm_num only [Nat.cast_ofNat]; linarith [hz.2.2]),
    upperBandRemainder_resonant (by norm_num) hAu,
    dyadicEigenResidual_on_core hAu hz]
  norm_num only [Nat.cast_ofNat]

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
    heckeRemainder_eq_upperBand (p := 2) (by norm_num) u (by linarith) hylo
      (by norm_num only [Nat.cast_ofNat]; linarith)]
  have hn (k : ℤ) : ¬ Y < returnHeight k z :=
    not_lt.mpr ((returnHeight_le_one_of_two_le k hz2).trans hY)
  simp only [dyadicReturnSource, dyadicReturnPower, if_neg (hn 0), if_neg (hn 1),
    if_neg (hn (-1)), add_zero, mul_zero, sub_zero]

/-- A quadratic height test cancels the hyperbolic density on a cusp band. -/
private theorem quadratic_band_integral {L U : ℝ} (hL : 1 ≤ L) (hLU : L ≤ U) (C : ℝ) :
    (∫ z in fd, if L < z.im ∧ z.im ≤ U then C * z.im ^ 2 else 0) = C * (U - L) := by
  have h := setIntegral_fd_height (Y₂ := U) hL (fun y => ((C * y ^ 2 : ℝ) : ℂ))
    ((Complex.continuous_ofReal.comp (continuous_const.mul (continuous_id.pow 2))).continuousOn)
  have he : (fun z : ℍ => if L < z.im ∧ z.im ≤ U then ((C * z.im ^ 2 : ℝ) : ℂ) else 0) =
      fun z => ((if L < z.im ∧ z.im ≤ U then C * z.im ^ 2 else 0 : ℝ) : ℂ) := by
    funext z
    split_ifs <;> rfl
  rw [he, integral_complex_ofReal] at h
  have hr : (∫ y in Ioc L U, ((C * y ^ 2 : ℝ) : ℂ) / (y : ℂ) ^ 2) =
      ((C * (U - L) : ℝ) : ℂ) := by
    calc
      _ = ∫ _ in Ioc L U, (C : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
        have hy0 : y ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
          (hL.trans hy.1.le))
        push_cast
        field_simp [Complex.ofReal_ne_zero.mpr hy0]
      _ = _ := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hLU, Complex.real_smul]
        push_cast
        ring
  exact Complex.ofReal_injective (h.trans hr)

private theorem quadratic_band_integrable {L U C : ℝ} (hC : 0 ≤ C) :
    IntegrableOn (fun z : ℍ => if L < z.im ∧ z.im ≤ U then C * z.im ^ 2 else 0) fd := by
  have hm : Measurable (fun z : ℍ => if L < z.im ∧ z.im ≤ U then C * z.im ^ 2 else 0) :=
    Measurable.ite (measurableSet_band L U)
      (measurable_const.mul (UpperHalfPlane.continuous_im.measurable.pow_const (2 : ℕ)))
      measurable_const
  refine Measure.integrableOn_of_bounded volume_fd_ne_top hm.aestronglyMeasurable
    (M := C * U ^ 2) (Eventually.of_forall fun z => ?_)
  split_ifs with hz
  · rw [Real.norm_of_nonneg (mul_nonneg hC (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ z.im_pos.le hz.2 2) hC
  · simp only [norm_zero]
    exact mul_nonneg hC (sq_nonneg _)

private theorem upperBand_quadratic_lower {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    (hur : u.re < 0) (hAu : msA u = 0) {Y y : ℝ} (hY : 0 < Y)
    (hy : Y ≤ y) (hyhi : y ≤ 2 * Y) :
    (‖msB u‖ ^ 2 * Y ^ (-2 * u.re) / (4 * Y)) * y ^ 2 ≤
      ‖upperBandRemainder 2 u y‖ ^ 2 := by
  have hy0 : 0 < y := hY.trans_le hy
  have hp : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (2 * u.re) := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (-1 : ℝ) ≤ 2 * u.re by linarith [hu.1])
    norm_num at hh ⊢
    exact hh
  have hq : Y ^ (-2 * u.re) ≤ y ^ (-2 * u.re) :=
    Real.rpow_le_rpow hY.le hy (by linarith)
  have he : y ^ (1 - 2 * u.re) = y * y ^ (-2 * u.re) := by
    rw [show 1 - 2 * u.re = 1 + (-2 * u.re) by ring, Real.rpow_add hy0, Real.rpow_one]
  rw [norm_sq_upperBandRemainder_resonant (by norm_num) hAu hy0, he]
  norm_num only [Nat.cast_ofNat]
  have hb := sq_nonneg ‖msB u‖
  have hYp := (Real.rpow_pos_of_pos hY (-2 * u.re)).le
  have hprod := mul_le_mul hp hq hYp (Real.rpow_pos_of_pos (by norm_num) _).le
  have hmid : ‖msB u‖ ^ 2 * y * ((1 / 2) * Y ^ (-2 * u.re)) ≤
      ‖msB u‖ ^ 2 * (2 : ℝ) ^ (2 * u.re) * (y * y ^ (-2 * u.re)) := by
    nlinarith only [mul_le_mul_of_nonneg_left hprod (mul_nonneg hb hy0.le)]
  apply le_trans _ hmid
  rw [show (‖msB u‖ ^ 2 * Y ^ (-2 * u.re) / (4 * Y)) * y ^ 2 =
    (‖msB u‖ ^ 2 * Y ^ (-2 * u.re) * y ^ 2) / (4 * Y) by ring,
    div_le_iff₀ (show 0 < 4 * Y by positivity)]
  have hh := mul_nonneg (mul_nonneg (mul_nonneg hb hYp) hy0.le)
    (sub_nonneg.mpr hyhi)
  nlinarith only [hh]

/-- A high cusp band retains a fixed fraction of the resonant norm at every larger cutoff. -/
theorem dyadicEigenResidualAt_large_cutoff_mass_lower {u : ℂ}
    (hu : u ∈ eisensteinLineDomain) (hur : u.re < 0) (hAu : msA u = 0)
    {Y : ℝ} (hY : 33 / 32 ≤ Y) :
    ‖msB u‖ ^ 2 * Y ^ (-2 * u.re) / 256 ≤ ∫ z in fd, ‖dyadicEigenResidualAt u Y z‖ ^ 2 := by
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  let L : ℝ := 63 * Y / 32
  let U : ℝ := 127 * Y / 64
  let C : ℝ := ‖msB u‖ ^ 2 * Y ^ (-2 * u.re) / (4 * Y)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hLU : L ≤ U := by dsimp [L, U]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hi := quadratic_band_integrable (L := L) (U := U) hC
  have hb := setIntegral_mono_on hi (dyadicEigenResidualAt_integrable_norm_sq hur hAu hY1)
    isClosed_fd.measurableSet (fun z hz => show
      (if L < z.im ∧ z.im ≤ U then C * z.im ^ 2 else 0) ≤ ‖dyadicEigenResidualAt u Y z‖ ^ 2 from by
        split_ifs with hy
        · have hz2 : 2 ≤ z.im := by dsimp [L] at hy; linarith
          have hylo : Y < z.im := by dsimp [L] at hy; linarith
          have hyhi : z.im ≤ 2 * Y := by dsimp [U] at hy; linarith
          rw [dyadicEigenResidualAt_eq_upperBand hAu hY1 hz hz2 hylo hyhi]
          exact upperBand_quadratic_lower hu hur hAu hY0 hylo.le hyhi
        · exact sq_nonneg _)
  rw [quadratic_band_integral hL hLU C] at hb
  have he : C * (U - L) = ‖msB u‖ ^ 2 * Y ^ (-2 * u.re) / 256 := by
    dsimp [C, U, L]
    field_simp [hY0.ne']
    ring
  rwa [he] at hb

/-- The compact-core source remains uniformly nonzero for cutoffs close to one. -/
theorem dyadicEigenResidualAt_small_cutoff_mass_lower {u : ℂ}
    (hu : u ∈ eisensteinLineDomain) (hur : u.re < 0) (hAu : msA u = 0)
    {Y : ℝ} (hY : 1 ≤ Y) (hYhi : Y ≤ 33 / 32) :
    ‖msB u‖ ^ 2 / 512 ≤ ∫ z in fd, ‖dyadicEigenResidualAt u Y z‖ ^ 2 := by
  have hm : MeasurableSet coreRectangle :=
    (measurableSet_le UpperHalfPlane.continuous_re.abs.measurable measurable_const).inter
      ((measurableSet_le measurable_const UpperHalfPlane.continuous_im.measurable).inter
        (measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const))
  have he : (∫ z in coreRectangle, ‖dyadicEigenResidualAt u Y z‖ ^ 2) =
      ∫ z in coreRectangle, ‖dyadicEigenResidual u z‖ ^ 2 :=
    setIntegral_congr_fun hm fun z hz => by rw [dyadicEigenResidualAt_eq_one_on_core hAu hY hYhi hz]
  have hb := setIntegral_mono_set (s := coreRectangle)
    (dyadicEigenResidualAt_integrable_norm_sq hur hAu hY)
    (Eventually.of_forall fun z => sq_nonneg ‖dyadicEigenResidualAt u Y z‖)
    (Eventually.of_forall fun z hz => coreRectangle_subset_fd hz)
  rw [he] at hb
  exact (dyadicEigenResidual_core_mass_lower hu hur hAu).trans hb

/-- No cutoff at least one removes the full automorphic Hecke source at a negative rate. -/
theorem dyadicEigenResidualAt_uniform_mass_lower {u : ℂ}
    (hu : u ∈ eisensteinLineDomain) (hur : u.re < 0) (hAu : msA u = 0)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (-2 * u.re) / 1024 * (∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2) ≤
      ∫ z in fd, ‖dyadicEigenResidualAt u Y z‖ ^ 2 := by
  have hY0 : 0 < Y := by linarith
  have he : (-2 * u.re) / 1024 * (∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2) =
      ‖msB u‖ ^ 2 * Y ^ (-2 * u.re) / 1024 := by
    rw [integral_norm_sq_of_msA_eq_zero hu hur hAu hY]
    have hne : u.re ≠ 0 := hur.ne
    field_simp
  rw [he]
  by_cases hYhi : Y ≤ 33 / 32
  · have hp : Y ^ (-2 * u.re) ≤ 2 := by
      have hb := Real.rpow_le_rpow_of_exponent_le hY (show -2 * u.re ≤ 1 by linarith [hu.1])
      rw [Real.rpow_one] at hb
      linarith
    have hh := mul_le_mul_of_nonneg_left hp (sq_nonneg ‖msB u‖)
    exact (show ‖msB u‖ ^ 2 * Y ^ (-2 * u.re) / 1024 ≤ ‖msB u‖ ^ 2 / 512 by linarith only [hh]).trans
      (dyadicEigenResidualAt_small_cutoff_mass_lower hu hur hAu hY hYhi)
  · have hb := dyadicEigenResidualAt_large_cutoff_mass_lower hu hur hAu (not_le.mp hYhi).le
    have hp := mul_nonneg (sq_nonneg ‖msB u‖) (Real.rpow_pos_of_pos hY0 (-2 * u.re)).le
    linarith only [hb, hp]

#print axioms dyadicEigenResidualAt_uniform_mass_lower
#print axioms dyadicEigenResidualAt_integrable_norm_sq
#print axioms dyadicEigenResidualAt_mass_of_two_le

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

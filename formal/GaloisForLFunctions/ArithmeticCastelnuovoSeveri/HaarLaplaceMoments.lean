import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellPoleBound

/-!
# Oriented Laplace moments of the actual Haar cells

Each balanced cell changes sign once and has zero mean. Increasing
weights therefore have nonpositive moments. The two exponential moments
that factor an ordered Gamma interaction have fixed opposite signs.
-/

noncomputable section
open MeasureTheory Set Filter
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry

/-- An increasing weight has a nonpositive moment against the oriented balanced cell. -/
theorem haarProfile_moment_nonpos_of_monotone {a : ℕ} (ha : 1 ≤ a)
    {w : ℝ → ℝ} (hc : Continuous w) (hw : Monotone w) :
    (∫ x, haarProfile a x * w x) ≤ 0 := by
  let c := Real.log ((2 * a + 1 : ℕ) : ℝ)
  have hi := integrable_compact_bv_mul (haarProfile_bv a) (haarProfile_compact a) hc
  have hq := (integrable_haarProfile a).mul_const (w c)
  have he : (∫ x, haarProfile a x * w x) =
      ∫ x, haarProfile a x * (w x - w c) := by
    simp_rw [mul_sub]
    rw [integral_sub hi hq, integral_mul_const, integral_haarProfile ha,
      zero_mul, sub_zero]
  rw [he]
  apply integral_nonpos
  intro x
  unfold haarProfile rawCell
  simp only [indicator_apply]
  split_ifs with hl hr hr
  · exact ((not_lt_of_ge hr.1) hl.2).elim
  · simp only [mul_one, mul_zero, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (haarCoeff_nonneg ha).1
      (sub_nonpos.mpr (hw hl.2.le))
  · simp only [mul_one, mul_zero, zero_sub]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (haarCoeff_nonneg ha).2)
      (sub_nonneg.mpr (hw hr.1))
  · simp only [mul_zero, sub_zero, zero_mul, Pi.zero_apply]

/-- The nonnegative left factor of an ordered Gamma interaction. -/
def haarLaplaceLeft (a : ℕ) (r : ℝ) : ℝ :=
  -(∫ x, haarProfile a x * Real.exp (r * x))

/-- The nonnegative right factor of an ordered Gamma interaction. -/
def haarLaplaceRight (a : ℕ) (r : ℝ) : ℝ :=
  ∫ x, haarProfile a x * Real.exp (-r * x)

theorem haarLaplaceLeft_nonneg {a : ℕ} (ha : 1 ≤ a) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ haarLaplaceLeft a r := by
  apply neg_nonneg.mpr
  exact haarProfile_moment_nonpos_of_monotone ha
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    (fun _ _ hxy => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxy hr))

theorem haarLaplaceRight_nonneg {a : ℕ} (ha : 1 ≤ a) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ haarLaplaceRight a r := by
  have hc : Continuous (fun x : ℝ => -Real.exp (-r * x)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).neg
  have hm : Monotone (fun x : ℝ => -Real.exp (-r * x)) := by
    intro x y hxy
    apply neg_le_neg
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hxy (neg_nonpos.mpr hr)
  have h := haarProfile_moment_nonpos_of_monotone ha hc hm
  simp only [mul_neg, integral_neg] at h
  exact neg_nonpos.mp h

/-- Compact support makes every real exponential moment integrable. -/
theorem integrable_haarProfile_mul_exp (a : ℕ) (r : ℝ) :
    Integrable (fun x => haarProfile a x * Real.exp (r * x)) :=
  integrable_compact_bv_mul (haarProfile_bv a) (haarProfile_compact a)
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))

/-- Restricting a Haar moment to its open pair removes only a null endpoint. -/
theorem setIntegral_haarProfile_mul_eq {a : ℕ} (ha : 1 ≤ a) (w : ℝ → ℝ) :
    (∫ x in Ioo (Real.log ((2 * a : ℕ) : ℝ))
      (Real.log ((2 * a + 2 : ℕ) : ℝ)), haarProfile a x * w x) =
        ∫ x, haarProfile a x * w x := by
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (Real.log ((2 * a : ℕ) : ℝ))] with x hne
  by_cases hx : x ∈ Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx, haarProfile_zero_outside_pair ha, zero_mul]
    intro hin
    exact hx ⟨lt_of_le_of_ne hin.1 hne.symm, hin.2⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

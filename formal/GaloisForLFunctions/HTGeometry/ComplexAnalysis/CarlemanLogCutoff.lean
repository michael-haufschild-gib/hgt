import GaloisForLFunctions.RHTower.ThetaCompactStripZeroEngineering

/-!
# A fixed smooth cutoff in logarithmic radius

Translate the compact even bump to a profile supported in `[1,5]`, equal to one at `3`.
The shift makes the profile vanish at `0`, so composition with Lean's total logarithm also
vanishes at the spatial origin. Every positive real power has positive finite mass, and every
positive power of the derivative is integrable.
-/

open MeasureTheory Set

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Fixed compact profile for logarithmic radial localization. -/
def carlemanLogCutoff (t : ℝ) : ℝ := RHTower.compactWeight (t - 3)

theorem contDiff_carlemanLogCutoff : ContDiff ℝ (⊤ : ℕ∞) carlemanLogCutoff :=
  RHTower.contDiff_compactWeight.comp (contDiff_id.sub contDiff_const)

theorem carlemanLogCutoff_nonneg (t : ℝ) : 0 ≤ carlemanLogCutoff t :=
  RHTower.compactWeight_nonneg _

theorem carlemanLogCutoff_three : carlemanLogCutoff 3 = 1 := by
  exact RHTower.compactWeight_eq_one (by norm_num)

/-- The logarithmic profile vanishes outside its fixed interval. -/
theorem carlemanLogCutoff_eq_zero {t : ℝ} (ht : t ≤ 1 ∨ 5 ≤ t) :
    carlemanLogCutoff t = 0 := by
  apply RHTower.compactWeight_eq_zero
  rcases ht with ht | ht
  · have h := neg_le_abs (t - 3)
    linarith only [ht, h]
  · have h := le_abs_self (t - 3)
    linarith only [ht, h]

theorem hasCompactSupport_carlemanLogCutoff : HasCompactSupport carlemanLogCutoff := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (1 : ℝ)) (b := 5))
  intro t ht
  by_contra hmem
  have hout : t ≤ 1 ∨ 5 ≤ t := by
    simp only [mem_Icc, not_and_or, not_le] at hmem
    exact hmem.imp le_of_lt le_of_lt
  exact ht (carlemanLogCutoff_eq_zero hout)

/-- Every positive power of the cutoff is integrable. -/
theorem integrable_carlemanLogCutoff_rpow {p : ℝ} (hp : 0 < p) :
    Integrable (fun t : ℝ => |carlemanLogCutoff t| ^ p) := by
  have hc : Continuous (fun t : ℝ => |carlemanLogCutoff t| ^ p) :=
    (Real.continuous_rpow_const hp.le).comp contDiff_carlemanLogCutoff.continuous.abs
  have hs : HasCompactSupport (fun t : ℝ => |carlemanLogCutoff t| ^ p) :=
    hasCompactSupport_carlemanLogCutoff.comp_left (g := fun u : ℝ => |u| ^ p)
      (by simp only [abs_zero, Real.zero_rpow hp.ne'])
  exact hc.integrable_of_hasCompactSupport hs

/-- The cutoff's positive-power mass is strictly positive. -/
theorem integral_carlemanLogCutoff_rpow_pos {p : ℝ} (hp : 0 < p) :
    0 < ∫ t : ℝ, |carlemanLogCutoff t| ^ p := by
  have hc : Continuous (fun t : ℝ => |carlemanLogCutoff t| ^ p) :=
    (Real.continuous_rpow_const hp.le).comp contDiff_carlemanLogCutoff.continuous.abs
  have hs : HasCompactSupport (fun t : ℝ => |carlemanLogCutoff t| ^ p) :=
    hasCompactSupport_carlemanLogCutoff.comp_left (g := fun u : ℝ => |u| ^ p)
      (by simp only [abs_zero, Real.zero_rpow hp.ne'])
  apply hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hs
    (fun t => Real.rpow_nonneg (abs_nonneg _) _) (x := 3)
  rw [carlemanLogCutoff_three, abs_one, Real.one_rpow]
  exact one_ne_zero

/-- Every positive power of the cutoff derivative has finite mass. -/
theorem integrable_deriv_carlemanLogCutoff_rpow {p : ℝ} (hp : 0 < p) :
    Integrable (fun t : ℝ => |deriv carlemanLogCutoff t| ^ p) := by
  have hc : Continuous (fun t : ℝ => |deriv carlemanLogCutoff t| ^ p) :=
    (Real.continuous_rpow_const hp.le).comp
      (contDiff_carlemanLogCutoff.continuous_deriv (by simp)).abs
  have hs : HasCompactSupport (fun t : ℝ => |deriv carlemanLogCutoff t| ^ p) :=
    hasCompactSupport_carlemanLogCutoff.deriv.comp_left (g := fun u : ℝ => |u| ^ p)
      (by simp only [abs_zero, Real.zero_rpow hp.ne'])
  exact hc.integrable_of_hasCompactSupport hs

/-- The derivative is nonzero somewhere, since the cutoff has a nonzero value and compact support. -/
theorem exists_deriv_carlemanLogCutoff_ne_zero : ∃ t : ℝ, deriv carlemanLogCutoff t ≠ 0 := by
  by_contra h
  push Not at h
  have hf := HasCompactSupport.integral_Ioi_deriv_eq
    (contDiff_carlemanLogCutoff.of_le (by simp)) hasCompactSupport_carlemanLogCutoff 3
  simp_rw [h, integral_zero, carlemanLogCutoff_three] at hf
  norm_num at hf

/-- The derivative's positive-power mass is strictly positive as well as finite. -/
theorem integral_deriv_carlemanLogCutoff_rpow_pos {p : ℝ} (hp : 0 < p) :
    0 < ∫ t : ℝ, |deriv carlemanLogCutoff t| ^ p := by
  obtain ⟨t, ht⟩ := exists_deriv_carlemanLogCutoff_ne_zero
  have hc : Continuous (fun t : ℝ => |deriv carlemanLogCutoff t| ^ p) :=
    (Real.continuous_rpow_const hp.le).comp
      (contDiff_carlemanLogCutoff.continuous_deriv (by simp)).abs
  have hs : HasCompactSupport (fun t : ℝ => |deriv carlemanLogCutoff t| ^ p) :=
    hasCompactSupport_carlemanLogCutoff.deriv.comp_left (g := fun u : ℝ => |u| ^ p)
      (by simp only [abs_zero, Real.zero_rpow hp.ne'])
  apply hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hs
    (fun t => Real.rpow_nonneg (abs_nonneg _) _) (x := t)
  exact (Real.rpow_pos_of_pos (abs_pos.mpr ht) p).ne'

end GaloisForLFunctions.HTGeometry

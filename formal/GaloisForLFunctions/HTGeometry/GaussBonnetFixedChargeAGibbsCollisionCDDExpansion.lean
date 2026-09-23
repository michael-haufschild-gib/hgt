import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionCDDPhase
import GaloisForLFunctions.HTGeometry.HausdorffKernelSeries

/-!
# Collision moments as coefficients of a convergent CDD expansion

A real parameter covers the full common interior convergence interval.
For every such parameter, the odd-spin phase expansion has the actual
positive-time collision values as its coefficients. No convergence premise
is left in the public theorem.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A parameterization of the whole common interior convergence interval for the two shells. -/
def egbFixedChargeAGibbsCollisionSeriesRapidity (t : ℝ) : ℝ :=
  Real.log (3 / 2 : ℝ) * (t / (1 + |t|))

/-- The parameterized rapidity always lies strictly inside the slow shell's convergence interval. -/
theorem egbFixedChargeAGibbsCollisionSeriesRapidity_abs_lt (t : ℝ) :
    |egbFixedChargeAGibbsCollisionSeriesRapidity t| < Real.log (3 / 2 : ℝ) := by
  have hL : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hd : 0 < 1 + |t| := by positivity
  have hq : |t| / (1 + |t|) < 1 := (div_lt_one hd).mpr (by linarith)
  rw [egbFixedChargeAGibbsCollisionSeriesRapidity, abs_mul, abs_of_pos hL,
    abs_div, abs_of_pos hd]
  nlinarith

/-- Every rapidity in the full common open interval has a real parameter. -/
theorem egbFixedChargeAGibbsCollisionSeriesRapidity_range :
    Set.range egbFixedChargeAGibbsCollisionSeriesRapidity =
      Set.Ioo (-Real.log (3 / 2 : ℝ)) (Real.log (3 / 2 : ℝ)) := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact abs_lt.mp (egbFixedChargeAGibbsCollisionSeriesRapidity_abs_lt t)
  · intro hy
    have hL : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
    have hy' : |y| < Real.log (3 / 2 : ℝ) := abs_lt.mpr hy
    have hd : 0 < Real.log (3 / 2 : ℝ) - |y| := by linarith
    refine ⟨y / (Real.log (3 / 2 : ℝ) - |y|), ?_⟩
    rw [egbFixedChargeAGibbsCollisionSeriesRapidity, abs_div, abs_of_pos hd]
    have he : 1 + |y| / (Real.log (3 / 2 : ℝ) - |y|) =
        Real.log (3 / 2 : ℝ) / (Real.log (3 / 2 : ℝ) - |y|) := by
      field_simp [hd.ne']
      <;> ring
    rw [he]
    field_simp [hL.ne', hd.ne']
    <;> ring

/-- Both shell convergence conditions hold for every real rapidity parameter. -/
theorem egbFixedChargeAGibbsCollisionSeriesRapidity_kernel_conditions (t : ℝ) :
    Real.sqrt (4 / 9 : ℝ) * Real.exp |egbFixedChargeAGibbsCollisionSeriesRapidity t| < 1 ∧
      Real.sqrt (1 / 36 : ℝ) * Real.exp |egbFixedChargeAGibbsCollisionSeriesRapidity t| < 1 := by
  have he := Real.exp_lt_exp.mpr (egbFixedChargeAGibbsCollisionSeriesRapidity_abs_lt t)
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)] at he
  have hr : Real.sqrt (4 / 9 : ℝ) = 2 / 3 := by
    rw [show (4 / 9 : ℝ) = (2 / 3 : ℝ) ^ (2 : ℕ) by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  have hs : Real.sqrt (1 / 36 : ℝ) = 1 / 6 := by
    rw [show (1 / 36 : ℝ) = (1 / 6 : ℝ) ^ (2 : ℕ) by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 6)]
  rw [hr, hs]
  constructor <;> nlinarith

/-- The convergent odd-spin phase expansion has the actual collision history as its coefficient sequence. -/
theorem egbFixedChargeAGibbsCollisionCDDPhase_hasSum (n o : ℕ) (β t : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    HasSum (fun m : ℕ =>
      8 * ((-1 : ℝ) ^ m * egbFixedChargeAGibbsCollisionExcess n (m + o + 1) β E *
        Real.sinh (((2 * m + 1 : ℕ) : ℝ) * egbFixedChargeAGibbsCollisionSeriesRapidity t) /
        ((2 * m + 1 : ℕ) : ℝ)))
      (egbFixedChargeAGibbsCollisionCDDPhase n o β E (egbFixedChargeAGibbsCollisionSeriesRapidity t)) := by
  have hc := egbFixedChargeAGibbsCollisionSeriesRapidity_kernel_conditions t
  have hr := hasSum_cddPhaseKernel (by norm_num : (0 : ℝ) ≤ 4 / 9) hc.1
  have hs := hasSum_cddPhaseKernel (by norm_num : (0 : ℝ) ≤ 1 / 36) hc.2
  have h := (hr.mul_left ((4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E)).add
    (hs.mul_left ((1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E))
  have hf : (fun m : ℕ =>
      ((4 / 9 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) *
        (8 * ((-1 : ℝ) ^ m * (4 / 9 : ℝ) ^ m *
          Real.sinh (((2 * m + 1 : ℕ) : ℝ) * egbFixedChargeAGibbsCollisionSeriesRapidity t) /
          ((2 * m + 1 : ℕ) : ℝ))) +
      ((1 / 36 : ℝ) ^ (o + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) *
        (8 * ((-1 : ℝ) ^ m * (1 / 36 : ℝ) ^ m *
          Real.sinh (((2 * m + 1 : ℕ) : ℝ) * egbFixedChargeAGibbsCollisionSeriesRapidity t) /
          ((2 * m + 1 : ℕ) : ℝ)))) =
      (fun m : ℕ =>
        8 * ((-1 : ℝ) ^ m * egbFixedChargeAGibbsCollisionExcess n (m + o + 1) β E *
          Real.sinh (((2 * m + 1 : ℕ) : ℝ) * egbFixedChargeAGibbsCollisionSeriesRapidity t) /
          ((2 * m + 1 : ℕ) : ℝ))) := by
    funext m
    rw [egbFixedChargeAGibbsCollisionExcess_two_rate n (m + o) β E]
    have he : m + o + 1 = (o + 1) + m := by omega
    rw [he, pow_add (4 / 9 : ℝ) (o + 1) m, pow_add (1 / 36 : ℝ) (o + 1) m]
    ring
  have hv := (egbFixedChargeAGibbsCollisionCDDPhase_formula n o β
    (egbFixedChargeAGibbsCollisionSeriesRapidity t) E).symm
  rw [hf, hv] at h
  exact h

end
end GaloisForLFunctions.HTGeometry

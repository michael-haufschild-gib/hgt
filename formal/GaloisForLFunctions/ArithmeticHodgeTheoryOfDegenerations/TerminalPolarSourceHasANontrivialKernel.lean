import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalPolarSourceIsNonzero
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePoleCorrectorRetainsItsSignedWindowBenefit

/-!
# A nonzero terminal window with zero polar source

Two disjoint translates of the terminal spline give an explicit kernel
element. Linearity of the discrete pairing and uniqueness of its limit
prove source cancellation without an additional integral interchange.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis

/-- A disjoint translate of the terminal witness in linear coordinates. -/
def shiftedTerminalPolarWitnessLinear (x : ℝ) : ℝ :=
  terminalPolarWitnessLinear (x + 1 / 128)

def shiftedTerminalPolarWitness (y : ℝ) : ℝ :=
  shiftedTerminalPolarWitnessLinear (Real.exp y)

theorem contDiff_shiftedTerminalPolarWitness : ContDiff ℝ 2 shiftedTerminalPolarWitness :=
  (contDiff_terminalPolarWitnessLinear.comp (contDiff_id.add contDiff_const)).comp
    Real.contDiff_exp

theorem shiftedTerminalPolarWitnessLinear_eq_zero_below (x : ℝ) (hx : x ≤ 251 / 256) :
    shiftedTerminalPolarWitnessLinear x = 0 :=
  terminalPolarWitnessLinear_eq_zero_below _ (by linarith only [hx])

theorem shiftedTerminalPolarWitnessLinear_eq_zero_above (x : ℝ) (hx : 511 / 512 ≤ x) :
    shiftedTerminalPolarWitnessLinear x = 0 :=
  terminalPolarWitnessLinear_eq_zero_above _ (by linarith only [hx])

theorem shiftedTerminalPolarWitness_window_support (y : ℝ)
    (hy : y ∉ Set.Icc (-Real.log 2) 0) : shiftedTerminalPolarWitness y = 0 := by
  have hy' : y < -Real.log 2 ∨ 0 < y := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hy
  rcases hy' with hy | hy
  · have he := Real.exp_lt_exp.mpr hy
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
    exact shiftedTerminalPolarWitnessLinear_eq_zero_below _ (by linarith only [he])
  · have he : 1 < Real.exp y := by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hy
    exact shiftedTerminalPolarWitnessLinear_eq_zero_above _ (by linarith only [he])

theorem logProfile_shiftedTerminalPolarWitness (x : ℝ) :
    logProfile shiftedTerminalPolarWitness x = shiftedTerminalPolarWitnessLinear x := by
  unfold logProfile
  split_ifs with hx
  · simp only [shiftedTerminalPolarWitness, Real.exp_log hx]
  · exact (shiftedTerminalPolarWitnessLinear_eq_zero_below x
      (by linarith only [le_of_not_gt hx])).symm

/-- The source-cancelled combination of the two disjoint terminal splines. -/
def terminalZeroSourceWitness (y : ℝ) : ℝ :=
  interiorTerminalPolarSource shiftedTerminalPolarWitness * terminalPolarWitness y -
    terminalPolarWitnessSource * shiftedTerminalPolarWitness y

theorem contDiff_terminalZeroSourceWitness : ContDiff ℝ 2 terminalZeroSourceWitness :=
  (contDiff_const.mul contDiff_terminalPolarWitness).sub
    (contDiff_const.mul contDiff_shiftedTerminalPolarWitness)

theorem terminalZeroSourceWitness_window_support (y : ℝ)
    (hy : y ∉ Set.Icc (-Real.log 2) 0) : terminalZeroSourceWitness y = 0 := by
  simp only [terminalZeroSourceWitness, terminalPolarWitness_window_support y hy,
    shiftedTerminalPolarWitness_window_support y hy, mul_zero, sub_zero]

theorem logProfile_terminalZeroSourceWitness (x : ℝ) :
    logProfile terminalZeroSourceWitness x =
      interiorTerminalPolarSource shiftedTerminalPolarWitness * terminalPolarWitnessLinear x -
        terminalPolarWitnessSource * shiftedTerminalPolarWitnessLinear x := by
  have he : logProfile terminalZeroSourceWitness x =
      interiorTerminalPolarSource shiftedTerminalPolarWitness * logProfile terminalPolarWitness x -
        terminalPolarWitnessSource * logProfile shiftedTerminalPolarWitness x := by
    unfold logProfile
    split_ifs
    · rfl
    · ring
  rw [he, logProfile_terminalPolarWitness, logProfile_shiftedTerminalPolarWitness]

theorem terminalZeroSourceWitness_eq_zero_below (x : ℝ) (hx : x ≤ 251 / 256) :
    logProfile terminalZeroSourceWitness x = 0 := by
  rw [logProfile_terminalZeroSourceWitness,
    terminalPolarWitnessLinear_eq_zero_below x (by linarith only [hx]),
    shiftedTerminalPolarWitnessLinear_eq_zero_below x hx]
  ring

theorem terminalZeroSourceWitness_eq_zero_above (x : ℝ) (hx : 511 / 512 ≤ x) :
    logProfile terminalZeroSourceWitness x = 0 := by
  rw [logProfile_terminalZeroSourceWitness,
    terminalPolarWitnessLinear_eq_zero_above x hx,
    shiftedTerminalPolarWitnessLinear_eq_zero_above x hx]
  ring

/-- The disjoint second spline prevents cancellation of the function itself. -/
theorem terminalZeroSourceWitness_nonzero : ∃ y, terminalZeroSourceWitness y ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, terminalPolarWitnessLinear x ≠ 0 := by
    by_contra hn
    push Not at hn
    have hh := integral_terminalPolarWitnessLinear_pos
    simp only [hn, intervalIntegral.integral_zero, lt_self_iff_false] at hh
  have hxrange := terminalPolarWitnessLinear_support hx
  have hx0 : 0 < x - 1 / 128 := by linarith only [hxrange.1]
  have hleft : terminalPolarWitnessLinear (x - 1 / 128) = 0 :=
    terminalPolarWitnessLinear_eq_zero_below _ (by linarith only [hxrange.2])
  refine ⟨Real.log (x - 1 / 128), ?_⟩
  simp only [terminalZeroSourceWitness, terminalPolarWitness, shiftedTerminalPolarWitness,
    shiftedTerminalPolarWitnessLinear, Real.exp_log hx0, hleft, mul_zero, zero_sub,
    sub_add_cancel]
  exact neg_ne_zero.mpr (mul_ne_zero terminalPolarWitnessSource_pos.ne' hx)

/-- The literal polar source vanishes on this nonzero compact terminal window. -/
theorem terminalZeroSourceWitness_source_eq_zero :
    interiorTerminalPolarSource terminalZeroSourceWitness = 0 := by
  let c := canonicalCriticalCurve 1
  have hc : ∀ N, 1 ≤ c N := one_le_canonicalCriticalCurve 1
  have hcrit := tendsto_canonicalCriticalCurve_pow_eight (by norm_num : (0 : ℝ) < 1)
  let T := fun (h : ℝ → ℝ) (N : ℕ) => Real.sqrt (Real.log N) / c N *
    ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (normalizedRamanujanHorizonVector 1 N), horizonProfileVector (horizonWeights h N) N⟫
  have hA : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h₀ : Tendsto (T terminalPolarWitness) atTop (𝓝 terminalPolarWitnessSource) :=
    tendsto_complete_terminalPolarWitness hc (by norm_num) hcrit
  have h₁ : Tendsto (T shiftedTerminalPolarWitness) atTop
      (𝓝 (interiorTerminalPolarSource shiftedTerminalPolarWitness)) := by
    apply tendsto_complete_terminal_pole_above_half contDiff_tiltedUnitSpline
      tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos contDiff_shiftedTerminalPolarWitness
      hA shiftedTerminalPolarWitness_window_support
      (by norm_num : (1 / 2 : ℝ) < 251 / 256) (by norm_num : (511 / 512 : ℝ) < 1)
      _ _ hc (by norm_num) hcrit
    · intro x hx
      rw [logProfile_shiftedTerminalPolarWitness]
      exact shiftedTerminalPolarWitnessLinear_eq_zero_below x hx
    · intro x hx
      rw [logProfile_shiftedTerminalPolarWitness]
      exact shiftedTerminalPolarWitnessLinear_eq_zero_above x hx
  have hH : Tendsto (T terminalZeroSourceWitness) atTop
      (𝓝 (interiorTerminalPolarSource terminalZeroSourceWitness)) :=
    tendsto_complete_terminal_pole_above_half contDiff_tiltedUnitSpline
      tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos contDiff_terminalZeroSourceWitness
      hA terminalZeroSourceWitness_window_support
      (by norm_num : (1 / 2 : ℝ) < 251 / 256) (by norm_num : (511 / 512 : ℝ) < 1)
      terminalZeroSourceWitness_eq_zero_below terminalZeroSourceWitness_eq_zero_above
      hc (by norm_num) hcrit
  have hlin (N : ℕ) : T terminalZeroSourceWitness N =
      interiorTerminalPolarSource shiftedTerminalPolarWitness * T terminalPolarWitness N -
        terminalPolarWitnessSource * T shiftedTerminalPolarWitness N := by
    have hv : horizonProfileVector (horizonWeights terminalZeroSourceWitness N) N =
        interiorTerminalPolarSource shiftedTerminalPolarWitness •
          horizonProfileVector (horizonWeights terminalPolarWitness N) N -
        terminalPolarWitnessSource •
          horizonProfileVector (horizonWeights shiftedTerminalPolarWitness N) N := by
      ext n
      change terminalZeroSourceWitness (Real.log (n : ℕ) - Real.log N) / Real.sqrt (n : ℕ) =
        interiorTerminalPolarSource shiftedTerminalPolarWitness *
          (terminalPolarWitness (Real.log (n : ℕ) - Real.log N) / Real.sqrt (n : ℕ)) -
        terminalPolarWitnessSource *
          (shiftedTerminalPolarWitness (Real.log (n : ℕ) - Real.log N) / Real.sqrt (n : ℕ))
      unfold terminalZeroSourceWitness
      ring
    dsimp only [T]
    rw [hv, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
    ring
  have hz := (h₀.const_mul (interiorTerminalPolarSource shiftedTerminalPolarWitness)).sub
    (h₁.const_mul terminalPolarWitnessSource)
  rw [show interiorTerminalPolarSource shiftedTerminalPolarWitness * terminalPolarWitnessSource -
    terminalPolarWitnessSource * interiorTerminalPolarSource shiftedTerminalPolarWitness = 0 by ring]
    at hz
  exact tendsto_nhds_unique hH (hz.congr fun N => (hlin N).symm)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.terminalZeroSourceWitness_nonzero
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.terminalZeroSourceWitness_source_eq_zero

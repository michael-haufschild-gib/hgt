import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalPolarSourceAboveHalf
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheHodgeIndexAtGrowingOverlap
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A nonzero terminal polar source

A translated and contracted tilted spline lies close enough to the
horizon that the polar boundary logarithm exceeds the constant Gamma
term. Its literal complete-matrix mixed limit is strictly positive at
every fixed positive critical ratio.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory

/-- A nonnegative spline supported in `[127/128,255/256]`. -/
def terminalPolarWitnessLinear (x : ℝ) : ℝ := tiltedUnitSpline (256 * x - 254)

/-- The same terminal witness in logarithmic coordinates. -/
def terminalPolarWitness (y : ℝ) : ℝ := terminalPolarWitnessLinear (Real.exp y)

theorem contDiff_terminalPolarWitnessLinear : ContDiff ℝ 2 terminalPolarWitnessLinear :=
  contDiff_tiltedUnitSpline.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem contDiff_terminalPolarWitness : ContDiff ℝ 2 terminalPolarWitness :=
  contDiff_terminalPolarWitnessLinear.comp Real.contDiff_exp

theorem terminalPolarWitnessLinear_nonneg (x : ℝ) : 0 ≤ terminalPolarWitnessLinear x :=
  RenormalizedIntersectionTheory.tiltedUnitSpline_nonneg _

theorem terminalPolarWitnessLinear_support {x : ℝ} (hx : terminalPolarWitnessLinear x ≠ 0) :
    x ∈ Set.Icc (127 / 128 : ℝ) (255 / 256) := by
  have ht : 256 * x - 254 ∈ Set.Icc (0 : ℝ) 1 := by
    by_contra hn
    exact hx (tiltedUnitSpline_eq_zero _ hn)
  exact ⟨by linarith only [ht.1], by linarith only [ht.2]⟩

theorem terminalPolarWitnessLinear_eq_zero_below (x : ℝ) (hx : x ≤ 253 / 256) :
    terminalPolarWitnessLinear x = 0 := by
  by_contra hn
  have h := (terminalPolarWitnessLinear_support hn).1
  linarith only [hx, h]

theorem terminalPolarWitnessLinear_eq_zero_above (x : ℝ) (hx : 511 / 512 ≤ x) :
    terminalPolarWitnessLinear x = 0 := by
  by_contra hn
  have h := (terminalPolarWitnessLinear_support hn).2
  linarith only [hx, h]

theorem hasCompactSupport_terminalPolarWitnessLinear : HasCompactSupport terminalPolarWitnessLinear := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (127 / 128 : ℝ) (255 / 256)))
  intro x hx
  by_contra hn
  exact hx (terminalPolarWitnessLinear_support hn)

/-- The logarithmic witness is a fixed compact window. -/
theorem terminalPolarWitness_window_support (y : ℝ)
    (hy : y ∉ Set.Icc (-Real.log 2) 0) : terminalPolarWitness y = 0 := by
  have hy' : y < -Real.log 2 ∨ 0 < y := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hy
  rcases hy' with hy | hy
  · have he := Real.exp_lt_exp.mpr hy
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
    exact terminalPolarWitnessLinear_eq_zero_below _ (by linarith only [he])
  · have he : 1 < Real.exp y := by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hy
    exact terminalPolarWitnessLinear_eq_zero_above _ (by linarith only [he])

theorem logProfile_terminalPolarWitness (x : ℝ) :
    logProfile terminalPolarWitness x = terminalPolarWitnessLinear x := by
  unfold logProfile
  split_ifs with hx
  · simp only [terminalPolarWitness, Real.exp_log hx]
  · exact (terminalPolarWitnessLinear_eq_zero_below x (by linarith only [le_of_not_gt hx])).symm

theorem integral_terminalPolarWitnessLinear_pos :
    0 < ∫ x in (0 : ℝ)..1, terminalPolarWitnessLinear x := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, tiltedUnitSpline u ≠ 0 := by
    by_contra hn
    push Not at hn
    have hi := RenormalizedIntersectionTheory.integral_tiltedUnitSpline_pos
    change 0 < ∫ u, tiltedUnitSpline u at hi
    simp only [hn, integral_zero, lt_self_iff_false] at hi
  have hx : terminalPolarWitnessLinear ((u + 254) / 256) ≠ 0 := by
    have he : 256 * ((u + 254) / 256) - 254 = u := by ring
    simpa only [terminalPolarWitnessLinear, he] using hu
  have hi : 0 < ∫ x, terminalPolarWitnessLinear x :=
    contDiff_terminalPolarWitnessLinear.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      hasCompactSupport_terminalPolarWitnessLinear terminalPolarWitnessLinear_nonneg hx
  rw [intervalIntegral.integral_of_le zero_le_one,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hi
  · intro x hx
    by_contra hn
    have hs := terminalPolarWitnessLinear_support hn
    exact hx ⟨by linarith only [hs.1], by linarith only [hs.2]⟩

/-- On the support of the witness the boundary logarithm pays `log(2π)` with room to spare. -/
theorem terminalPolarWitnessLinear_le_source (x : ℝ) :
    terminalPolarWitnessLinear x ≤ polarCenterProfile terminalPolarWitnessLinear x -
      Real.log (2 * Real.pi) * terminalPolarWitnessLinear x := by
  by_cases hz : terminalPolarWitnessLinear x = 0
  · simp only [polarCenterProfile, hz, zero_div, zero_mul, mul_zero, sub_zero, le_refl]
  have hx := terminalPolarWitnessLinear_support hz
  have hx0 : 0 < x := by linarith only [hx.1]
  have hx1 : x < 1 := by linarith only [hx.2]
  have hb0 : 0 < 1 - x ^ 2 := by
    have hp := mul_pos (sub_pos.mpr hx1) (by linarith only [hx0] : 0 < 1 + x)
    nlinarith only [hp]
  have hxsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 127 / 128) hx.1 2
  have hb : 1 - x ^ 2 ≤ (255 / 16384 : ℝ) := by nlinarith only [hxsq]
  have hπ0 : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  have hπ : (2 * Real.pi) ^ 2 ≤ (64 : ℝ) := by
    have hp := mul_pos (sub_pos.mpr Real.pi_lt_four) (by positivity : 0 < 4 + Real.pi)
    nlinarith only [hp]
  have hq0 : 0 < (2 * Real.pi) ^ 2 * (1 - x ^ 2) := mul_pos (pow_pos hπ0 2) hb0
  have hq1 : (2 * Real.pi) ^ 2 * (1 - x ^ 2) < 1 := by
    have h := mul_le_mul hπ hb hb0.le (by norm_num : (0 : ℝ) ≤ 64)
    exact h.trans_lt (by norm_num)
  have hlog := Real.log_neg hq0 hq1
  rw [Real.log_mul (pow_ne_zero 2 hπ0.ne') hb0.ne', Real.log_pow] at hlog
  have hlog' : Real.log (2 * Real.pi) + Real.log (1 - x ^ 2) / 2 < 0 := by
    norm_num only [Nat.cast_ofNat] at hlog
    linarith only [hlog]
  have hF0 := terminalPolarWitnessLinear_nonneg x
  have hdiv : terminalPolarWitnessLinear x ≤ terminalPolarWitnessLinear x / x := by
    apply (le_div_iff₀ hx0).mpr
    exact (mul_le_mul_of_nonneg_left hx1.le hF0).trans_eq (mul_one _)
  have hn := mul_nonpos_of_nonneg_of_nonpos hF0 hlog'.le
  unfold polarCenterProfile
  nlinarith only [hdiv, hn]

theorem terminalPolarWitness_source_integral_pos :
    0 < (∫ x in (0 : ℝ)..1, polarCenterProfile (logProfile terminalPolarWitness) x) -
      Real.log (2 * Real.pi) * ∫ x in (0 : ℝ)..1, logProfile terminalPolarWitness x := by
  rw [show logProfile terminalPolarWitness = terminalPolarWitnessLinear from
    funext logProfile_terminalPolarWitness]
  obtain ⟨LF, hLF⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    hasCompactSupport_terminalPolarWitnessLinear contDiff_terminalPolarWitnessLinear (by norm_num)
  have hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |terminalPolarWitnessLinear x - terminalPolarWitnessLinear y| ≤ (LF : ℝ) * |x - y| := by
    intro x _ y _
    simpa only [Real.dist_eq] using hLF.dist_le_mul x y
  have hcont := continuousOn_polarCenterProfile (by positivity : 0 ≤ (LF : ℝ)) hFL
    (terminalPolarWitnessLinear_eq_zero_above 1 (by norm_num))
    (by norm_num : (0 : ℝ) < 253 / 256)
    (fun x _ hx => terminalPolarWitnessLinear_eq_zero_below x hx)
  have hP : IntervalIntegrable (polarCenterProfile terminalPolarWitnessLinear) volume 0 1 :=
    (show ContinuousOn (polarCenterProfile terminalPolarWitnessLinear) (Set.uIcc 0 1) by
      simpa only [Set.uIcc_of_le zero_le_one] using hcont).intervalIntegrable
  have hF : IntervalIntegrable terminalPolarWitnessLinear volume (0 : ℝ) 1 :=
    contDiff_terminalPolarWitnessLinear.continuous.intervalIntegrable (0 : ℝ) 1
  have hC := hF.const_mul (Real.log (2 * Real.pi))
  have hi := intervalIntegral.integral_mono_on zero_le_one hF (hP.sub hC)
    (fun x _ => terminalPolarWitnessLinear_le_source x)
  rw [intervalIntegral.integral_sub hP hC, intervalIntegral.integral_const_mul] at hi
  exact integral_terminalPolarWitnessLinear_pos.trans_le hi

/-- The positive source coefficient of the fixed terminal witness. -/
def terminalPolarWitnessSource : ℝ :=
  ((∫ u, tiltedUnitSpline u) ^ 2 / ∫ u, tiltedUnitSpline u ^ 2) *
    ((∫ x in (0 : ℝ)..1, polarCenterProfile (logProfile terminalPolarWitness) x) -
      Real.log (2 * Real.pi) * ∫ x in (0 : ℝ)..1, logProfile terminalPolarWitness x)

theorem terminalPolarWitnessSource_pos : 0 < terminalPolarWitnessSource := by
  apply mul_pos _ terminalPolarWitness_source_integral_pos
  exact div_pos (pow_pos RenormalizedIntersectionTheory.integral_tiltedUnitSpline_pos 2)
    integral_tiltedUnitSpline_sq_pos

/-- A single compact terminal window receives the same strictly positive source at every
positive critical ratio. -/
theorem tendsto_complete_terminalPolarWitness
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log N) / c N *
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
          (normalizedRamanujanHorizonVector 1 N),
        horizonProfileVector (horizonWeights terminalPolarWitness N) N⟫)
      atTop (𝓝 terminalPolarWitnessSource) := by
  apply tendsto_complete_terminal_pole_above_half contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos contDiff_terminalPolarWitness
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) terminalPolarWitness_window_support
    (by norm_num : (1 / 2 : ℝ) < 253 / 256) (by norm_num : (511 / 512 : ℝ) < 1)
    _ _ hc hR hcrit
  · intro x hx
    rw [logProfile_terminalPolarWitness]
    exact terminalPolarWitnessLinear_eq_zero_below x hx
  · intro x hx
    rw [logProfile_terminalPolarWitness]
    exact terminalPolarWitnessLinear_eq_zero_above x hx

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.terminalPolarWitnessSource_pos
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_complete_terminalPolarWitness

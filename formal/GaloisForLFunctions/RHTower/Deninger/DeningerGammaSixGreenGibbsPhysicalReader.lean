import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixSingularGreenStokesCoface
import GaloisForLFunctions.RHTower.Deninger.DeningerOrdinaryIntegerBVGreenStokesRadialComparison

namespace RHTower

noncomputable section

/-- Positive-temperature diagonal density of the shell Green operator. -/
def deningerGammaSixGibbsWeight (delta : ℝ) (n : ℕ) : ℝ :=
  deningerGammaSixShellEigenvalue n ^ (1 + delta)

theorem summable_deningerGammaSixGibbsWeight
    {delta : ℝ} (hdelta : 0 < delta) :
    Summable (deningerGammaSixGibbsWeight delta) := by
  let p : DeningerGammaSixPositiveExponent := ⟨1 + delta, by linarith⟩
  have hp : 1 < (p : ℝ) := by dsimp [p]; linarith
  have hsum := summable_deningerGammaSixShellPowerWeight_of_one_lt p hp
  exact hsum.congr fun n => by
    simp [deningerGammaSixGibbsWeight,
      deningerGammaSixShellPowerWeight, p]

/-- Actual shell partition trace `Tr(G₆^(1+delta))`. -/
def deningerGammaSixGibbsPartition (delta : ℝ) : ℝ :=
  ∑' n : ℕ, deningerGammaSixGibbsWeight delta n

theorem deningerGammaSixGibbsPartition_pos
    {delta : ℝ} (hdelta : 0 < delta) :
    0 < deningerGammaSixGibbsPartition delta := by
  exact (summable_deningerGammaSixGibbsWeight hdelta).tsum_pos
    (fun n => Real.rpow_nonneg (deningerGammaSixShellEigenvalue_nonneg n) _)
    0 (Real.rpow_pos_of_pos (by
      unfold deningerGammaSixShellEigenvalue
      positivity) _)

/-- Trace of the range projection `S₆ S₆*` against the Gibbs density,
computed on its canonical Wold orthonormal basis. -/
def deningerGammaSixWoldRangeGibbsTrace (delta : ℝ) : ℝ :=
  ∑' n : ℕ,
    deningerGammaSixGibbsWeight delta
      (deningerGammaSixWoldCoordinate n)

theorem deningerGammaSixWoldRangeGibbsTrace_eq
    (delta : ℝ) :
    deningerGammaSixWoldRangeGibbsTrace delta =
      (1 / 6 : ℝ) ^ (1 + delta) *
        deningerGammaSixGibbsPartition delta := by
  rw [deningerGammaSixWoldRangeGibbsTrace,
    deningerGammaSixGibbsPartition, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [deningerGammaSixGibbsWeight,
    deningerGammaSixGibbsWeight,
    deningerGammaSixShellEigenvalue_wold,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 6)
      (deningerGammaSixShellEigenvalue_nonneg n)]

/-- Actual Gibbs trace of the bounded shell Stokes cocycle
`C₆ = (1/6)I - S₆S₆*`. -/
def deningerGammaSixStokesGibbsTrace (delta : ℝ) : ℝ :=
  (1 / 6 : ℝ) * deningerGammaSixGibbsPartition delta -
    deningerGammaSixWoldRangeGibbsTrace delta

/-- Normalized Green Gibbs reader on the shell Stokes cocycle. -/
def deningerGammaSixNormalizedGreenGibbsReader (delta : ℝ) : ℝ :=
  deningerGammaSixStokesGibbsTrace delta /
    deningerGammaSixGibbsPartition delta

/-- Meromorphic/real-analytic continuation of the normalized Gibbs reader. -/
def deningerGammaSixGreenGibbsContinuation (delta : ℝ) : ℝ :=
  (1 / 6 : ℝ) * (1 - (1 / 6 : ℝ) ^ delta)

/-- **Exact source Gibbs formula.**  At every positive temperature, the
literal normalized operator trace equals the closed boundary coefficient. -/
theorem deningerGammaSixNormalizedGreenGibbsReader_eq
    {delta : ℝ} (hdelta : 0 < delta) :
    deningerGammaSixNormalizedGreenGibbsReader delta =
      deningerGammaSixGreenGibbsContinuation delta := by
  have hZ : deningerGammaSixGibbsPartition delta ≠ 0 :=
    (deningerGammaSixGibbsPartition_pos hdelta).ne'
  rw [deningerGammaSixNormalizedGreenGibbsReader,
    deningerGammaSixStokesGibbsTrace,
    deningerGammaSixWoldRangeGibbsTrace_eq delta,
    deningerGammaSixGreenGibbsContinuation,
    Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 6) 1 delta,
    Real.rpow_one]
  field_simp [hZ]

theorem deningerGammaSixGreenGibbsContinuation_eq_physicalBV
    (s : ℂ) :
    deningerGammaSixGreenGibbsContinuation (2 * s.re - 1) =
      deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6 s := by
  rw [deningerGammaSixGreenGibbsContinuation,
    deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation,
    deningerHalfDensityMateGain]
  have hlog : Real.log (1 / 6 : ℝ) = -Real.log 6 := by
    rw [show (1 / 6 : ℝ) = (6 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 6), hlog]
  norm_num
  rw [← Real.exp_neg]
  congr 1
  ring

theorem deningerGammaSixGreenGibbs_reflectedDifference
    (s : ℂ) :
    (6 : ℝ) *
        (deningerGammaSixGreenGibbsContinuation (2 * s.re - 1) -
          deningerGammaSixGreenGibbsContinuation (-(2 * s.re - 1))) =
      deningerTensorSquareRadialMateCurvature 6 s := by
  rw [deningerGammaSixGreenGibbsContinuation_eq_physicalBV]
  have hreflect : -(2 * s.re - 1) =
      2 * (1 - star s).re - 1 := by simp; ring
  rw [hreflect,
    deningerGammaSixGreenGibbsContinuation_eq_physicalBV]
  simpa using
    deningerOrdinaryIntegerBVGreenStokes_reflectedDifference
      (n := 6) (by norm_num) s

end

end RHTower

import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Fourier.CoprimePlateau
import GaloisForLFunctions.HTGeometry.NearDiagonalParity

/-!
# A nonvanishing parity correction

The substitution `2n = m + r` retains only the parity class of `m`.
At phase one sixth, unrestricted harmonic sine sums tend to `π/3`, whereas
the odd terms tend to `π/4`. Their difference is `π/12`, so discarding the
parity condition changes the limiting term rather than only the truncation error.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open Finset Filter Topology
open BezoutValuationIncidence

noncomputable section

/-- The unrestricted Fourier value at one sixth of a turn. -/
theorem tendsto_harmonicSine_one_sixth :
    Tendsto (fun N => harmonicSine N (1 / 6)) atTop (𝓝 (Real.pi / 3)) := by
  have h := tendsto_harmonicSine (1 / 6)
  have hv : sawtooth (1 / 6) = -(1 / 3 : ℝ) := by
    rw [sawtooth, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
    norm_num
  rw [hv] at h
  convert h using 1 <;> congr 1 <;> ring

/-- Odd terms have the square-wave value at the same phase. -/
theorem tendsto_coprimeHarmonicSine_two_one_sixth :
    Tendsto (fun N => coprimeHarmonicSine 2 N (1 / 6)) atTop (𝓝 (Real.pi / 4)) := by
  have h := tendsto_coprimeHarmonicSine_plateau 0
    (by norm_num : (0 : ℝ) < 1 / 6) (by norm_num)
  norm_num [Nat.totient_prime Nat.prime_two] at h
  convert h using 1 <;> congr 1 <;> ring

/-- On the whole first half-period, the parity correction is an explicit affine function. -/
theorem tendsto_parity_correction_first_cell {x : ℝ} (hx : 0 < x) (hxhalf : x < 1 / 2) :
    Tendsto (fun N => harmonicSine N x - coprimeHarmonicSine 2 N x)
      atTop (𝓝 (Real.pi * (1 / 4 - x))) := by
  have hfull := tendsto_harmonicSine x
  have hv : sawtooth x = x - 1 / 2 := by
    rw [sawtooth, Int.fract_eq_self.mpr ⟨hx.le, by linarith⟩, if_neg hx.ne']
  rw [hv] at hfull
  have hodd := tendsto_coprimeHarmonicSine_plateau 0 hx (by simpa using hxhalf)
  norm_num [Nat.totient_prime Nat.prime_two] at hodd
  convert hfull.sub hodd using 1 <;> congr 1 <;> ring

/-- The even terms omitted by the parity restriction retain a nonzero limit. -/
theorem tendsto_parity_correction_one_sixth :
    Tendsto (fun N => harmonicSine N (1 / 6) - coprimeHarmonicSine 2 N (1 / 6))
      atTop (𝓝 (Real.pi / 12)) := by
  convert tendsto_harmonicSine_one_sixth.sub
    tendsto_coprimeHarmonicSine_two_one_sixth using 1 <;> congr 1 <;> ring

/-- At the rational phase `T/m = 1`, the correction is `(π - 2)/4`. -/
theorem tendsto_parity_correction_unit_phase :
    Tendsto (fun N => harmonicSine N (1 / (2 * Real.pi)) -
      coprimeHarmonicSine 2 N (1 / (2 * Real.pi))) atTop (𝓝 ((Real.pi - 2) / 4)) := by
  have hx : 1 / (2 * Real.pi) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    linarith [Real.two_le_pi]
  have h := tendsto_parity_correction_first_cell
    (by positivity : (0 : ℝ) < 1 / (2 * Real.pi)) hx
  convert h using 1
  congr 1
  field_simp [Real.pi_ne_zero]
  ring

/-- Replacing the parity-restricted series by the unrestricted series is not an `o(1)` error. -/
theorem parity_correction_not_tendsto_zero :
    ¬ Tendsto (fun N => harmonicSine N (1 / 6) - coprimeHarmonicSine 2 N (1 / 6))
      atTop (𝓝 0) := by
  intro h
  have heq := tendsto_nhds_unique tendsto_parity_correction_one_sixth h
  exact (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 12)).ne' heq

/-- Every integer offset missed by the odd lattice is inadmissible in the substitution. -/
theorem nearDiagonalSubst_odd_excludes_even {m r : ℤ} (hm : Odd m) (hr : Even r) :
    r ∉ Set.range (HTGeometry.nearDiagonalSubst m) := by
  rw [HTGeometry.range_nearDiagonalSubst_of_odd hm]
  exact Int.not_odd_iff_even.mpr hr

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis

import GaloisForLFunctions.RHTower.SawtoothFourierSeries
import GaloisForLFunctions.BezoutValuationIncidence.CotangentSawtoothFormOfThePronicGram

/-!
# The sine series at every phase

The harmonic sine series converges to the centered sawtooth, with value zero at
integer phases. Keeping this boundary value permits finite arithmetic filters
without excluding their resonances.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open Finset Filter Topology
open BezoutValuationIncidence

noncomputable section

/-- Harmonic sine partial sums at a phase measured in turns. -/
def harmonicSine (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ range N, Real.sin ((n : ℝ) * (2 * Real.pi * x)) / (n : ℝ)

/-- Integer translation leaves every partial sum unchanged. -/
theorem harmonicSine_add_int (N : ℕ) (x : ℝ) (k : ℤ) :
    harmonicSine N (x + k) = harmonicSine N x := by
  apply sum_congr rfl
  intro n _
  rw [show 2 * Real.pi * (x + k) = 2 * Real.pi * x + (k : ℝ) * (2 * Real.pi) by ring,
    RHTower.sawtoothSine_periodic]

/-- The Fourier value includes every jump: the symmetric value there is zero. -/
theorem tendsto_harmonicSine (x : ℝ) :
    Tendsto (fun N => harmonicSine N x) atTop (𝓝 (-Real.pi * sawtooth x)) := by
  have hper (N : ℕ) : harmonicSine N x = harmonicSine N (Int.fract x) := by
    conv_lhs => rw [← Int.floor_add_fract x, add_comm]
    exact harmonicSine_add_int N _ _
  by_cases hx : Int.fract x = 0
  · have hv : sawtooth x = 0 := by simp only [sawtooth, hx, if_true]
    simp only [hv, mul_zero]
    convert tendsto_const_nhds (x := (0 : ℝ)) using 1
    funext N
    rw [hper, hx, harmonicSine]
    simp
  · have hx0 : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hx)
    have hx1 := Int.fract_lt_one x
    have hangle : 2 * Real.pi * Int.fract x ∈ Set.Ioo 0 (2 * Real.pi) :=
      ⟨by positivity, by nlinarith [Real.pi_pos]⟩
    have h := RHTower.tendsto_sum_sawtoothSine hangle
    rw [RHTower.sawWave_eq_of_mem_Ioo hangle] at h
    have hv : (Real.pi - 2 * Real.pi * Int.fract x) / 2 = -Real.pi * sawtooth x := by
      rw [sawtooth, if_neg hx]
      ring
    rw [hv] at h
    exact h.congr fun N => (hper N).symm

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis

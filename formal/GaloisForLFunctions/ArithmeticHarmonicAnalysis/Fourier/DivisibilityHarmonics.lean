import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Fourier.SawtoothBoundary
import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion

/-!
# Harmonic sine sums with divisor filters

A finite divisor filter is a finite superposition of decimated sine series.
Its boundary value is therefore an explicit sum of dilated sawtooths. Möbius
inversion gives the coprimality filter, with every resonant phase retained.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open Finset Filter Topology ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open BezoutValuationIncidence

noncomputable section

/-- Positive-index partial sums agree with the zero-based convention. -/
theorem sum_Icc_harmonicSine (N : ℕ) (x : ℝ) :
    (∑ n ∈ Icc 1 N, Real.sin ((n : ℝ) * (2 * Real.pi * x)) / (n : ℝ)) =
      harmonicSine (N + 1) x := by
  rw [harmonicSine, ← sum_Ico_eq_sub _ (by omega : 0 ≤ 1) (by omega : 1 ≤ N + 1)]
  simp [Nat.Ico_succ_right]

/-- A divisor restriction decimates both the cutoff and the phase. -/
theorem sum_dvd_harmonicSine {d : ℕ} (hd : 0 < d) (N : ℕ) (x : ℝ) :
    (∑ n ∈ (Icc 1 N).filter (fun n => d ∣ n),
      Real.sin ((n : ℝ) * (2 * Real.pi * x)) / (n : ℝ)) =
      (d : ℝ)⁻¹ * harmonicSine (N / d + 1) ((d : ℝ) * x) := by
  rw [HTGeometry.multiples_Icc hd N,
    sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hd hab),
    ← sum_Icc_harmonicSine, mul_sum]
  apply sum_congr rfl
  intro j _
  push_cast
  rw [show (d : ℝ) * j * (2 * Real.pi * x) =
    (j : ℝ) * (2 * Real.pi * ((d : ℝ) * x)) by ring]
  ring

/-- A finite combination of divisibility indicators. -/
def divisorFilter (D : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ D, if d ∣ n then a d else 0

/-- Exact finite expansion; no limiting interchange over infinitely many divisors is used. -/
theorem sum_divisorFilter_harmonicSine (D : Finset ℕ) (a : ℕ → ℝ)
    (hD : ∀ d ∈ D, 0 < d) (N : ℕ) (x : ℝ) :
    (∑ n ∈ Icc 1 N, divisorFilter D a n *
      (Real.sin ((n : ℝ) * (2 * Real.pi * x)) / (n : ℝ))) =
      ∑ d ∈ D, a d / d * harmonicSine (N / d + 1) ((d : ℝ) * x) := by
  simp only [divisorFilter, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  have hterm (n : ℕ) : (if d ∣ n then a d else 0) *
      (Real.sin ((n : ℝ) * (2 * Real.pi * x)) / (n : ℝ)) =
      if d ∣ n then a d * (Real.sin ((n : ℝ) * (2 * Real.pi * x)) / (n : ℝ)) else 0 := by
    split <;> simp only [zero_mul]
  simp_rw [hterm]
  rw [← sum_filter, ← mul_sum, sum_dvd_harmonicSine (hD d hd)]
  ring

/-- Every finite divisor filter has an exact Fourier boundary value, even at resonances. -/
theorem tendsto_divisorFilter_harmonicSine (D : Finset ℕ) (a : ℕ → ℝ)
    (hD : ∀ d ∈ D, 0 < d) (x : ℝ) :
    Tendsto (fun N => ∑ n ∈ Icc 1 N, divisorFilter D a n *
      (Real.sin ((n : ℝ) * (2 * Real.pi * x)) / (n : ℝ))) atTop
      (𝓝 (-Real.pi * ∑ d ∈ D, a d / d * sawtooth ((d : ℝ) * x))) := by
  simp_rw [sum_divisorFilter_harmonicSine D a hD]
  have h : Tendsto (fun N => ∑ d ∈ D,
      a d / d * harmonicSine (N / d + 1) ((d : ℝ) * x)) atTop
      (𝓝 (∑ d ∈ D, a d / d * (-Real.pi * sawtooth ((d : ℝ) * x)))) := by
    apply tendsto_finsetSum
    intro d hd
    exact ((tendsto_harmonicSine ((d : ℝ) * x)).comp
      (tendsto_add_atTop_nat 1 |>.comp (HTGeometry.tendsto_natDiv_atTop (hD d hd)))).const_mul _
  convert h using 1
  rw [mul_sum]
  apply sum_congr rfl
  intro d _
  ring

/-- Möbius inversion realizes the coprimality indicator as a divisor filter. -/
theorem divisorFilter_moebius {q : ℕ} (hq : q ≠ 0) (n : ℕ) :
    divisorFilter q.divisors (fun d => (μ d : ℝ)) n = if n.Coprime q then 1 else 0 := by
  rw [divisorFilter, ← sum_filter, ← HTGeometry.divisors_gcd_eq_filter n hq,
    HTGeometry.sum_divisors_moebius_real]
  rfl

/-- Sine harmonics restricted to integers coprime to the modulus. -/
def coprimeHarmonicSine (q N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => n.Coprime q),
    Real.sin ((n : ℝ) * (2 * Real.pi * x)) / (n : ℝ)

/-- Coprime harmonics converge to the Möbius combination of dilated sawtooths. -/
theorem tendsto_coprimeHarmonicSine (q : ℕ) (x : ℝ) :
    Tendsto (fun N => coprimeHarmonicSine (q + 1) N x) atTop
      (𝓝 (-Real.pi * ∑ d ∈ (q + 1).divisors,
        (μ d : ℝ) / d * sawtooth ((d : ℝ) * x))) := by
  have h := tendsto_divisorFilter_harmonicSine (q + 1).divisors
    (fun d => (μ d : ℝ)) (fun _ hd => Nat.pos_of_mem_divisors hd) x
  refine h.congr fun N => ?_
  simp only [coprimeHarmonicSine, sum_filter, divisorFilter_moebius (Nat.succ_ne_zero q),
    ite_mul, one_mul, zero_mul]

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis

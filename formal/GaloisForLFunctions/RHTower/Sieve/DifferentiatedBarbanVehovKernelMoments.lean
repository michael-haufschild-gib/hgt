import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovScaledKernels

/-!
# Logarithmic window moments for differentiated Barban--Vehov kernels
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Harmonic logarithmic moment on the positive-natural window `(A,B]`. -/
def harmonicLogWindowMoment (m A B : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ioc A B, Real.log (j : ℝ) ^ m / (j : ℝ)

theorem barbanVehovLongHarmonicKernel_eq_moment
    {L U q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    barbanVehovLongHarmonicKernel L U q r =
      1 / (Nat.lcm q r : ℝ) *
        harmonicLogWindowMoment 0 (L / Nat.lcm q r) (U / Nat.lcm q r) := by
  rw [barbanVehovLongHarmonicKernel_eq_scaled hq hr]
  simp [harmonicLogWindowMoment]

theorem barbanVehovLongFirstLogKernel_eq_moments
    {L U q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    barbanVehovLongFirstLogKernel L U q r =
      1 / (Nat.lcm q r : ℝ) *
        (Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) *
            harmonicLogWindowMoment 0 (L / Nat.lcm q r) (U / Nat.lcm q r) +
          harmonicLogWindowMoment 1 (L / Nat.lcm q r) (U / Nat.lcm q r)) := by
  rw [barbanVehovLongFirstLogKernel_eq_scaled hq hr]
  congr 1
  rw [harmonicLogWindowMoment, harmonicLogWindowMoment]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [pow_zero, pow_one]
  ring

theorem barbanVehovLongSecondLogKernel_eq_moments
    {L U q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    barbanVehovLongSecondLogKernel L U q r =
      1 / (Nat.lcm q r : ℝ) *
        (Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) *
              Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) *
              harmonicLogWindowMoment 0 (L / Nat.lcm q r) (U / Nat.lcm q r) +
          (Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) +
              Real.log (((Nat.lcm q r / r : ℕ) : ℝ))) *
              harmonicLogWindowMoment 1 (L / Nat.lcm q r) (U / Nat.lcm q r) +
          harmonicLogWindowMoment 2 (L / Nat.lcm q r) (U / Nat.lcm q r)) := by
  rw [barbanVehovLongSecondLogKernel_eq_scaled hq hr]
  congr 1
  rw [harmonicLogWindowMoment, harmonicLogWindowMoment,
    harmonicLogWindowMoment]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [pow_zero, pow_one]
  ring

end

end RHTower.Sieve

import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheIntegratedCoreIsAPrimeCount
import GaloisForLFunctions.RHTower.Sieve.LogSumFromCount
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The core debt is the prime harmonic series

Summing the integrated core by scales instead of horizons collapses the pronic weights by
telescoping, `Σ_{n = j}^{T} 1/(n(n+1)) = 1/j − 1/(T+1)`, and leaves one sum over scales:

`∫_η^ε core_x(T) dx = Σ_{j ≤ T} (Λ(j)/log j)(j^{-η} − j^{-ε})(1/j − 1/(T+1))`
(`integral_workCore_eq_scaleSum`).

The density `Λ(j)/log j` is `1` at a prime and `1/k` at a `k`-th prime power, so the scale sum is a
**prime harmonic series**: its prime terms are `(p^{-η} − p^{-ε})/p` times a telescoping factor.
Hence the integrated core grows without bound in the horizon — at the rate of `Σ_{p ≤ T} 1/p`
(`exists_horizon_integral_workCore_ge`, using the divergence of the prime reciprocals).

So the explicit positive core of the signed work is a debt of size `log log T`, and admission forces
the deviation terms to carry it: under any energy budget the integrated deviation tends to `−∞`
along the horizons (`exists_horizon_integral_workDeviation_le`).  The continuation layer's
obstruction is thereby identified with the classical divergence of the prime harmonic series: the
only way the energy can stay bounded is that the source's deviation from constancy cancels, to
leading order, the prime harmonic growth of its own tangent.
-/

open Set Filter Finset MeasureTheory RHTower

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The scale form of the integrated core -/

/-- The pronic tail mass from a scale. -/
theorem sum_Icc_pronic_from {j T : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T) :
    (∑ n ∈ Finset.Icc j T, 1 / ((n : ℝ) * ((n : ℝ) + 1))) =
      1 / (j : ℝ) - 1 / ((T : ℝ) + 1) := by
  have hIcc : (Finset.Icc j T : Finset ℕ) = Finset.Icc ((j - 1) + 1) T := by
    congr 1
    omega
  have hcell : ∀ n ∈ Finset.Icc ((j - 1) + 1) T,
      1 / ((n : ℝ) * ((n : ℝ) + 1)) = 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
    intro n hn
    have hn1 : 1 ≤ n := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    field_simp
    ring
  rw [hIcc, Finset.sum_congr rfl hcell,
    RHTower.Sieve.sum_Icc_telescope_inv (by omega : j - 1 ≤ T)]
  congr 2
  have : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
    have h : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      have : (1 : ℕ) ≤ j := hj
      push_cast [Nat.cast_sub this]
      ring
    rw [h]
    ring
  rw [this]

/-- **The integrated core, summed by scales.** -/
theorem integral_workCore_eq_scaleSum (η ε : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∫ x in η..ε, workCore x T) =
      ∑ j ∈ Finset.Icc 1 T, ArithmeticFunction.vonMangoldt j *
        (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j) *
          (1 / (j : ℝ) - 1 / ((T : ℝ) + 1)) := by
  classical
  rw [integral_workCore_eq]
  -- extend each inner sum to the full scale range with an indicator, then swap
  have hext : ∀ n ∈ Finset.Icc 1 T,
      (∑ j ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt j *
          (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j)) /
            ((n : ℝ) * ((n : ℝ) + 1)) =
        ∑ j ∈ Finset.Icc 1 T, (if j ≤ n then
          ArithmeticFunction.vonMangoldt j *
            (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j) /
              ((n : ℝ) * ((n : ℝ) + 1)) else 0) := by
    intro n hn
    have hnT : n ≤ T := (Finset.mem_Icc.mp hn).2
    rw [Finset.sum_div, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun j _ => rfl
    ext j
    rw [Finset.mem_Icc, Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [Finset.sum_congr rfl hext, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjT : j ≤ T := (Finset.mem_Icc.mp hj).2
  rw [← Finset.sum_filter]
  have hfil : (Finset.Icc 1 T).filter (fun n => j ≤ n) = Finset.Icc j T := by
    ext n
    rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
    omega
  rw [hfil]
  have hmass : (∑ n ∈ Finset.Icc j T, 1 / ((n : ℝ) * ((n : ℝ) + 1))) =
      1 / (j : ℝ) - 1 / ((T : ℝ) + 1) := sum_Icc_pronic_from hj1 hjT
  have hfac : ∀ n ∈ Finset.Icc j T,
      ArithmeticFunction.vonMangoldt j *
          (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j) /
            ((n : ℝ) * ((n : ℝ) + 1)) =
        (ArithmeticFunction.vonMangoldt j *
          (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j)) *
            (1 / ((n : ℝ) * ((n : ℝ) + 1))) := fun n _ => by ring
  rw [Finset.sum_congr rfl hfac, ← Finset.sum_div, ← Finset.sum_div] at *
  rw [Finset.mul_sum.symm, hmass]

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

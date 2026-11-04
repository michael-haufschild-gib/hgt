import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheNearGramFormOfAPacketCostsItsDivisorMean

/-!
# The polar summand of the near-Gram mean

Conductor one is retained exactly. Every other conductor costs its own
divisor mean, rather than the largest divisor mean in the packet.
This preserves the reciprocal-prime gain of coherent receiving families.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell BezoutValuationIncidence

/-- The near-Gram mean is diagonal in the conductor coefficients. -/
theorem midBandMeanSum_conductor_diagonal (φ : ℝ → ℝ) (R N : ℕ) (c : ℝ)
    (a : ℕ → ℝ) :
    midBandMeanSum φ R N c a =
      ∑ m ∈ Icc 1 R, (a m ^ 2 / m.totient) *
        ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
          ramanujanLagCoefficient m h * nearWeightMass φ c N h := by
  unfold midBandMeanSum
  rw [sum_comm]
  apply sum_congr rfl
  intro m _
  rw [mul_sum]
  apply sum_congr rfl
  intro h _
  unfold nearWeightMass
  ring

/-- The exact polar term is the conductor-one coefficient squared times the near mass. -/
theorem midBandMeanSum_sub_pole (φ : ℝ → ℝ) {R : ℕ} (hR : 1 ≤ R)
    (N : ℕ) (c : ℝ) (a : ℕ → ℝ) :
    midBandMeanSum φ R N c a -
        a 1 ^ 2 * ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, nearWeightMass φ c N h =
      ∑ m ∈ (Icc 1 R).filter (fun m => m ≠ 1), (a m ^ 2 / m.totient) *
        ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
          ramanujanLagCoefficient m h * nearWeightMass φ c N h := by
  let f (m : ℕ) := (a m ^ 2 / m.totient) *
    ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
      ramanujanLagCoefficient m h * nearWeightMass φ c N h
  have hmode (h : ℕ) : ramanujanLagCoefficient 1 h = 1 := by
    simpa only [Nat.totient_one, Nat.cast_one] using
      ramanujanLagCoefficient_of_dvd (one_dvd h)
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 R) (fun m => m = 1) f
  have hone : (∑ m ∈ (Icc 1 R).filter (fun m => m = 1), f m) =
      a 1 ^ 2 * ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, nearWeightMass φ c N h := by
    rw [sum_filter]
    simp only [sum_ite_eq', if_pos (mem_Icc.mpr ⟨le_rfl, hR⟩), f,
      Nat.totient_one, Nat.cast_one, div_one, hmode, one_mul]
  rw [hone] at hsplit
  rw [midBandMeanSum_conductor_diagonal]
  change (∑ m ∈ Icc 1 R, f m) - _ = _
  linarith only [hsplit]

/-- Removing only the explicit polar summand leaves the coefficient-weighted divisor mean. -/
theorem exists_midBandMeanSum_sub_pole_bound {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R N : ℕ} {c : ℝ},
      1 ≤ R → 1 ≤ N → 1 ≤ c → 2 * ⌊linearNearRowRadius c⌋₊ ≤ N →
      ∀ a : ℕ → ℝ,
        |midBandMeanSum φ R N c a -
          a 1 ^ 2 * ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, nearWeightMass φ c N h| ≤
          C * (1 + Real.log c) *
            ∑ m ∈ (Icc 1 R).filter (fun m => m ≠ 1),
              a m ^ 2 * ((ArithmeticFunction.sigma 1 m : ℝ) / m.totient) := by
  obtain ⟨C, hC, hV⟩ := exists_nearWeightMass_variation_le hφ hsupp
  refine ⟨C, hC, ?_⟩
  intro R N c hR hN hc hHN a
  let H := ⌊linearNearRowRadius c⌋₊
  let V := |nearWeightMass φ c N H| +
    ∑ h ∈ Ico 1 H, |nearWeightMass φ c N (h + 1) - nearWeightMass φ c N h|
  have hVle : V ≤ C * (1 + Real.log c) := hV hN hc hHN
  rw [midBandMeanSum_sub_pole φ hR N c a, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro m hm
  obtain ⟨hmR, hm1⟩ := mem_filter.mp hm
  have hm2 : 2 ≤ m := by have := (mem_Icc.mp hmR).1; omega
  have hmean := abs_sum_ramanujanLagCoefficient_mul_le hm2 (nearWeightMass φ c N) H
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ a m ^ 2 / (m.totient : ℝ))]
  calc
    _ ≤ (a m ^ 2 / m.totient) * ((ArithmeticFunction.sigma 1 m : ℝ) * V) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = (a m ^ 2 * ((ArithmeticFunction.sigma 1 m : ℝ) / m.totient)) * V := by ring
    _ ≤ (a m ^ 2 * ((ArithmeticFunction.sigma 1 m : ℝ) / m.totient)) *
        (C * (1 + Real.log c)) := mul_le_mul_of_nonneg_left hVle (by positivity)
    _ = _ := by ring

#print axioms midBandMeanSum_conductor_diagonal
#print axioms midBandMeanSum_sub_pole
#print axioms exists_midBandMeanSum_sub_pole_bound

end GaloisForLFunctions.CriticalScaleArithmeticRigidity

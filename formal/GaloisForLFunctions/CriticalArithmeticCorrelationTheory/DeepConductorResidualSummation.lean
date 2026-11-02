import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheConductorResidualsAreSmallOnTheDeepRows
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BilinearConductorResidualsAndOneEighthPackets

/-!
# Inverse-energy sums of deep conductor residuals

On deep rows the prime error has no overlap loss. Summing it against the
completed conductor energies costs `c⁷ + Q²(1 + log Q)²`. Every other
channel retains its inverse horizon or inverse depth factor.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity

/-- The coefficient of the quadratic conductor term in the deep center error. -/
def deepCenterCost (N : ℕ) (c X : ℝ) : ℝ :=
  2 * c ^ 2 * harmonic N / ((N : ℝ) ^ 2 * Real.log N) +
    18 * c ^ 2 * ((harmonic N : ℝ) + 1) ^ 2 / (X ^ 2 * Real.log N)

/-- The coefficient of the totient in the deep upward error. -/
def deepUpwardCost (K_up : ℝ) (N : ℕ) (c X : ℝ) : ℝ :=
  3 * (K_up * c ^ 4 * ((linearPrimeStrip c : ℝ) + 1) ^ 6 * (Real.log N / N) ^ 2 +
    2048 * (linearPrimeStrip c : ℝ) ^ 2 * ((linearPrimeStrip c : ℝ) + 1) ^ 2 /
      (X * Real.log N))

/-- All nonprime deep channels after replacing `m²` by `Qm` and `φ(m)` by `m`. -/
def deepNonprimeCost (C_s C_q K₀ K_up : ℝ) (Q N : ℕ) (c X ρ : ℝ) : ℝ :=
  C_s * c ^ 2 / (N : ℝ) ^ 2 + (Q : ℝ) * deepCenterCost N c X +
    32 * K₀ ^ 2 * c ^ 4 / ((N : ℝ) * X * Real.log N) +
    2048 * K₀ ^ 2 * c ^ 2 / (X ^ 2 * Real.log N) +
    C_q * c ^ 10 * (Real.log N / N) ^ 2 + deepUpwardCost K_up N c X +
    3 * ρ ^ 2 * harmonic N / Real.log N

theorem deepNonprimeCost_nonneg {C_s C_q K₀ K_up c X ρ : ℝ} (Q N : ℕ)
    (hCs : 0 ≤ C_s) (hCq : 0 ≤ C_q) (hKu : 0 ≤ K_up)
    (hc : 0 ≤ c) (hX : 0 ≤ X) :
    0 ≤ deepNonprimeCost C_s C_q K₀ K_up Q N c X ρ := by
  have hH := harmonic_nonneg_real N
  have hL := Real.log_natCast_nonneg N
  unfold deepNonprimeCost deepCenterCost deepUpwardCost
  positivity

/-- Only the prime part retains its logarithmic conductor weight. -/
theorem deepResidualBudget_le_linear {C_p C_s C_q K₀ K_up c X ρ : ℝ} {m Q N : ℕ}
    (hm : 1 ≤ m) (hmQ : m ≤ Q) (hKu : 0 ≤ K_up) (hX : 0 ≤ X) :
    deepResidualBudget C_p C_s C_q K₀ K_up m N c X ρ ≤
      C_p * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N +
        (m : ℝ) * deepNonprimeCost C_s C_q K₀ K_up Q N c X ρ := by
  have hH := harmonic_nonneg_real N
  have hL := Real.log_natCast_nonneg N
  have hA : 0 ≤ deepCenterCost N c X := by unfold deepCenterCost; positivity
  have hB : 0 ≤ deepUpwardCost K_up N c X := by unfold deepUpwardCost; positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmQ' : (m : ℝ) ≤ Q := by exact_mod_cast hmQ
  have hφ : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have h1 := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg m) (sub_nonneg.mpr hmQ')) hA
  have h2 := mul_nonneg (sub_nonneg.mpr hφ) hB
  have h3 := mul_nonneg (sub_nonneg.mpr hm1)
    (show 0 ≤ 3 * ρ ^ 2 * harmonic N / Real.log N by positivity)
  have he : C_p * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N +
      (m : ℝ) * deepNonprimeCost C_s C_q K₀ K_up Q N c X ρ -
      deepResidualBudget C_p C_s C_q K₀ K_up m N c X ρ =
      (m : ℝ) * ((Q : ℝ) - m) * deepCenterCost N c X +
        ((m : ℝ) - m.totient) * deepUpwardCost K_up N c X +
        ((m : ℝ) - 1) * (3 * ρ ^ 2 * harmonic N / Real.log N) := by
    unfold deepResidualBudget deepNonprimeCost deepCenterCost deepUpwardCost
    ring
  linarith only [he, h1, h2, h3]

/-- The inverse-energy deep budget separates its overlap-free prime term. -/
theorem sum_deepResidualBudget_div_energy_le {C_p C_s C_q K₀ K_up c X ρ : ℝ}
    (Q N : ℕ) (hCp : 0 ≤ C_p) (hCs : 0 ≤ C_s) (hCq : 0 ≤ C_q)
    (hKu : 0 ≤ K_up) (hc : 1 ≤ c) (hX : 0 ≤ X) :
    (∑ m ∈ Icc 1 Q, deepResidualBudget C_p C_s C_q K₀ K_up m N c X ρ /
      completedConductorEnergy tiltedUnitSpline c m) ≤
      C_p / Real.log N *
        ((8 * c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) /
          tiltedSplineSpectralFloorConstant) +
      deepNonprimeCost C_s C_q K₀ K_up Q N c X ρ *
        ((2 * c ^ 7 + (Q : ℝ) ^ 2) / tiltedSplineSpectralFloorConstant) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hB := deepNonprimeCost_nonneg (K₀ := K₀) (ρ := ρ) Q N hCs hCq hKu hc0.le hX
  calc
    _ ≤ ∑ m ∈ Icc 1 Q,
        (C_p * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N +
          (m : ℝ) * deepNonprimeCost C_s C_q K₀ K_up Q N c X ρ) /
            completedConductorEnergy tiltedUnitSpline c m := by
      refine sum_le_sum fun m hm => ?_
      exact div_le_div_of_nonneg_right
        (deepResidualBudget_le_linear (mem_Icc.mp hm).1 (mem_Icc.mp hm).2 hKu hX)
        (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
          integral_tiltedUnitSpline_sq_pos hc0 (mem_Icc.mp hm).1)
    _ = C_p / Real.log N * (∑ m ∈ Icc 1 Q,
          (m : ℝ) * (1 + Real.log m) ^ 2 / completedConductorEnergy tiltedUnitSpline c m) +
        deepNonprimeCost C_s C_q K₀ K_up Q N c X ρ *
          ∑ m ∈ Icc 1 Q, (m : ℝ) / completedConductorEnergy tiltedUnitSpline c m := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (sum_conductor_log_sq_inv_energy_le hc Q)
        (div_nonneg hCp (Real.log_natCast_nonneg N)))
      (mul_le_mul_of_nonneg_left (sum_conductor_inv_energy_le hc Q) hB)

/-- The actual deep residuals inherit the separated inverse-energy budget. -/
theorem exists_deep_conductor_inv_energy_sum_le :
    ∃ C_p C_s C_q K_up : ℝ, 0 ≤ C_p ∧ 0 ≤ C_s ∧ 0 ≤ C_q ∧ 0 ≤ K_up ∧
      ∀ {Q N : ℕ} {c X ρ : ℝ}, 1 ≤ N → 1 ≤ Real.log N → 1 ≤ c → c / N ≤ 1 →
      2 * ((Real.exp 1 + 3) * c) * linearPrimeStrip c ≤ (N : ℝ) →
      2 * (linearPrimeStrip c : ℝ) + 3 ≤ X → linearNearRowRadius c < X → 2 * c < X →
      (∀ m ∈ Icc 1 Q, ∀ n ∈ Icc 1 N, (n : ℝ) * X ≤ N →
        |shiftedReciprocalUpwardRowError tiltedUnitSpline c id N m n| ≤ ρ / Real.sqrt n ∧
        |shiftedReciprocalUpwardRowError tiltedUnitSpline c (reflectedAffineShift m) N m n| ≤
          ρ / Real.sqrt n) →
      (∑ m ∈ Icc 1 Q,
        deepMass X (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N) /
            completedConductorEnergy tiltedUnitSpline c m) ≤
        8 * (C_p / Real.log N *
          ((8 * c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) /
            tiltedSplineSpectralFloorConstant) +
          deepNonprimeCost C_s C_q
            (152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2))
            K_up Q N c X ρ *
              ((2 * c ^ 7 + (Q : ℝ) ^ 2) / tiltedSplineSpectralFloorConstant)) := by
  obtain ⟨C_p, C_s, C_q, K_up, hCp, hCs, hCq, hKu, hres⟩ :=
    exists_deepMass_conductorResidual_le contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      integral_tiltedUnitSpline_sq_pos
  refine ⟨C_p, C_s, C_q, K_up, hCp, hCs, hCq, hKu, ?_⟩
  intro Q N c X ρ hN hL hc hw hkernel hXB hXR hX2 hrate
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hX : 0 ≤ X := by linarith only [hc, hX2]
  calc
    _ ≤ ∑ m ∈ Icc 1 Q, 8 *
        deepResidualBudget C_p C_s C_q
          (152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2))
          K_up m N c X ρ / completedConductorEnergy tiltedUnitSpline c m := by
      refine sum_le_sum fun m hm => ?_
      exact div_le_div_of_nonneg_right
        (hres (mem_Icc.mp hm).1 hN hL hc hw hkernel hXB hXR hX2 (hrate m hm))
        (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
          integral_tiltedUnitSpline_sq_pos hc0 (mem_Icc.mp hm).1)
    _ = 8 * ∑ m ∈ Icc 1 Q,
        deepResidualBudget C_p C_s C_q
          (152 * (∫ u, |tiltedUnitSpline u|) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2))
          K_up m N c X ρ / completedConductorEnergy tiltedUnitSpline c m := by
      simp only [mul_sum, mul_div_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_deepResidualBudget_div_energy_le Q N hCp hCs hCq hKu hc hX) (by norm_num)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

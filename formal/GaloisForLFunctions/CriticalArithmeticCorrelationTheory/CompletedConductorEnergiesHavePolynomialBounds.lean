import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AffinePrimeShellsHavePolynomialGrowth
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.OverlapForcesNewRamanujanTerms

/-!
# Polynomial bounds for completed conductor energies

The zero affine multiplier removes the Ramanujan amplitude from the signed
shell estimate. Exact self and pole scaling then bound each completed energy,
controlling its amplification of finite-horizon Gram errors.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis BezoutValuationIncidence
  RenormalizedArithmeticPotentialTheory.CompletedShell

/-- Taking the zero multiplier removes the conductor amplitude from the shell bound. -/
theorem abs_shellCorrection_le_polynomial {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) {c : ℝ} (hc : 1 ≤ c) :
    |shellCorrection φ c m| ≤ 4 * (Real.log 4 + 4) * c ^ 2 := by
  have h := abs_shellCorrectionOfShift_mean_le_polynomial hm hφ hsupp hM 0 id hc
  have hφm : 0 < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  rw [ramanujanLagCoefficient_of_dvd (dvd_zero m), abs_mul, abs_of_pos hφm] at h
  change (m.totient : ℝ) * |shellCorrection φ c m| ≤ _ at h
  have hscaled : (m.totient : ℝ) * |shellCorrection φ c m| ≤
      (m.totient : ℝ) * (4 * (Real.log 4 + 4) * c ^ 2) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  by_contra hbad
  exact (not_lt_of_ge hscaled) (mul_lt_mul_of_pos_left (lt_of_not_ge hbad) hφm)

/-- The absolute completed energy of each fixed conductor has a quadratic overlap bound. -/
theorem exists_completedConductorEnergy_polynomial_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 1 ≤ c → |completedConductorEnergy φ c m| ≤ C * c ^ 2 := by
  let S := |completeWeilSelfFinitePart φ 1 + ramanujanAdjunctionEnergy m - Real.eulerMascheroniConstant|
  have hS : 0 ≤ S := abs_nonneg _
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  refine ⟨S + 2 + 4 * (Real.log 4 + 4), by positivity, ?_⟩
  intro c hc
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hc2 : c ≤ c ^ 2 := by nlinarith only [hc]
  have hbase : S ≤ S * c ^ 2 := by
    have h1 : 1 ≤ c ^ 2 := by nlinarith only [hc]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h1 hS
  have hlogc : |Real.log c| ≤ c := by
    rw [abs_of_nonneg (Real.log_nonneg hc)]
    exact (Real.log_le_sub_one_of_pos hc0).trans (by linarith)
  have hcharge : |if m = 1 then completeWeilPoleShift φ c else 0| ≤ c := by
    split_ifs
    · rw [abs_of_nonneg (completeWeilPoleShift_nonneg φ hc0.le)]
      exact completeWeilPoleShift_le hφ.continuous hsupp hM hc0.le
    · simpa only [abs_zero] using hc0.le
  have href : |completeWeilAdjunctionEnergy φ c m| ≤ (S + 2) * c ^ 2 := by
    have hid : completeWeilAdjunctionEnergy φ c m =
        (completeWeilSelfFinitePart φ 1 + ramanujanAdjunctionEnergy m - Real.eulerMascheroniConstant) -
          Real.log c + (if m = 1 then completeWeilPoleShift φ c else 0) := by
      rw [completeWeilAdjunctionEnergy, completeWeilSelfFinitePart_eq_at_one_sub_log φ hc0]
      ring
    rw [hid]
    calc
      _ ≤ S + |Real.log c| + |if m = 1 then completeWeilPoleShift φ c else 0| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ S + c + c := add_le_add (add_le_add le_rfl hlogc) hcharge
      _ ≤ _ := by nlinarith only [hbase, hc2]
  rw [completedConductorEnergy_eq_sub_shellCorrection hc0 hm]
  calc
    _ ≤ |completeWeilAdjunctionEnergy φ c m| + |shellCorrection φ c m| := abs_sub _ _
    _ ≤ (S + 2) * c ^ 2 + 4 * (Real.log 4 + 4) * c ^ 2 :=
      add_le_add href (abs_shellCorrection_le_polynomial hφ hsupp hM hm hc)
    _ = _ := by ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_shellCorrection_le_polynomial
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completedConductorEnergy_polynomial_bound

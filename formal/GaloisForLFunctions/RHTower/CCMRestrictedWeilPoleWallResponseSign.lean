import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleWallFieldWeld
import GaloisForLFunctions.RHTower.BaezDuarteWaveletPairing

/-!
# One-sided even critical-wall response

Every admitted critical-Mellin atom weakly lowers the literal even restricted-Weil pole.
This retains each prime coefficient and its entry age; no absolute-value estimate is taken.
-/

open scoped BigOperators
noncomputable section

namespace RHTower

/-- An even critical-wall response is nonpositive at and after its own entry. -/
theorem ccmWeilEvenWallEnergyResponse_nonpos_after_entry
    (n : ℕ) (s : ℝ) (hs : Real.log n / 2 ≤ s) :
    ccmWeilEvenWallEnergyResponse n s ≤ 0 := by
  rw [ccmWeilEvenWallEnergyResponse_eq_hyperbolic]
  have hx : 0 ≤ s - Real.log n / 2 := sub_nonneg.mpr hs
  have hterm : 0 ≤
      (s - Real.log n / 2) * Real.cosh (Real.log n / 2) +
        Real.sinh (s - Real.log n / 2) := by
    have hmul : 0 ≤ (s - Real.log n / 2) * Real.cosh (Real.log n / 2) :=
      mul_nonneg hx (Real.cosh_pos _).le
    have hsinh : 0 ≤ Real.sinh (s - Real.log n / 2) := by
      nlinarith [Real.self_le_sinh_iff.mpr hx]
    linarith
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) hterm

/-- An even critical-wall response is strictly negative after its own entry. -/
theorem ccmWeilEvenWallEnergyResponse_neg_after_entry
    (n : ℕ) (s : ℝ) (hs : Real.log n / 2 < s) :
    ccmWeilEvenWallEnergyResponse n s < 0 := by
  rw [ccmWeilEvenWallEnergyResponse_eq_hyperbolic]
  have hx : 0 < s - Real.log n / 2 := sub_pos.mpr hs
  have hterm : 0 <
      (s - Real.log n / 2) * Real.cosh (Real.log n / 2) +
        Real.sinh (s - Real.log n / 2) := by
    have hmul : 0 < (s - Real.log n / 2) * Real.cosh (Real.log n / 2) :=
      mul_pos hx (Real.cosh_pos _)
    have hsinh : 0 ≤ Real.sinh (s - Real.log n / 2) := by
      nlinarith [Real.self_le_sinh_iff.mpr hx.le]
    linarith
  exact mul_neg_of_neg_of_pos (by norm_num) hterm

/-- The literal finite even restricted-Weil pole never exceeds its smooth
prime--polar--Gamma carrier. Every retained arithmetic wall response has the opposite sign. -/
theorem ccmWeilEvenPole_le_smooth (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) ≤
      2 * (ccmWeilPoleDiagonalSmooth a.1 + ccmWeilPoleCrossSmooth a.1) := by
  rw [ccmWeilEvenPole_eq_criticalMellinWallEnergySuperposition]
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
      criticalMellinAtomWeight n * ccmWeilEvenWallEnergyResponse n a.1 ≤ 0 := by
    apply Finset.sum_nonpos
    intro n hn
    apply mul_nonpos_of_nonneg_of_nonpos (criticalMellinAtomWeight_nonneg n)
    apply ccmWeilEvenWallEnergyResponse_nonpos_after_entry
    have hlog : Real.log n ≤ 2 * a.1 := by
      apply log_natCast_le
      · linarith [a.2]
      · exact Finset.mem_Icc.mp hn |>.2
    linarith
  linarith

end RHTower

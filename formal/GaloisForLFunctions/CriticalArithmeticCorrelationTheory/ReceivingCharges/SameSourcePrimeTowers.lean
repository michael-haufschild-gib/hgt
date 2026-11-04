import GaloisForLFunctions.BezoutValuationIncidence.Sieve.AffineResidues
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonDivergenceLivesOnTheTorsionOrbits

/-!
# Same-source prime towers in affine rows

A source prime dividing the multiplier cannot divide either nonzero small
offset. Its full reciprocal Mangoldt tower is controlled by logarithmic charge.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open Finset ArithmeticFunction
open GaloisForLFunctions
open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory

/-- A nonzero shift smaller than the source prime cannot lie in its multiplier tower. -/
theorem same_source_positive_nondivisibility {p k n h : ℕ}
    (hpk : p ∣ k) (hh : 0 < h) (hhp : h < p) : ¬p ∣ k * n + h := by
  intro hd
  have hkn : k * n ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hpk n)
  have hshift : k * n + h ≡ h [MOD p] := by
    simpa only [zero_add] using hkn.add_right h
  have hdiv : p ∣ h := Nat.modEq_zero_iff_dvd.mp
    (hshift.symm.trans (Nat.modEq_zero_iff_dvd.mpr hd))
  exact (not_le.mpr hhp) (Nat.le_of_dvd hh hdiv)

/-- The negative offset has the same nondivisibility law whenever subtraction is genuine. -/
theorem same_source_negative_nondivisibility {p k n h : ℕ}
    (hpk : p ∣ k) (hh : 0 < h) (hhp : h < p) (hhkn : h ≤ k * n) : ¬p ∣ k * n - h := by
  intro hd
  have hcong := (dvd_negative_shift_iff hhkn).mp hd
  have hkn : k * n ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hpk n)
  have hdiv : p ∣ h := Nat.modEq_zero_iff_dvd.mp (hcong.symm.trans hkn)
  exact (not_le.mpr hhp) (Nat.le_of_dvd hh hdiv)

/-- The exceptional source-prime towers cost one inverse band endpoint times their logarithmic charge. -/
theorem source_prime_tower_mass_le {P : Finset ℕ} {R : ℕ} (hR : 0 < R)
    (hP : ∀ p ∈ P, p.Prime) (hRP : ∀ p ∈ P, R < p) (Y : ℕ) :
    (∑ p ∈ P, (1 / (p : ℝ)) *
      ∑ k ∈ Icc 1 Y, if p ∣ k then vonMangoldt k / (k : ℝ) else 0) ≤
        (2 / (R : ℝ)) * ∑ p ∈ P, Real.log p / (p : ℝ) := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
  have hp1 : 0 < (p : ℝ) - 1 := by linarith only [hp2]
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have htower : (∑ k ∈ Icc 1 Y, if p ∣ k then vonMangoldt k / (k : ℝ) else 0) ≤
      2 * Real.log p / p := by
    refine (sum_dvd_vonMangoldt_div_le (hP p hp) (Icc 1 Y)).trans ?_
    apply (div_le_div_iff₀ hp1 hp0).mpr
    have h := mul_nonneg hlog (sub_nonneg.mpr hp2)
    nlinarith only [h]
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hRp : (R : ℝ) ≤ p := by exact_mod_cast (hRP p hp).le
  calc
    _ ≤ (1 / (p : ℝ)) * (2 * Real.log p / p) :=
      mul_le_mul_of_nonneg_left htower (by positivity)
    _ = (2 / (p : ℝ)) * (Real.log p / p) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left zero_le_two hR0 hRp) (div_nonneg hlog hp0.le)

#print axioms same_source_positive_nondivisibility
#print axioms same_source_negative_nondivisibility
#print axioms source_prime_tower_mass_le

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

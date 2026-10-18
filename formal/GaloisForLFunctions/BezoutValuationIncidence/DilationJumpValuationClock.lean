import GaloisForLFunctions.BezoutValuationIncidence.DilationProfileIntegerJumpCoupling
import GaloisForLFunctions.BezoutValuationIncidence.ValuationVisibilityClockAndRamanujanSupport

/-!
# The valuation clock inside physical dilation jump sectors

Transport the existing exact Ramanujan support law to the literal coefficients
of the dilation profile. If a pair contributes at gap `p*a-q*b`, the product
`lagVisibilityClock r * gcd(p,q)` divides that gap. Filtering finite sectors by
this product clock preserves the original profile coupling and its error.
On successor pairs, squarefreeness is exactly the pointwise nonvanishing
boundary. Allowed signed sector sums may still cancel.
-/

open Finset RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section

/-- The literal jump coefficient is the existing real translated-mode coefficient. -/
theorem ramanujanNaturalCoefficient_re_eq_lagCoefficient (r n : ℕ) :
    (d4BMRamanujanNaturalCoefficient n r).re = ramanujanLagCoefficient r n := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [d4BMRamanujanNaturalCoefficient, ramanujanLagCoefficient]
  · rw [d4BMRamanujanNaturalCoefficient_eq_gcd_mobiusDivisorSum hr,
      ramanujanLagCoefficient_eq_gcd_divisor_sum, Nat.gcd_comm n r]
    simp [moebiusReal]

/-- Transport the existing valuation support law without rebuilding its number theory. -/
theorem ramanujanNaturalCoefficient_re_ne_zero_iff_clock (r n : ℕ) :
    (d4BMRamanujanNaturalCoefficient n r).re ≠ 0 ↔
      r ≠ 0 ∧ lagVisibilityClock r ∣ n := by
  rw [ramanujanNaturalCoefficient_re_eq_lagCoefficient]
  exact ramanujanLagCoefficient_ne_zero_iff r n

/-- Exact support of a pair amplitude is the common valuation clock of its two indices. -/
theorem ramanujan_pair_re_ne_zero_iff_clock (r a b : ℕ) :
    (d4BMRamanujanNaturalCoefficient a r).re *
        (d4BMRamanujanNaturalCoefficient b r).re ≠ 0 ↔
      r ≠ 0 ∧ lagVisibilityClock r ∣ Nat.gcd a b := by
  rw [mul_ne_zero_iff, ramanujanNaturalCoefficient_re_ne_zero_iff_clock,
    ramanujanNaturalCoefficient_re_ne_zero_iff_clock, Nat.dvd_gcd_iff]
  tauto

/-- On an actual successor fiber, squarefreeness is the exact pointwise visibility boundary. -/
theorem successor_pair_re_ne_zero_iff_squarefree (r : ℕ) {p q : ℕ} {ab : ℕ × ℕ}
    (hgap : dilationJumpGap p q ab = 1) :
    (d4BMRamanujanNaturalCoefficient ab.1 r).re *
        (d4BMRamanujanNaturalCoefficient ab.2 r).re ≠ 0 ↔ Squarefree r := by
  have hgcd : Nat.gcd ab.1 ab.2 = 1 := (dilationJumpGap_one_coprime hgap).2
  rw [ramanujan_pair_re_ne_zero_iff_clock, hgcd]
  simpa using (squarefree_lag_quotient_iff r 1).symm

/-- The mode clock and scale gcd multiply in the physical additive gap. -/
theorem jointClock_dvd_dilationJumpGap_of_pair_ne_zero (r p q : ℕ) (ab : ℕ × ℕ)
    (hc : (d4BMRamanujanNaturalCoefficient ab.1 r).re *
      (d4BMRamanujanNaturalCoefficient ab.2 r).re ≠ 0) :
    ((lagVisibilityClock r * Nat.gcd p q : ℕ) : ℤ) ∣ dilationJumpGap p q ab := by
  have hv := (ramanujan_pair_re_ne_zero_iff_clock r ab.1 ab.2).mp hc
  have ha : lagVisibilityClock r ∣ ab.1 := hv.2.trans (Nat.gcd_dvd_left _ _)
  have hb : lagVisibilityClock r ∣ ab.2 := hv.2.trans (Nat.gcd_dvd_right _ _)
  have hpa : lagVisibilityClock r * Nat.gcd p q ∣ p * ab.1 := by
    simpa only [Nat.mul_comm] using mul_dvd_mul ha (Nat.gcd_dvd_left p q)
  have hqb : lagVisibilityClock r * Nat.gcd p q ∣ q * ab.2 := by
    simpa only [Nat.mul_comm] using mul_dvd_mul hb (Nat.gcd_dvd_right p q)
  have hpaZ : ((lagVisibilityClock r * Nat.gcd p q : ℕ) : ℤ) ∣
      (p : ℤ) * ab.1 := by exact_mod_cast hpa
  have hqbZ : ((lagVisibilityClock r * Nat.gcd p q : ℕ) : ℤ) ∣
      (q : ℤ) * ab.2 := by exact_mod_cast hqb
  exact dvd_sub hpaZ hqbZ

/-- A forbidden physical gap has zero pair contribution, independently of the cutoff. -/
theorem ramanujanJumpPairTerm_eq_zero_of_not_jointClock_dvd
    (r p q H : ℕ) (ab : ℕ × ℕ)
    (hh : ¬ ((lagVisibilityClock r * Nat.gcd p q : ℕ) : ℤ) ∣
      dilationJumpGap p q ab) :
    ramanujanJumpPairTerm r p q H ab = 0 := by
  by_contra ht
  apply hh
  apply jointClock_dvd_dilationJumpGap_of_pair_ne_zero r p q ab
  intro hz
  exact ht (by simp [ramanujanJumpPairTerm, hz])

/-- Every lag outside the product clock is absent at every finite physical horizon. -/
theorem ramanujanDilationLagSector_eq_zero_of_not_jointClock_dvd
    (r p q H : ℕ) (h : ℤ)
    (hh : ¬ ((lagVisibilityClock r * Nat.gcd p q : ℕ) : ℤ) ∣ h) :
    ramanujanDilationLagSector r p q H h = 0 := by
  apply sum_eq_zero
  intro ab hab
  apply ramanujanJumpPairTerm_eq_zero_of_not_jointClock_dvd r p q H ab
  simpa only [(mem_filter.mp hab).2] using hh

/-- Nonsquarefree modes have no successor contribution, not just zero period mean. -/
theorem ramanujanDilationLagSector_one_eq_zero_of_not_squarefree
    (r p q H : ℕ) (hr : ¬ Squarefree r) :
    ramanujanDilationLagSector r p q H 1 = 0 := by
  apply sum_eq_zero
  intro ab hab
  have hc : (d4BMRamanujanNaturalCoefficient ab.1 r).re *
      (d4BMRamanujanNaturalCoefficient ab.2 r).re = 0 := by
    by_contra hn
    exact hr ((successor_pair_re_ne_zero_iff_squarefree r (mem_filter.mp hab).2).mp hn)
  simp [ramanujanJumpPairTerm, hc]

/-- The full finite lag sum retains exactly the potentially visible product-clock lags. -/
theorem sum_dilation_lag_sectors_eq_jointClock_filter (r p q H : ℕ) :
    (∑ h ∈ (dilationJumpPairs H p q).image (dilationJumpGap p q),
      ramanujanDilationLagSector r p q H h) =
    ∑ h ∈ ((dilationJumpPairs H p q).image (dilationJumpGap p q)).filter
        (fun h => ((lagVisibilityClock r * Nat.gcd p q : ℕ) : ℤ) ∣ h),
      ramanujanDilationLagSector r p q H h := by
  rw [sum_filter]
  apply sum_congr rfl
  intro h _
  by_cases hv : ((lagVisibilityClock r * Nat.gcd p q : ℕ) : ℤ) ∣ h
  · rw [if_pos hv]
  · rw [if_neg hv]
    exact ramanujanDilationLagSector_eq_zero_of_not_jointClock_dvd r p q H h hv

/-- Valuation-clock selection preserves the original profile and its cutoff error. -/
theorem abs_dilationProfile_sub_jointClock_sectors_le {r p q : ℕ}
    (hr : 1 < r) (hp : 0 < p) (hq : 0 < q) (H : ℕ) :
    |pmRamanujanDilationProfile r hr ((p : ℝ) / q) -
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        (∑ h ∈ ((dilationJumpPairs H p q).image (dilationJumpGap p q)).filter
            (fun h => ((lagVisibilityClock r * Nat.gcd p q : ℕ) : ℤ) ∣ h),
          ramanujanDilationLagSector r p q H h)| ≤
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        (pmRamanujanPrimitiveBound r ^ 2 / ((H : ℝ) + 1)) := by
  rw [← sum_dilation_lag_sectors_eq_jointClock_filter]
  exact abs_dilationProfile_sub_finite_lag_sectors_le hr hp hq H

/-- Unconditional actual-profile coupling to the product of mode and scale clocks. -/
theorem dilation_profile_valuation_clock_coupling (r n m H : ℕ) :
    let R := r + 2
    let p := n + 1
    let q := m + 1
    |pmRamanujanDilationProfile R (by dsimp [R]; omega) ((p : ℝ) / q) -
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        (∑ h ∈ ((dilationJumpPairs H p q).image (dilationJumpGap p q)).filter
            (fun h => ((lagVisibilityClock R * Nat.gcd p q : ℕ) : ℤ) ∣ h),
          ramanujanDilationLagSector R p q H h)| ≤
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        (pmRamanujanPrimitiveBound R ^ 2 / ((H : ℝ) + 1)) := by
  dsimp only
  exact abs_dilationProfile_sub_jointClock_sectors_le (by omega) (by omega) (by omega) H

end
end GaloisForLFunctions.BezoutValuationIncidence

import GaloisForLFunctions.BezoutValuationIncidence.DilationClockSectorBoundaryAndSuccessorTransport
import GaloisForLFunctions.BezoutValuationIncidence.DilationSuccessorLeastSeedResonance


/-!
# The radical least seed in the original physical clock sector

Use the existing least-seed estimate at the squarefree radical, then transport
its successor sector to the original visibility clock at an aligned physical
cutoff. The resulting actual-profile bound retains the full signed complement.
The seed is nonzero exactly for coprime scales, even when the original mode is
nonsquarefree and its lag-one sector vanishes.

The last theorem has data parameters only. Seed nonvanishing is qualitative:
it supplies no uniform lower bound and no bound on the other signed sectors.
-/

open Finset RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section

/-- Every allowed least successor seed at the radical has nonzero arithmetic amplitude. -/
theorem successorLeastSeedResonance_radical_ne_zero_iff_coprime {r p q : ℕ}
    (hr : r ≠ 0) (hp : 1 < p) (hq : 1 < q) :
    successorLeastSeedResonance (primeRadical r) p q ≠ 0 ↔ Nat.Coprime p q := by
  by_cases hc : Nat.Coprime p q
  · have hs := leastSuccessorSeed_spec hp hq hc
    have hgap : dilationJumpGap p q (leastSuccessorSeed p q) = 1 := by
      have hh : (p : ℤ) * (leastSuccessorSeed p q).1 =
          (q : ℤ) * (leastSuccessorSeed p q).2 + 1 := by exact_mod_cast hs.2.2.2
      unfold dilationJumpGap
      omega
    have hprod := (successor_pair_re_ne_zero_iff_squarefree (primeRadical r) hgap).mpr
      (squarefree_primeRadical r hr)
    have ha0 : ((leastSuccessorSeed p q).1 : ℝ) ≠ 0 := by
      exact_mod_cast (show (leastSuccessorSeed p q).1 ≠ 0 by omega)
    have hn : successorLeastSeedResonance (primeRadical r) p q ≠ 0 := div_ne_zero hprod ha0
    exact ⟨fun _ => hc, fun _ => hn⟩
  · simp [successorLeastSeedResonance, leastSuccessorSeed, hc]

/-- The original physical clock sector inherits the established radical least-seed estimate. -/
theorem abs_normalized_clock_successor_sector_sub_radicalSeed_le {r p q : ℕ}
    (hr : r ≠ 0) (hp : 1 < p) (hq : 1 < q) :
    let s := primeRadical r
    let v := lagVisibilityClock r
    let H := v * (p * q * s + 1) - 1
    |Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        ramanujanDilationLagSector r p q H (v : ℤ) -
      (v : ℝ) * (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
        successorLeastSeedResonance s p q| ≤
      (v : ℝ) * ((s : ℝ) * (s.totient : ℝ) ^ 2 /
        (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ))) := by
  dsimp only
  have hspos : 0 < primeRadical r :=
    prod_pos fun _ hp => (Nat.mem_primeFactors.mp hp).1.pos
  have hs := abs_normalized_successor_sector_sub_leastSeed_le
    ⟨primeRadical r, hspos⟩ hp hq
  have hsector := ramanujanDilationLagSector_clock_aligned hr
    (by omega : 0 < p) (by omega : 0 < q) (p * q * primeRadical r) 1
  simp only [mul_one] at hsector
  rw [hsector]
  have he : Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
      ((lagVisibilityClock r : ℝ) *
        ramanujanDilationLagSector (primeRadical r) p q (p * q * primeRadical r) 1) -
      (lagVisibilityClock r : ℝ) * (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
        successorLeastSeedResonance (primeRadical r) p q =
      (lagVisibilityClock r : ℝ) *
        (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          ramanujanDilationLagSector (primeRadical r) p q (p * q * primeRadical r) 1 -
          (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
            successorLeastSeedResonance (primeRadical r) p q) := by ring
  rw [he, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)

/-- The actual profile retains a radical least seed at physical lag equal to its clock. -/
theorem abs_dilationProfile_sub_clockSeed_and_other_sectors_le {r p q : ℕ}
    (hr : 1 < r) (hp : 1 < p) (hq : 1 < q) :
    let s := primeRadical r
    let v := lagVisibilityClock r
    let H := v * (p * q * s + 1) - 1
    |pmRamanujanDilationProfile r hr ((p : ℝ) / q) -
        Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          ((∑ h ∈ (dilationJumpPairs H p q).image (dilationJumpGap p q),
            ramanujanDilationLagSector r p q H h) - ramanujanDilationLagSector r p q H (v : ℤ)) -
        (v : ℝ) * (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
          successorLeastSeedResonance s p q| ≤
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) * (pmRamanujanPrimitiveBound r ^ 2 / ((H : ℝ) + 1)) +
        (v : ℝ) * ((s : ℝ) * (s.totient : ℝ) ^ 2 /
          (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ))) := by
  dsimp only
  let H := lagVisibilityClock r * (p * q * primeRadical r + 1) - 1
  have hprofile := abs_dilationProfile_sub_finite_lag_sectors_le hr
    (by omega : 0 < p) (by omega : 0 < q) H
  have hsector := abs_normalized_clock_successor_sector_sub_radicalSeed_le
    (by omega : r ≠ 0) hp hq
  have he : pmRamanujanDilationProfile r hr ((p : ℝ) / q) -
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        ((∑ h ∈ (dilationJumpPairs H p q).image (dilationJumpGap p q),
          ramanujanDilationLagSector r p q H h) -
            ramanujanDilationLagSector r p q H (lagVisibilityClock r : ℤ)) -
      (lagVisibilityClock r : ℝ) * (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
        successorLeastSeedResonance (primeRadical r) p q =
      (pmRamanujanDilationProfile r hr ((p : ℝ) / q) -
        Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          (∑ h ∈ (dilationJumpPairs H p q).image (dilationJumpGap p q),
            ramanujanDilationLagSector r p q H h)) +
      (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        ramanujanDilationLagSector r p q H (lagVisibilityClock r : ℤ) -
        (lagVisibilityClock r : ℝ) * (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
          successorLeastSeedResonance (primeRadical r) p q) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hprofile hsector)

/-- Data-only clock-successor coupling and exact nonvanishing classification of its seed. -/
theorem dilation_profile_clock_successor_seed_coupling (r n m : ℕ) :
    let R := r + 2
    let p := n + 2
    let q := m + 2
    let s := primeRadical R
    let v := lagVisibilityClock R
    let H := v * (p * q * s + 1) - 1
    (|pmRamanujanDilationProfile R (by dsimp [R]; omega) ((p : ℝ) / q) -
        Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          ((∑ h ∈ (dilationJumpPairs H p q).image (dilationJumpGap p q),
            ramanujanDilationLagSector R p q H h) - ramanujanDilationLagSector R p q H (v : ℤ)) -
        (v : ℝ) * (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
          successorLeastSeedResonance s p q| ≤
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) * (pmRamanujanPrimitiveBound R ^ 2 / ((H : ℝ) + 1)) +
        (v : ℝ) * ((s : ℝ) * (s.totient : ℝ) ^ 2 /
          (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)))) ∧
      (successorLeastSeedResonance s p q ≠ 0 ↔ Nat.Coprime p q) := by
  dsimp only
  exact ⟨abs_dilationProfile_sub_clockSeed_and_other_sectors_le (by omega) (by omega) (by omega),
    successorLeastSeedResonance_radical_ne_zero_iff_coprime (by omega) (by omega) (by omega)⟩

end
end GaloisForLFunctions.BezoutValuationIncidence

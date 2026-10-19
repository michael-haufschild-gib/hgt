import GaloisForLFunctions.BiScaleUncertainty.SieveHighestDyadicCoordinate
import GaloisForLFunctions.BezoutValuationIncidence.PrimeTailCalibrationAndMobiusDefect
import GaloisForLFunctions.RHTower.Sieve.BarbanVehovWeight
import Mathlib.Algebra.Squarefree.Basic

/-!
# Arithmetic source anchors for finite sieve observations

Squarefree-supported coefficient rows have zero Selberg coordinates at every
non-squarefree mode. In particular, the highest-dyadic coordinate vanishes for
`N ≥ 4`, so the nonzero highest-dyadic local classification does not apply to
Möbius rows or their scalar tapers.

A terminal prime has a single multiple in the coefficient support. Its weighted
Möbius coordinate is nonzero exactly when its taper is nonzero. For the
Barban–Vehov row this means `p < X`, not merely `p ≤ N`. These are applicability
and nonvanishing results; no prime-anchored local inverse classification is
asserted.
-/

open Finset
open scoped ArithmeticFunction.Moebius
open GaloisForLFunctions.BezoutValuationIncidence RHTower.Sieve

namespace GaloisForLFunctions.BiScaleUncertainty
open SieveMoments
noncomputable section
set_option autoImplicit false

/-- A nonsquarefree divisor cannot divide a squarefree element of the support. -/
theorem selbergMultiplesCoord_eq_zero_of_not_squarefree (N q : ℕ) (c : ℕ → ℝ)
    (hc : ∀ d, ¬Squarefree d → c d = 0) (hq : ¬Squarefree q) :
    selbergMultiplesCoord N c q = 0 := by
  unfold selbergMultiplesCoord
  apply Finset.sum_eq_zero
  intro d hd
  have hqd : q ∣ d := (Finset.mem_filter.mp hd).2
  have hds : ¬Squarefree d := fun hs => hq (hs.squarefree_of_dvd hqd)
  rw [hc d hds, zero_div]

theorem selbergMultiplesCoord_topOrder_eq_zero_of_squarefree_support
    (N : ℕ) (hN : 4 ≤ N) (c : ℕ → ℝ)
    (hc : ∀ d, ¬Squarefree d → c d = 0) :
    selbergMultiplesCoord N c (TopAnchor.topOrder N) = 0 := by
  apply selbergMultiplesCoord_eq_zero_of_not_squarefree N _ c hc
  unfold TopAnchor.topOrder
  intro hs
  have hh : 2 ≤ Nat.log 2 N :=
    Nat.le_log_of_pow_le (by decide) (by norm_num; exact hN)
  have hu : ¬IsUnit (2 : ℕ) := by norm_num
  rcases hs.eq_zero_or_one_of_pow_of_not_isUnit hu with h | h <;> omega

/-- Every scalar taper of the Möbius coefficients misses the highest-dyadic stratum. -/
theorem selbergMultiplesCoord_moebius_mul_topOrder (N : ℕ) (hN : 4 ≤ N)
    (w : ℕ → ℝ) :
    selbergMultiplesCoord N (fun d => (μ d : ℝ) * w d) (TopAnchor.topOrder N) = 0 := by
  apply selbergMultiplesCoord_topOrder_eq_zero_of_squarefree_support N hN
  intro d hd
  simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]

/-- The existing single-multiple prime coordinate specialized to a Möbius taper. -/
theorem selbergMultiplesCoord_moebius_mul_primeTail {N p : ℕ}
    (hp : p ∈ sievePrimeTail N) (w : ℕ → ℝ) :
    selbergMultiplesCoord N (fun d => (μ d : ℝ) * w d) p = -w p / (p : ℝ) := by
  rw [selbergMultiplesCoord_primeTail hp]
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
  simp [ArithmeticFunction.moebius_apply_prime hprime]

/-- A prime anchor survives exactly when its scalar taper does. -/
theorem selbergMultiplesCoord_moebius_mul_primeTail_ne_zero_iff {N p : ℕ}
    (hp : p ∈ sievePrimeTail N) (w : ℕ → ℝ) :
    selbergMultiplesCoord N (fun d => (μ d : ℝ) * w d) p ≠ 0 ↔ w p ≠ 0 := by
  rw [selbergMultiplesCoord_moebius_mul_primeTail hp w]
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  simp [hp0]

/-- A terminal prime is a Barban–Vehov anchor precisely below the taper cutoff. -/
theorem selbergMultiplesCoord_barbanVehov_primeTail_ne_zero_iff {N p : ℕ}
    (hp : p ∈ sievePrimeTail N) (X : ℕ) :
    selbergMultiplesCoord N (barbanVehovWeight X) p ≠ 0 ↔ p < X := by
  rw [selbergMultiplesCoord_primeTail hp]
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  by_cases hlt : p < X
  · have hlog : 0 < Real.log ((X : ℝ) / p) := by
      apply Real.log_pos
      exact (lt_div_iff₀ hp0).mpr (by simpa using (Nat.cast_lt.mpr hlt : (p : ℝ) < X))
    simp [barbanVehovWeight, hlt.le, ArithmeticFunction.moebius_apply_prime hprime,
      hlt, hlog.ne', hp0.ne']
  · by_cases hle : p ≤ X
    · have heq : X = p := by omega
      subst X
      simp [barbanVehovWeight, hp0.ne']
    · simp [barbanVehovWeight, hle, hlt]

end
end GaloisForLFunctions.BiScaleUncertainty

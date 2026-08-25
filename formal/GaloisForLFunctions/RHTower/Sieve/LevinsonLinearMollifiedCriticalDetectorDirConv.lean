import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifiedCriticalDirConv
import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifiedCriticalDetectorCoefficient

/-!
# Finite convolution bridge for the critical detector

An arbitrary positive-natural head is reindexed against the literal linear mollifier.  The critical
log-differentiated head then specializes to its exact Barban--Vehov divisor coefficient.
-/

open Finset Complex

noncomputable section

namespace RHTower.Sieve

/-- Generic short-head reindex against the literal linear mollifier. -/
theorem dirConv_natSucc_mul_levinsonLinearMollifier_eq_divisorSum
    (a : ℕ → ℂ) (L M : ℕ) (r : Fin (L * M)) (hrL : (r : ℕ) + 1 ≤ L) :
    dirConv L M (fun n : Fin L => a ((n : ℕ) + 1))
        (RHTower.levinsonLinearMollifierFinCoeff M) r =
      ∑ q ∈ ((r : ℕ) + 1).divisors,
        a (((r : ℕ) + 1) / q) * levinsonLinearMollifierCoeff M q := by
  classical
  let K : ℕ := (r : ℕ) + 1
  have hK : 0 < K := by dsimp only [K]; omega
  rw [dirConv_eq_sum_divisors_finCoeffNat]
  have hterm : ∀ d ∈ K.divisors,
      finCoeffNat L (fun n : Fin L => a ((n : ℕ) + 1)) d *
          finCoeffNat M (RHTower.levinsonLinearMollifierFinCoeff M) (K / d) =
        a d * levinsonLinearMollifierCoeff M (K / d) := by
    intro d hdmem
    have hdvd : d ∣ K := Nat.dvd_of_mem_divisors hdmem
    have hdpos : 1 ≤ d := Nat.pos_of_mem_divisors hdmem
    have hdK : d ≤ K := Nat.le_of_dvd hK hdvd
    have hqpos : 1 ≤ K / d :=
      Nat.one_le_div_iff (by omega) |>.2 (Nat.le_of_dvd hK hdvd)
    have hA : finCoeffNat L (fun n : Fin L => a ((n : ℕ) + 1)) d = a d := by
      rw [finCoeffNat, dif_pos ⟨hdpos, le_trans hdK hrL⟩]
      change a (d - 1 + 1) = a d
      rw [Nat.sub_add_cancel hdpos]
    rw [hA, finCoeffNat_levinsonLinearMollifierFinCoeff_of_pos M hqpos]
  rw [show ((r : ℕ) + 1) = K by rfl, Finset.sum_congr rfl hterm]
  rw [← Nat.sum_divisorsAntidiagonal
      (fun d q => a d * levinsonLinearMollifierCoeff M q)]
  exact Nat.sum_divisorsAntidiagonal'
    (fun d q => a d * levinsonLinearMollifierCoeff M q)

/-- Positive-natural coefficient of the unsmoothed critical detector head. -/
def levinsonCriticalDetectorHeadCoeff (lam : ℝ) (n : ℕ) : ℂ :=
  ((((1 : ℝ) / Real.sqrt n : ℝ) *
      (1 - lam * Real.log n) : ℝ) : ℂ)

/-- The finite critical detector convolution is the exact differentiated
Barban--Vehov coefficient on every product index inside the head. -/
theorem dirConv_levinsonCriticalDetectorHead_eq
    (lam : ℝ) (L M : ℕ) (r : Fin (L * M)) (hrL : (r : ℕ) + 1 ≤ L) :
    dirConv L M
        (fun n : Fin L => levinsonCriticalDetectorHeadCoeff lam ((n : ℕ) + 1))
        (RHTower.levinsonLinearMollifierFinCoeff M) r =
      levinsonLinearMollifiedCriticalDetectorCoeff lam M ((r : ℕ) + 1) := by
  rw [dirConv_natSucc_mul_levinsonLinearMollifier_eq_divisorSum
    (levinsonCriticalDetectorHeadCoeff lam) L M r hrL]
  rfl

end RHTower.Sieve

import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheValuationStepsHaveCompletedPrimeRows
import Mathlib.Data.Nat.Factorization.Induction

/-!
# The completed Ramanujan prime row has torsion-adjunction energy

The exact prime-power generator equations assemble by coprime conductor
multiplication. A Mangoldt atom changes at most one coprime factor, so the
upward and downward corrections both obey the same product rule.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction ArithmeticIntersectionTheory BezoutValuationIncidence

/-- One term of the upward correction of an unnormalized Ramanujan mode. -/
def ramanujanUpCorrectionTerm (m n t : ℕ) : ℝ :=
  (ramanujanLagCoefficient m (n * t) - ramanujanLagCoefficient m n) * Λ t / (t : ℝ)

/-- The exact finite downward divisor correction of a Ramanujan mode. -/
def ramanujanDownCorrection (m n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (ramanujanLagCoefficient m (n / d) - ramanujanLagCoefficient m n) * Λ d

private theorem hasSum_ramanujan_correction_mul {a b n : ℕ}
    (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    (hA : HasSum (ramanujanUpCorrectionTerm a n)
      (-(Real.log a + tameDifferent a) * ramanujanLagCoefficient a n - ramanujanDownCorrection a n))
    (hB : HasSum (ramanujanUpCorrectionTerm b n)
      (-(Real.log b + tameDifferent b) * ramanujanLagCoefficient b n - ramanujanDownCorrection b n)) :
    HasSum (ramanujanUpCorrectionTerm (a * b) n)
      (-(Real.log (a * b : ℕ) + tameDifferent (a * b)) * ramanujanLagCoefficient (a * b) n -
        ramanujanDownCorrection (a * b) n) := by
  have hup (t : ℕ) : ramanujanUpCorrectionTerm (a * b) n t =
      ramanujanLagCoefficient b n * ramanujanUpCorrectionTerm a n t +
        ramanujanLagCoefficient a n * ramanujanUpCorrectionTerm b n t := by
    unfold ramanujanUpCorrectionTerm
    rw [ramanujanCoefficient_up_difference_mul hab]
    ring
  have hdown : ramanujanDownCorrection (a * b) n =
      ramanujanLagCoefficient b n * ramanujanDownCorrection a n +
        ramanujanLagCoefficient a n * ramanujanDownCorrection b n := by
    unfold ramanujanDownCorrection
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun d hd =>
      ramanujanCoefficient_down_difference_mul hab (Nat.dvd_of_mem_divisors hd)
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hsum := (hA.mul_left (ramanujanLagCoefficient b n)).add
    (hB.mul_left (ramanujanLagCoefficient a n))
  have henergy :
      ramanujanLagCoefficient b n *
          (-(Real.log a + tameDifferent a) * ramanujanLagCoefficient a n - ramanujanDownCorrection a n) +
        ramanujanLagCoefficient a n *
          (-(Real.log b + tameDifferent b) * ramanujanLagCoefficient b n - ramanujanDownCorrection b n) =
      -(Real.log (a * b : ℕ) + tameDifferent (a * b)) * ramanujanLagCoefficient (a * b) n -
        ramanujanDownCorrection (a * b) n := by
    rw [Nat.cast_mul, Real.log_mul haR hbR, tameDifferent_mul hab,
      BezoutValuationIncidence.ramanujanLagCoefficient_mul_of_coprime hab, hdown]
    ring
  rw [henergy] at hsum
  exact hsum.congr_fun fun t => hup t

/-- Every positive conductor has its exact completed prime-row energy. No support
restriction is imposed on the row index or its upward multiples. -/
theorem hasSum_ramanujan_correction (m : ℕ) : ∀ (_ : 0 < m) (n : ℕ), 0 < n →
    HasSum (ramanujanUpCorrectionTerm m n)
      (-(Real.log m + tameDifferent m) * ramanujanLagCoefficient m n - ramanujanDownCorrection m n) := by
  induction m using Nat.recOnPrimePow with
  | zero =>
      intro hm
      omega
  | one =>
      intro _ n _
      have hc (t : ℕ) : ramanujanLagCoefficient 1 t = 1 := by
        rw [ramanujanLagCoefficient_eq_totient_mul,
          sieveLagMultiplier_of_dvd one_ne_zero (one_dvd t)]
        norm_num
      change HasSum (fun t : ℕ =>
        (ramanujanLagCoefficient 1 (n * t) - ramanujanLagCoefficient 1 n) * Λ t / (t : ℝ)) _
      simpa only [ramanujanDownCorrection, hc, sub_self,
        zero_mul, zero_div, sum_const_zero, Nat.cast_one, Real.log_one, tameDifferent,
        Nat.primeFactors_one, sum_empty, add_zero, neg_zero, mul_one, sub_zero] using
        (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  | prime_pow_mul a p k hp hpa hk ih =>
      intro hprod n hn
      have ha : 0 < a := by
        apply Nat.pos_of_ne_zero
        intro haz
        simp [haz] at hprod
      have hcop : (p ^ k).Coprime a := (hp.coprime_iff_not_dvd.mpr hpa).pow_left k
      exact hasSum_ramanujan_correction_mul hcop (pow_pos hp.pos k) ha
        (hasSum_ramanujan_primePower_correction hp hk hn) (ih ha n hn)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory


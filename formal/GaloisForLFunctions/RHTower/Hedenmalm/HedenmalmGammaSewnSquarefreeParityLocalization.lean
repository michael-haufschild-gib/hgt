import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGammaSewnWoldThermofieldBridge
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicFockLocal

/-!
# Squarefree parity localization of the Route N modular class

The geometric Wold exponent splits canonically as `k = e + 2j`.  Its first Boolean parity digit
has odds exactly equal to the geometric parameter.  Applied to the two Route N critical channel
masses, the ratio of parity odds is therefore the transverse modular cocycle, while their signed
odds displacement is exactly the Route N Krein charge.

The residual paired-depth odds carry the square of the cocycle but their critical/twisted
difference is summable for every grade.  Hence the nonsummable all-prime modular class is supported
entirely on the source-canonical squarefree parity digit; the higher dyadic Wold tower is a regular
correction.  This localizes the remaining exceptional-Cartier producer to the squarefree singular
source channel.
-/

namespace RHTower

noncomputable section

/-- Odds of the source-canonical squarefree parity digit. -/
def dyadicSquarefreeParityOdds (q : ℝ) : ℝ :=
  dyadicSquarefreeParityProbability q (1 : Fin 2) /
    dyadicSquarefreeParityProbability q (0 : Fin 2)

/-- Parity odds recover the complete geometric parameter. -/
theorem dyadicSquarefreeParityOdds_eq
    {q : ℝ} (hq : 0 ≤ q) :
    dyadicSquarefreeParityOdds q = q := by
  have hplus : 1 + q ≠ 0 := by linarith
  unfold dyadicSquarefreeParityOdds dyadicSquarefreeParityProbability
  simp only [Fin.val_one, Fin.val_zero, pow_one, pow_zero]
  field_simp [hplus]

/-- Critical squarefree parity odds are the universal Route N channel mass. -/
def routeNGammaSewnCriticalSquarefreeParityOdds (p : Nat.Primes) : ℝ :=
  dyadicSquarefreeParityOdds
    (routeNGammaSewnUniversalCriticalChannelMass p)

/-- Twisted squarefree parity odds are the twisted Route N channel mass. -/
def routeNGammaSewnTwistedSquarefreeParityOdds
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  dyadicSquarefreeParityOdds
    (routeNGammaSewnTwistedCriticalChannelMass t p)

theorem routeNGammaSewnCriticalSquarefreeParityOdds_eq
    (p : Nat.Primes) :
    routeNGammaSewnCriticalSquarefreeParityOdds p =
      routeNGammaSewnUniversalCriticalChannelMass p := by
  rw [routeNGammaSewnCriticalSquarefreeParityOdds,
    dyadicSquarefreeParityOdds_eq]
  exact (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _).le

theorem routeNGammaSewnTwistedSquarefreeParityOdds_eq
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnTwistedSquarefreeParityOdds t p =
      routeNGammaSewnTwistedCriticalChannelMass t p := by
  rw [routeNGammaSewnTwistedSquarefreeParityOdds,
    dyadicSquarefreeParityOdds_eq]
  exact (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _).le

/-- The complete transverse modular cocycle is the twisted-to-critical squarefree parity odds
ratio. -/
theorem routeNGammaSewnSquarefreeParityOdds_ratio_eq_modularCocycle
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnTwistedSquarefreeParityOdds t p /
        routeNGammaSewnCriticalSquarefreeParityOdds p =
      routeNGammaSewnTransverseModularCocycle t p := by
  rw [routeNGammaSewnTwistedSquarefreeParityOdds_eq,
    routeNGammaSewnCriticalSquarefreeParityOdds_eq,
    routeNGammaSewnTwisted_div_universal_eq_modularCocycle]

/-- Stronger oriented statement: squarefree parity odds displacement is exactly the signed Route N
Krein charge. -/
theorem routeNGammaSewnSquarefreeParityOdds_sub_eq_sign_mul_routeNKrein
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnTwistedSquarefreeParityOdds t p -
        routeNGammaSewnCriticalSquarefreeParityOdds p =
      Real.sign t * routeNGammaSewnCriticalHorizonKreinCharge t p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hmassPrime :
      routeNGammaSewnUniversalCriticalChannelMass p * (p : ℝ) = 1 := by
    rw [routeNGammaSewnUniversalCriticalChannelMass, Real.rpow_neg_one]
    exact inv_mul_cancel₀ hp0.ne'
  have hmodular := one_add_sign_mul_prime_mul_routeNKrein_eq_modularCocycle t p
  have hmass :=
    routeNGammaSewnTwistedCriticalChannelMass_eq_universal_mul_modularCocycle t p
  rw [routeNGammaSewnTwistedSquarefreeParityOdds_eq,
    routeNGammaSewnCriticalSquarefreeParityOdds_eq, hmass]
  calc
    routeNGammaSewnUniversalCriticalChannelMass p *
          routeNGammaSewnTransverseModularCocycle t p -
        routeNGammaSewnUniversalCriticalChannelMass p =
      routeNGammaSewnUniversalCriticalChannelMass p *
        (routeNGammaSewnTransverseModularCocycle t p - 1) := by ring
    _ = routeNGammaSewnUniversalCriticalChannelMass p *
        (Real.sign t * (p : ℝ) *
          routeNGammaSewnCriticalHorizonKreinCharge t p) := by
      congr 1
      linarith
    _ = Real.sign t *
        routeNGammaSewnCriticalHorizonKreinCharge t p := by
      rw [show routeNGammaSewnUniversalCriticalChannelMass p *
          (Real.sign t * (p : ℝ) *
            routeNGammaSewnCriticalHorizonKreinCharge t p) =
          Real.sign t *
            (routeNGammaSewnUniversalCriticalChannelMass p * (p : ℝ)) *
              routeNGammaSewnCriticalHorizonKreinCharge t p by ring,
        hmassPrime, mul_one]

/-- Paired-depth residual odds carry the square of the parity modular cocycle. -/
theorem routeNGammaSewnResidualOdds_ratio_eq_modularCocycle_sq
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnTwistedCriticalChannelMass t p ^ 2 /
        routeNGammaSewnUniversalCriticalChannelMass p ^ 2 =
      routeNGammaSewnTransverseModularCocycle t p ^ 2 := by
  rw [← div_pow,
    routeNGammaSewnTwisted_div_universal_eq_modularCocycle]

/-- Higher paired-depth correction is summable at every grade.  Thus it vanishes in the fixed
all-prime quotient where the parity/Krein class survives. -/
theorem summable_routeNGammaSewnResidualOddsDifference (t : ℝ) :
    Summable (fun p : Nat.Primes =>
      routeNGammaSewnTwistedCriticalChannelMass t p ^ 2 -
        routeNGammaSewnUniversalCriticalChannelMass p ^ 2) := by
  have htwisted : Summable (fun p : Nat.Primes =>
      routeNGammaSewnTwistedCriticalChannelMass t p ^ 2) := by
    have hs : Summable (fun p : Nat.Primes =>
        (p : ℝ) ^ (-2 - 4 * |t|)) :=
      (Nat.Primes.summable_rpow).2 (by linarith [abs_nonneg t])
    convert hs using 1
    funext p
    have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
    rw [routeNGammaSewnTwistedCriticalChannelMass, pow_two,
      ← Real.rpow_add hp0]
    congr 1
    ring
  have hcritical : Summable (fun p : Nat.Primes =>
      routeNGammaSewnUniversalCriticalChannelMass p ^ 2) := by
    have hs : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 : ℝ)) :=
      (Nat.Primes.summable_rpow).2 (by norm_num)
    convert hs using 1
    funext p
    have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
    rw [routeNGammaSewnUniversalCriticalChannelMass, pow_two,
      ← Real.rpow_add hp0]
    congr 1
    ring
  exact htwisted.sub hcritical

/-- The singular squarefree parity displacement is summable exactly at neutral grade. -/
theorem summable_routeNGammaSewnSquarefreeParityOddsDifference_iff (t : ℝ) :
    Summable (fun p : Nat.Primes =>
      routeNGammaSewnTwistedSquarefreeParityOdds t p -
        routeNGammaSewnCriticalSquarefreeParityOdds p) ↔
      t = 0 := by
  have hrealKrein :
      Summable (fun p : Nat.Primes =>
        routeNGammaSewnCriticalHorizonKreinCharge t p) ↔ t = 0 := by
    rw [← summable_routeNGammaSewnCriticalHorizonKreinPrimeSequence_iff t]
    exact Complex.summable_ofReal.symm
  rw [show (fun p : Nat.Primes =>
      routeNGammaSewnTwistedSquarefreeParityOdds t p -
        routeNGammaSewnCriticalSquarefreeParityOdds p) =
      fun p => Real.sign t *
        routeNGammaSewnCriticalHorizonKreinCharge t p by
      funext p
      exact routeNGammaSewnSquarefreeParityOdds_sub_eq_sign_mul_routeNKrein t p]
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [Real.sign_of_neg ht]
    simpa only [neg_mul, one_mul, summable_neg_iff] using hrealKrein
  · simp
  · rw [Real.sign_of_pos ht]
    rw [show (fun p : Nat.Primes =>
        1 * routeNGammaSewnCriticalHorizonKreinCharge t p) =
      fun p => routeNGammaSewnCriticalHorizonKreinCharge t p by
        funext p
        rw [one_mul]]
    exact hrealKrein

end

end RHTower

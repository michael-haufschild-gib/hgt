import GaloisForLFunctions.RHTower.Sieve.NonRoughRamareBilinear
import GaloisForLFunctions.RHTower.Sieve.RamarePhaseBilinear

/-!
# The non-rough polynomial factors with only the square-multiple diagonal as error

`Sieve/RamarePhaseBilinear.norm_logPoly_moebius_sub_ramare_bilinear_le` factors the full Möbius
polynomial and pays two errors: the cofactors still divisible by the designated prime, and the rough
integers.  For the non-rough polynomial the second error is absent by construction — the rough
indices carry the coefficient `0` — so only the square-multiple diagonal remains.

That matters because the rough term has already been paid once, per fibre and squared, in
`Sieve/FibreNonRoughSpectral`; paying it again here at the polynomial level would reinstate exactly
the linear loss the Ramaré route exists to avoid.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- **The non-rough Möbius polynomial is a bilinear form up to the square-multiple diagonal.** -/
theorem norm_logPoly_nonRoughMoebius_sub_ramare_bilinear_le {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (s : Finset ℕ) (w : ℝ) :
    ‖logPoly (fun n => ((nonRoughMoebius P n : ℝ) : ℂ)) s w
        - ∑ p ∈ P, moebiusPhase w p
            * logPoly (ramareCofactorCoeff P) {m ∈ ramareCofactorSet s p | ¬ p ∣ m} w‖
      ≤ ∑ p ∈ P, (({m ∈ ramareCofactorSet s p | p ∣ m}).card : ℝ) := by
  classical
  have hmul := moebiusPhase_mul_of_coprime w
  have hg := norm_moebiusPhase_le_one w
  -- the non-rough polynomial as the Ramaré inner sum
  have hphase : ∀ n : ℕ, ((moebius n : ℤ) : ℂ)
      * Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I)
      = moebiusPhase w n := by
    intro n
    rw [moebiusPhase, unitLogPhase]
  have hlhs : logPoly (fun n => ((nonRoughMoebius P n : ℝ) : ℂ)) s w
      = ∑ p ∈ P, ∑ n ∈ {n ∈ s | p ∣ n},
          moebiusPhase w n / ((primeFactorsIn P n).card : ℂ) := by
    rw [logPoly_nonRoughMoebius_eq_ramare]
    refine Finset.sum_congr rfl fun p _ => ?_
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hphase]
  -- reindex each inner sum by the cofactor
  have hinner : ∀ p ∈ P,
      ∑ n ∈ {n ∈ s | p ∣ n}, moebiusPhase w n / ((primeFactorsIn P n).card : ℂ)
        = ∑ m ∈ ramareCofactorSet s p,
            moebiusPhase w (p * m) / ((primeFactorsIn P (p * m)).card : ℂ) :=
    fun p _ => (sum_div_image_complex p {n ∈ s | p ∣ n}
      (fun n hn => (Finset.mem_filter.1 hn).2)
      (fun n => moebiusPhase w n / ((primeFactorsIn P n).card : ℂ))).symm
  rw [hlhs, Finset.sum_congr rfl hinner]
  -- split each cofactor sum into the bilinear part and the diagonal
  have hsplit : ∀ p ∈ P,
      ∑ m ∈ ramareCofactorSet s p,
          moebiusPhase w (p * m) / ((primeFactorsIn P (p * m)).card : ℂ)
        - moebiusPhase w p
            * logPoly (ramareCofactorCoeff P)
                {m ∈ ramareCofactorSet s p | ¬ p ∣ m} w
        = ∑ m ∈ {m ∈ ramareCofactorSet s p | p ∣ m},
            moebiusPhase w (p * m) / ((primeFactorsIn P (p * m)).card : ℂ) := by
    intro p hp
    have hpprime : p.Prime := hPprime p hp
    rw [sum_ramare_bilinear_split_complex hPprime hmul hpprime hp (ramareCofactorSet s p),
      sum_moebiusPhase_div_eq_logPoly]
    ring
  have hdiff : (∑ p ∈ P, ∑ m ∈ ramareCofactorSet s p,
          moebiusPhase w (p * m) / ((primeFactorsIn P (p * m)).card : ℂ))
        - ∑ p ∈ P, moebiusPhase w p
            * logPoly (ramareCofactorCoeff P)
                {m ∈ ramareCofactorSet s p | ¬ p ∣ m} w
      = ∑ p ∈ P, ∑ m ∈ {m ∈ ramareCofactorSet s p | p ∣ m},
          moebiusPhase w (p * m) / ((primeFactorsIn P (p * m)).card : ℂ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hsplit
  rw [hdiff]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun p hp => ?_
  exact norm_ramare_remainder_le_complex hg hp (ramareCofactorSet s p)

end

end RHTower.Sieve

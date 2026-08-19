import GaloisForLFunctions.RHTower.Sieve.NonRoughBilinearFactor
import GaloisForLFunctions.RHTower.Sieve.OmegaWeightedFactorisation

/-!
# The non-rough polynomial factors exactly

The square-multiple diagonal of the Ramaré factorisation does not merely admit a bound: it vanishes.
If the designated prime divides the cofactor then the index is divisible by the square of a prime,
so its Möbius phase is zero.  Together with the absence of a rough term for the non-rough
polynomial, the factorisation into designated prime times cofactor is therefore an **identity**.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- **The non-rough Möbius polynomial is exactly a bilinear form.**  No rough term, no diagonal. -/
theorem logPoly_nonRoughMoebius_eq_ramare_bilinear {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (s : Finset ℕ) (w : ℝ) :
    logPoly (fun n => ((nonRoughMoebius P n : ℝ) : ℂ)) s w
      = ∑ p ∈ P, moebiusPhase w p
          * logPoly (ramareCofactorCoeff P) {m ∈ ramareCofactorSet s p | ¬ p ∣ m} w := by
  classical
  have hmul := moebiusPhase_mul_of_coprime w
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
  have hinner : ∀ p ∈ P,
      ∑ n ∈ {n ∈ s | p ∣ n}, moebiusPhase w n / ((primeFactorsIn P n).card : ℂ)
        = ∑ m ∈ ramareCofactorSet s p,
            moebiusPhase w (p * m) / ((primeFactorsIn P (p * m)).card : ℂ) :=
    fun p _ => (sum_div_image_complex p {n ∈ s | p ∣ n}
      (fun n hn => (Finset.mem_filter.1 hn).2)
      (fun n => moebiusPhase w n / ((primeFactorsIn P n).card : ℂ))).symm
  rw [hlhs, Finset.sum_congr rfl hinner]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpprime : p.Prime := hPprime p hp
  have hdiag : ∑ m ∈ {m ∈ ramareCofactorSet s p | p ∣ m},
      moebiusPhase w (p * m) / ((primeFactorsIn P (p * m)).card : ℂ) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    have hpm : p ∣ m := (Finset.mem_filter.1 hm).2
    rw [moebiusPhase_eq_zero_of_dvd hpprime hpm, zero_div]
  rw [sum_ramare_bilinear_split_complex hPprime hmul hpprime hp (ramareCofactorSet s p),
    hdiag, add_zero, sum_moebiusPhase_div_eq_logPoly]

end

end RHTower.Sieve

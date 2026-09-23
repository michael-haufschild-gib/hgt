import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicShellRoughMeanSquare

/-!
# Splitting a shell at a prime cutoff, with the rough half already paid

The exact harmonic Ramare factorisation is general in the designated prime set
(`logPoly_harmonicMoebius_eq_ramare_add_rough` needs only that the set consists of primes).  Taking
the set to be **all** primes up to a cutoff `z` makes its rough remainder exactly
`menonShellRough`, which the previous file bounds by Brun's pure sieve at `≍ 1/log z` — with no
factorisation estimate.

So the shell splits into a bilinear part whose every ladder block has prime scale at most `z` —
the regime where the cofactors are long and every receiver of this session applies cleanly — plus
a remainder that is already closed.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The Ramare rough remainder of the full cutoff prime set is the shell's rough part. -/
theorem ramareRough_primesLE_eq_menonShellRough (A B z : ℕ) :
    {n ∈ Finset.Icc A B | primeFactorsIn (Nat.primesLE z) n = ∅}
      = menonShellRough A B z := by
  classical
  rw [menonShellRough]
  refine Finset.filter_congr fun n _ => ?_
  constructor
  · intro h p hp hdvd
    have : p ∈ primeFactorsIn (Nat.primesLE z) n := mem_primeFactorsIn.2 ⟨hp, hdvd⟩
    rw [h] at this
    exact absurd this (Finset.notMem_empty p)
  · intro h
    refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
    have hp' := mem_primeFactorsIn.1 hp
    exact h p hp'.1 hp'.2

/-- **The shell split at a prime cutoff.** -/
theorem integral_Icc_normSq_shell_le_bilinear_add_rough
    {A B z : ℕ} {T : ℝ} (_hT : 0 ≤ T) :
    (∫ w in Set.Icc (-T) T, ‖logPoly harmonicMoebiusC (Finset.Icc A B) w‖ ^ (2 : ℕ))
      ≤ 2 * (∫ w in Set.Icc (-T) T,
            ‖harmonicRamareBilinear (Nat.primesLE z) (Finset.Icc A B) w‖ ^ (2 : ℕ))
        + 2 * ∫ w in Set.Icc (-T) T,
            ‖logPoly harmonicMoebiusC (menonShellRough A B z) w‖ ^ (2 : ℕ) := by
  classical
  have hsplit := setIntegral_normSq_add_le
    (F := fun w => harmonicRamareBilinear (Nat.primesLE z) (Finset.Icc A B) w)
    (G := fun w => logPoly harmonicMoebiusC (menonShellRough A B z) w)
    (E := Set.Icc (-T) T) (W := T)
    (by
      refine continuous_finsetSum _ fun p _ => ?_
      exact ((continuous_moebiusPhase p).div_const _).mul (continuous_logPoly _ _))
    (continuous_logPoly _ _)
    measurableSet_Icc (le_refl _)
  have hid : ∀ w : ℝ,
      logPoly harmonicMoebiusC (Finset.Icc A B) w
        = harmonicRamareBilinear (Nat.primesLE z) (Finset.Icc A B) w
          + logPoly harmonicMoebiusC (menonShellRough A B z) w := by
    intro w
    rw [← ramareRough_primesLE_eq_menonShellRough]
    exact logPoly_harmonicMoebius_eq_ramare_add_rough
      (fun p hp => Nat.prime_of_mem_primesLE hp) (Finset.Icc A B) w
  simpa only [hid] using hsplit

/-- **The shell split at a prime cutoff, rough half paid by Brun's pure sieve.** -/
theorem integral_Icc_normSq_shell_le_bilinear_add_brun
    {A B z r : ℕ} (hA : 1 ≤ A) (hz : 2 ≤ z) (hAB : A - 1 ≤ B) (hr : Even r)
    {lam : ℝ} (hlam : 1 ≤ lam) {T : ℝ} (hT : 0 ≤ T) :
    (∫ w in Set.Icc (-T) T, ‖logPoly harmonicMoebiusC (Finset.Icc A B) w‖ ^ (2 : ℕ))
      ≤ 2 * (∫ w in Set.Icc (-T) T,
            ‖harmonicRamareBilinear (Nat.primesLE z) (Finset.Icc A B) w‖ ^ (2 : ℕ))
        + 2 * ((5 * Real.pi / 2) *
                (((((B : ℝ) - ((A - 1 : ℕ) : ℝ))
                      * (Real.exp mertensSecondLowerConst / Real.log z)
                    + ((B : ℝ) - ((A - 1 : ℕ) : ℝ))
                        * (Real.exp (lam * mertensSecondUpperConst)
                            * (Real.log z) ^ lam / lam ^ r)
                    + ((truncDivisors (primorial z) r).card : ℝ))) / (A : ℝ) ^ (2 : ℕ)) * T
            + ((5 * Real.exp 1 / 2) *
                  (((((B : ℝ) - ((A - 1 : ℕ) : ℝ))
                        * (Real.exp mertensSecondLowerConst / Real.log z)
                      + ((B : ℝ) - ((A - 1 : ℕ) : ℝ))
                          * (Real.exp (lam * mertensSecondUpperConst)
                              * (Real.log z) ^ lam / lam ^ r)
                      + ((truncDivisors (primorial z) r).card : ℝ))) / (A : ℝ))
              + (5 / 4) *
                  (((((B : ℝ) - ((A - 1 : ℕ) : ℝ))
                        * (Real.exp mertensSecondLowerConst / Real.log z)
                      + ((B : ℝ) - ((A - 1 : ℕ) : ℝ))
                          * (Real.exp (lam * mertensSecondUpperConst)
                              * (Real.log z) ^ lam / lam ^ r)
                      + ((truncDivisors (primorial z) r).card : ℝ))) / (A : ℝ) ^ (2 : ℕ)))) := by
  have hbase := integral_Icc_normSq_shell_le_bilinear_add_rough (A := A) (B := B) (z := z) hT
  have hrough := integral_Icc_normSq_menonShellRough_le_brun hA hz hAB hr hlam hT
  have htwice := mul_le_mul_of_nonneg_left hrough (show (0 : ℝ) ≤ 2 by norm_num)
  exact hbase.trans (add_le_add le_rfl htwice)

end

end RHTower.Sieve

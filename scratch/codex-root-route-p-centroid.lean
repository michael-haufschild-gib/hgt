import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePTerminalCoefficientChebyshevCofinal

open scoped BigOperators Chebyshev
open ArithmeticFunction

namespace RHTower

private noncomputable def centroidAtomExcess (n : ℕ) : ℝ :=
  criticalMellinAtomWeight n *
    (ccmActualHeadMatchedPolarCentroid n - 2 * Real.sqrt (n : ℝ))

private theorem centroidAtomExcess_nonneg {n : ℕ} (hn : 0 < n) :
    0 ≤ centroidAtomExcess n := by
  unfold centroidAtomExcess
  have hw : 0 ≤ criticalMellinAtomWeight n :=
    criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n
  have hc : 0 < ccmActualHeadMatchedPolarCentroid n :=
    ccmActualHeadMatchedPolarCentroid_pos n
  have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsq := ccmActualHeadMatchedPolarCentroid_sq n hn
  have hroot : Real.sqrt (n : ℝ) ^ (2 : ℕ) = (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  apply mul_nonneg hw
  nlinarith [sq_nonneg (criticalMellinAtomWeight n)]

private theorem centroidAtomExcess_le_cube {n : ℕ} (hn : 0 < n) :
    centroidAtomExcess n ≤
      criticalMellinAtomWeight n ^ (3 : ℕ) /
        (16 * Real.sqrt (n : ℝ)) := by
  let w := criticalMellinAtomWeight n
  let c := ccmActualHeadMatchedPolarCentroid n
  let r := Real.sqrt (n : ℝ)
  have hw : 0 ≤ w := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n
  have hc : 0 < c := ccmActualHeadMatchedPolarCentroid_pos n
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hsq : c ^ (2 : ℕ) = 4 * (n : ℝ) + w ^ (2 : ℕ) / 4 :=
    ccmActualHeadMatchedPolarCentroid_sq n hn
  have hroot : r ^ (2 : ℕ) = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hcr : 2 * r ≤ c := by nlinarith [sq_nonneg w]
  have hfactor : (c - 2 * r) * (c + 2 * r) = w ^ (2 : ℕ) / 4 := by
    nlinarith only [hsq, hroot]
  have hbound : 16 * r * (w * (c - 2 * r)) ≤ w ^ (3 : ℕ) := by
    have hprod := mul_le_mul_of_nonneg_left
      (show 4 * r ≤ c + 2 * r by linarith)
      (mul_nonneg hw (sub_nonneg.mpr hcr))
    have hfactorw := congrArg (fun x : ℝ => w * x) hfactor
    nlinarith only [hprod, hfactorw]
  unfold centroidAtomExcess
  dsimp only [w, c, r] at *
  apply (le_div_iff₀ (by positivity : 0 < 16 * Real.sqrt (n : ℝ))).mpr
  nlinarith only [hbound]

private theorem centroidAtomExcess_le_logMajorant (n : ℕ) :
    centroidAtomExcess n ≤
      (Real.log (n : ℝ)) ^ (3 : ℕ) / (16 * (n : ℝ) ^ (2 : ℕ)) := by
  by_cases hn : n = 0
  · subst n
    simp [centroidAtomExcess, criticalMellinAtomWeight]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  trace "A"
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
  have hroot : Real.sqrt (n : ℝ) ^ (4 : ℕ) = (n : ℝ) ^ (2 : ℕ) := by
    calc
      Real.sqrt (n : ℝ) ^ (4 : ℕ) =
          (Real.sqrt (n : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = (n : ℝ) ^ (2 : ℕ) := by
        rw [Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)]
  trace "B"
  have hv : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log
  have hv0 : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hcub : ArithmeticFunction.vonMangoldt n ^ (3 : ℕ) ≤
      Real.log (n : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ hv0 hv 3
  trace "C"
  calc
    centroidAtomExcess n ≤
        criticalMellinAtomWeight n ^ (3 : ℕ) /
          (16 * Real.sqrt (n : ℝ)) := centroidAtomExcess_le_cube hnpos
    _ = ArithmeticFunction.vonMangoldt n ^ (3 : ℕ) /
          (16 * (n : ℝ) ^ (2 : ℕ)) := by
      rw [criticalMellinAtomWeight_eq_div_sqrt, ← hroot]
      field_simp [hr.ne']
    _ ≤ _ := div_le_div_of_nonneg_right hcub (by positivity)
  trace "D"

/-
private theorem summable_centroidAtomExcess : Summable centroidAtomExcess := by
  have hbase : Summable (fun n : ℕ =>
      (Real.log (n : ℝ)) ^ (3 : ℕ) / (16 * (n : ℝ) ^ (2 : ℕ))) := by
    have h := summable_abs_log_natCast_pow_mul_rpow_neg 3 2 (by norm_num)
    convert h.mul_left (1 / 16 : ℝ) using 1
    ext n
    simp only [Real.rpow_neg, Real.rpow_natCast]
    ring
  apply hbase.of_nonneg_of_le
  · intro n
    by_cases hn : n = 0
    · subst n; simp [centroidAtomExcess]
    · exact centroidAtomExcess_nonneg (Nat.pos_of_ne_zero hn)
  · exact centroidAtomExcess_le_logMajorant
-/

end RHTower

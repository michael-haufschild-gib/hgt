import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePTerminalCoefficientChebyshevCofinal
import GaloisForLFunctions.RHTower.ZetaFisherVariance

/-!
# Summable matched-centroid excess at the Route P unit boundary

The literal matched-cell centroid exceeds twice its arithmetic square-root by
an atom-width correction of order Λ(n)^3/n². Its total mass is finite. Thus
the geometric excess in the exact unit-scale terminal barrier converges;
only the signed Chebyshev-error and critical-mass mismatch remain scale-bearing.
-/

open scoped BigOperators Chebyshev
open ArithmeticFunction
open Filter Topology

namespace RHTower

noncomputable def centroidAtomExcess (n : ℕ) : ℝ :=
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
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
  have hroot : Real.sqrt (n : ℝ) ^ (4 : ℕ) = (n : ℝ) ^ (2 : ℕ) := by
    calc
      Real.sqrt (n : ℝ) ^ (4 : ℕ) =
          (Real.sqrt (n : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = (n : ℝ) ^ (2 : ℕ) := by
        rw [Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)]
  have hv : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log
  have hv0 : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hcub : ArithmeticFunction.vonMangoldt n ^ (3 : ℕ) ≤
      Real.log (n : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ hv0 hv 3
  calc
    centroidAtomExcess n ≤
        criticalMellinAtomWeight n ^ (3 : ℕ) /
          (16 * Real.sqrt (n : ℝ)) := centroidAtomExcess_le_cube hnpos
    _ = ArithmeticFunction.vonMangoldt n ^ (3 : ℕ) /
          (16 * (n : ℝ) ^ (2 : ℕ)) := by
      rw [criticalMellinAtomWeight_eq_div_sqrt, ← hroot]
      field_simp [hr.ne']
    _ ≤ _ := div_le_div_of_nonneg_right hcub (by positivity)

private theorem summable_centroidAtomExcess : Summable centroidAtomExcess := by
  have hbase : Summable (fun n : ℕ =>
      (Real.log (n : ℝ)) ^ (3 : ℕ) / (16 * (n : ℝ) ^ (2 : ℕ))) := by
    have h := summable_log_natCast_pow_mul_rpow_neg 3 (show (1 : ℝ) < 2 by norm_num)
    refine (h.mul_left (1 / 16 : ℝ)).congr (fun n => ?_)
    rw [Real.rpow_neg_eq_inv_rpow]
    rw [Real.rpow_ofNat]
    rw [inv_pow]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  apply hbase.of_nonneg_of_le
  · intro n
    by_cases hn : n = 0
    · subst n
      have hz : criticalMellinAtomWeight 0 = 0 := by
        simp [criticalMellinAtomWeight]
      simp [centroidAtomExcess, hz]
    · exact centroidAtomExcess_nonneg (Nat.pos_of_ne_zero hn)
  · exact centroidAtomExcess_le_logMajorant

theorem centroidAtomExcess_nonneg_all (n : ℕ) :
    0 ≤ centroidAtomExcess n := by
  by_cases hn : n = 0
  · subst n
    have hz : criticalMellinAtomWeight 0 = 0 := by
      simp [criticalMellinAtomWeight]
    simp [centroidAtomExcess, hz]
  · exact centroidAtomExcess_nonneg (Nat.pos_of_ne_zero hn)

private theorem centroidAtomExcess_zero : centroidAtomExcess 0 = 0 := by
  have hz : criticalMellinAtomWeight 0 = 0 := by
    simp [criticalMellinAtomWeight]
  simp [centroidAtomExcess, hz]

private theorem centroidAtomExcess_one : centroidAtomExcess 1 = 0 := by
  have hz : criticalMellinAtomWeight 1 = 0 := by
    simp [criticalMellinAtomWeight]
  simp [centroidAtomExcess, hz]

private theorem centroidAtomExcess_sum_range_shift_two (K : ℕ) :
    (∑ n ∈ Finset.range (K + 3), centroidAtomExcess n) =
      ∑ n ∈ Finset.range (K + 1), centroidAtomExcess (n + 2) := by
  induction K with
  | zero => simp [Finset.sum_range_succ, centroidAtomExcess_zero,
      centroidAtomExcess_one]
  | succ K ih =>
      simpa [Finset.sum_range_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        congrArg (fun x : ℝ => x + centroidAtomExcess (K + 3)) ih

theorem centroid_sum_range_shift_two (F : ℕ → ℝ)
    (hzero : F 0 = 0) (hone : F 1 = 0) (K : ℕ) :
    (∑ n ∈ Finset.range (K + 3), F n) =
      ∑ n ∈ Finset.range (K + 1), F (n + 2) := by
  induction K with
  | zero => simp [Finset.sum_range_succ, hzero, hone]
  | succ K ih =>
      simpa [Finset.sum_range_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        congrArg (fun x : ℝ => x + F (K + 3)) ih

theorem centroidAtomExcess_vonMangoldt_shift_two (K : ℕ) :
    (∑ n ∈ Finset.range (K + 1), ArithmeticFunction.vonMangoldt (n + 2)) =
      Chebyshev.psi ((K + 2 : ℕ) : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have hIcc : Finset.Icc 0 (K + 2) = Finset.range (K + 3) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hIcc]
  have hzero : ArithmeticFunction.vonMangoldt 0 = 0 := by simp
  have hone : ArithmeticFunction.vonMangoldt 1 = 0 := by simp
  exact (centroid_sum_range_shift_two ArithmeticFunction.vonMangoldt
    hzero hone K).symm

theorem centroidAtomExcess_weight_mul_sqrt {n : ℕ} (hn : 0 < n) :
    criticalMellinAtomWeight n * Real.sqrt (n : ℝ) =
      ArithmeticFunction.vonMangoldt n := by
  rw [criticalMellinAtomWeight_eq_div_sqrt]
  exact div_mul_cancel₀ _ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn))

theorem ccmActualHeadMatchedCentroidChebyshevExcess_eq_atomPrefix (K : ℕ) :
    ccmActualHeadMatchedCentroidChebyshevExcess K =
      ∑ n ∈ Finset.range (K + 3), centroidAtomExcess n := by
  rw [centroidAtomExcess_sum_range_shift_two]
  unfold ccmActualHeadMatchedCentroidChebyshevExcess
  rw [← centroidAtomExcess_vonMangoldt_shift_two K, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← centroidAtomExcess_weight_mul_sqrt (show 0 < n + 2 by omega)]
  unfold centroidAtomExcess
  ring

theorem ccmActualHeadMatchedCentroidChebyshevExcess_le_tsum (K : ℕ) :
    ccmActualHeadMatchedCentroidChebyshevExcess K ≤
      ∑' n : ℕ, centroidAtomExcess n := by
  rw [ccmActualHeadMatchedCentroidChebyshevExcess_eq_atomPrefix]
  exact summable_centroidAtomExcess.sum_le_tsum (Finset.range (K + 3))
    (fun n _ => centroidAtomExcess_nonneg_all n)

theorem ccmActualHeadMatchedCentroidChebyshevExcess_tendsto :
    Tendsto ccmActualHeadMatchedCentroidChebyshevExcess atTop
      (nhds (∑' n : ℕ, centroidAtomExcess n)) := by
  have hsum := summable_centroidAtomExcess.hasSum.tendsto_sum_nat
  have hcomp := hsum.comp (tendsto_add_atTop_nat 3)
  exact hcomp.congr' (Eventually.of_forall fun K =>
    (ccmActualHeadMatchedCentroidChebyshevExcess_eq_atomPrefix K).symm)

end RHTower

import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheMollifiedDetectorHasTheThreeMomentIdentity
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheDetectorTaperTermsAreSmall
import GaloisForLFunctions.RHTower.LevinsonShiftedLinearMollifier

/-!
# Taper error for the literal linear Levinson mollifier

The entire coefficients on the displaced line are bounded by `n^(-d)`.
The logarithmic correction has the same bound when `λ log N ≤ 1`.
Consequently both edge terms in the exact detector identity are sublinear.
-/

open Complex Filter MeasureTheory Set Topology
open RHTower RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Real coefficients of the shifted entire linear mollifier. -/
def linearDetectorWeights (N : ℕ) (d : ℝ) (n : ℕ) : ℝ :=
  (levinsonShiftedLinearMollifierCoeff N (1 / 2 - d) n).re

theorem coe_linearDetectorWeights (N : ℕ) (d : ℝ) (n : ℕ) :
    (linearDetectorWeights N d n : ℂ) =
      levinsonShiftedLinearMollifierCoeff N (1 / 2 - d) n := by
  unfold linearDetectorWeights levinsonShiftedLinearMollifierCoeff Sieve.levinsonLinearMollifierCoeff
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.ofReal_mul]

/-- Critical-line normalization cancels precisely the real displacement. -/
theorem abs_linearDetectorWeights_le {N : ℕ} (hN : 1 < N) (d : ℝ) {n : ℕ}
    (hn : 1 ≤ n) : |linearDetectorWeights N d n| ≤ (n : ℝ) ^ (-d) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.norm_eq_abs, ← Complex.norm_real, coe_linearDetectorWeights,
    levinsonShiftedLinearMollifierCoeff, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  calc
    _ ≤ (n : ℝ) ^ (1 / 2 - d) * (1 / Real.sqrt n) :=
      mul_le_mul_of_nonneg_left (Sieve.norm_levinsonLinearMollifierCoeff_le hN)
        (Real.rpow_nonneg hn0.le _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]
      congr 1
      ring

/-- The real-coefficient polynomial is the existing critical-line-normalized mollifier. -/
theorem edPoly_linearDetectorWeights (N : ℕ) (d t : ℝ) :
    edPoly (fun n => (linearDetectorWeights N d n : ℂ)) (Finset.Icc 1 N)
      (displacedLinePt d t) = Sieve.levinsonLinearMollifier N t := by
  simp_rw [coe_linearDetectorWeights]
  exact edPoly_levinsonShiftedLinearMollifierCoeff_line N (1 / 2 - d) t

/-- Multiplying by `-λ log n` preserves the coefficient envelope below its unit scale. -/
theorem abs_detectorCorrectionWeights_le {N : ℕ} {w : ℕ → ℝ} {lam d : ℝ}
    (hlam : 0 ≤ lam) (hlog : lam * Real.log N ≤ 1)
    (hw : ∀ n ∈ Finset.Icc 1 N, |w n| ≤ (n : ℝ) ^ (-d)) :
    ∀ n ∈ Finset.Icc 1 N,
      |detectorCorrectionWeights lam w n| ≤ (n : ℝ) ^ (-d) := by
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hnlog := Real.log_nonneg hn1
  have hfactor : lam * Real.log n ≤ 1 :=
    (mul_le_mul_of_nonneg_left (Real.log_le_log hn0 hnN) hlam).trans hlog
  unfold detectorCorrectionWeights
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hlam, abs_of_nonneg hnlog]
  exact (mul_le_mul_of_nonneg_left (hw n hn) (mul_nonneg hlam hnlog)).trans
    (mul_le_of_le_one_left (Real.rpow_nonneg hn0.le _) hfactor)

/-- The residual coefficients need only the fixed normalization factor two. -/
theorem abs_half_detectorResidualWeights_le {N : ℕ} {w : ℕ → ℝ} {lam d : ℝ}
    (hlam : 0 ≤ lam) (hlog : lam * Real.log N ≤ 1)
    (hw : ∀ n ∈ Finset.Icc 1 N, |w n| ≤ (n : ℝ) ^ (-d)) :
    ∀ n ∈ Finset.Icc 1 N,
      |detectorResidualWeights lam w n / 2| ≤ (n : ℝ) ^ (-d) := by
  intro n hn
  have hc := abs_detectorCorrectionWeights_le hlam hlog hw n hn
  have he : detectorResidualWeights lam w n = w n - detectorCorrectionWeights lam w n := by
    unfold detectorResidualWeights detectorCorrectionWeights
    ring
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), he]
  have hb := (abs_sub _ _).trans (add_le_add (hw n hn) hc)
  linarith only [hb]

/-- Both actual edge terms together are uniformly `O(T^(7/8))` for the linear mollifier. -/
theorem exists_linearDetector_taper_error_bound :
    ∃ r C : ℝ, 0 < r ∧ r < 1 / 2 ∧ 0 < C ∧
      ∀ (T q η d lam : ℝ) (N : ℕ),
        16 ≤ T → T ≤ q → q ≤ 2 * T → 1 ≤ η → η ≤ T / 2 → |d| ≤ r →
        1 < N → (N : ℝ) ≤ T ^ (1 / 2 : ℝ) → 0 ≤ lam → lam ≤ 1 →
        lam * Real.log N ≤ 1 →
        |lam * (∫ t, iteratedDeriv 1 (blockWindow T q η) t *
          (mollifiedLineJet N (linearDetectorWeights N d) 0 (d : ℂ) t *
            conj (mollifiedLineJet N (detectorCorrectionWeights lam (linearDetectorWeights N d))
              0 (d : ℂ) t)).im) +
          lam ^ 2 / 4 * (∫ t, iteratedDeriv 2 (blockWindow T q η) t *
            ‖mollifiedLineJet N (linearDetectorWeights N d) 0 (d : ℂ) t‖ ^ 2)| ≤
          C * T ^ (7 / 8 : ℝ) := by
  obtain ⟨r, C, hr, hrhalf, hC, hb⟩ := exists_actual_mollified_taper_power_bound
  refine ⟨r, 5 * C / 4, hr, hrhalf, by positivity,
    fun T q η d lam N hT hq hq2 hη hηT hd hN hNT hlam hlam1 hlog => ?_⟩
  have hw : ∀ n ∈ Finset.Icc 1 N, |linearDetectorWeights N d n| ≤ (n : ℝ) ^ (-d) :=
    fun n hn => abs_linearDetectorWeights_le hN d (Finset.mem_Icc.mp hn).1
  obtain ⟨hfirst, hsecond⟩ := hb T q η d N (linearDetectorWeights N d)
    (detectorCorrectionWeights lam (linearDetectorWeights N d)) hT hq hq2 hη hηT hd hNT hw
    (abs_detectorCorrectionWeights_le hlam hlog hw)
  simp_rw [mollifiedLineJet_zero]
  have hlam2 : lam ^ 2 ≤ 1 := by nlinarith only [hlam, hlam1]
  have hp : 0 ≤ C * T ^ (7 / 8 : ℝ) :=
    mul_nonneg hC.le (Real.rpow_nonneg (by linarith only [hT]) _)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hlam, abs_mul, abs_of_nonneg (by positivity : 0 ≤ lam ^ 2 / 4)]
  calc
    _ ≤ lam * (C * T ^ (7 / 8 : ℝ)) + lam ^ 2 / 4 * (C * T ^ (7 / 8 : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst hlam)
        (mul_le_mul_of_nonneg_left hsecond (by positivity))
    _ ≤ 1 * (C * T ^ (7 / 8 : ℝ)) + 1 / 4 * (C * T ^ (7 / 8 : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_right hlam1 hp)
        (mul_le_mul_of_nonneg_right (by linarith only [hlam2]) hp)
    _ = _ := by ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField

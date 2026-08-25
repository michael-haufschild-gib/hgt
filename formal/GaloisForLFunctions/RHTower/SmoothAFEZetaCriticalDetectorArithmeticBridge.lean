import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDirectMollifiedDivisorCoefficient
import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifiedCriticalDetectorDirConv
import GaloisForLFunctions.RHTower.SmoothAFECutoffBounds

/-!
# Critical smooth-AFE detector to arithmetic carrier

At zero displacement, the direct detector coefficient is the unsmoothed critical half-density
coefficient multiplied by the Gaussian AFE cutoff.  The cutoff bounds give a quantitative bridge.
-/

noncomputable section

namespace RHTower

open Complex

/-- A positive natural to the negative complex half-power is its reciprocal real square root. -/
theorem natCast_cpow_neg_half_eq_one_div_sqrt
    {n : ℕ} (hn : 0 < n) :
    (n : ℂ) ^ (-(1 / 2 : ℂ)) = (((1 : ℝ) / Real.sqrt n : ℝ) : ℂ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Complex.cpow_neg]
  push_cast
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hnR.le]
  norm_num

/-- Exact zero-displacement factorization of the smooth direct detector coefficient. -/
theorem smoothAFEZetaDisplacedDirectDetectorPositiveCoeff_zero_eq
    (lam x : ℝ) {n : ℕ} (hn : 0 < n) :
    smoothAFEZetaDisplacedDirectDetectorPositiveCoeff lam 0 x n =
      smoothAFECutoff ((n : ℝ) / x) *
        Sieve.levinsonCriticalDetectorHeadCoeff lam n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) :=
    (Complex.ofReal_log hnR.le).symm
  rw [smoothAFEZetaDisplacedDirectDetectorPositiveCoeff,
    Sieve.levinsonCriticalDetectorHeadCoeff]
  have hpoint : -displacedLinePt 0 0 = -(1 / 2 : ℂ) := by
    unfold displacedLinePt
    norm_num
  rw [hpoint, natCast_cpow_neg_half_eq_one_div_sqrt hn, hlog]
  push_cast
  ring

/-- Exact norm of the unsmoothed critical detector coefficient. -/
theorem norm_levinsonCriticalDetectorHeadCoeff
    (lam : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖Sieve.levinsonCriticalDetectorHeadCoeff lam n‖ =
      ((1 : ℝ) / Real.sqrt n) * |1 - lam * Real.log n| := by
  rw [Sieve.levinsonCriticalDetectorHeadCoeff, Complex.norm_real,
    Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 : ℝ) / Real.sqrt n)]

/-- Uniform power bound for removing the Gaussian cutoff from one critical detector coefficient. -/
theorem exists_norm_smoothAFEZetaDirectDetectorPositiveCoeff_zero_sub_le
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (lam x : ℝ) {n : ℕ}, 0 < x → 0 < n →
      ‖smoothAFEZetaDisplacedDirectDetectorPositiveCoeff lam 0 x n -
          Sieve.levinsonCriticalDetectorHeadCoeff lam n‖ ≤
        K * ((n : ℝ) / x) ^ delta *
          (((1 : ℝ) / Real.sqrt n) * |1 - lam * Real.log n|) := by
  obtain ⟨K, hK, hcut⟩ := exists_norm_smoothAFECutoff_sub_one_le_rpow hdelta
  refine ⟨K, hK, ?_⟩
  intro lam x n hx hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have harg : 0 < (n : ℝ) / x := div_pos hnR hx
  rw [smoothAFEZetaDisplacedDirectDetectorPositiveCoeff_zero_eq lam x hn]
  have hfactor :
      smoothAFECutoff ((n : ℝ) / x) *
          Sieve.levinsonCriticalDetectorHeadCoeff lam n -
        Sieve.levinsonCriticalDetectorHeadCoeff lam n =
      (smoothAFECutoff ((n : ℝ) / x) - 1) *
        Sieve.levinsonCriticalDetectorHeadCoeff lam n := by ring
  rw [hfactor, norm_mul, norm_levinsonCriticalDetectorHeadCoeff lam hn]
  exact mul_le_mul_of_nonneg_right (hcut harg)
    (mul_nonneg (by positivity) (abs_nonneg _))

end RHTower

import GaloisForLFunctions.ConjugateDiagonalGeometry.PolynomialThetaReadingError
import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceLocalCutoff

/-!
# Finite arithmetic readings on shrinking spectral discs

The prescribed polynomial theta prefix resolves every local bump in a
growing height window. The error is uniform in the center and does not
require a zero-free boundary or a lower bound for zero separation.
-/

open Complex MeasureTheory Set Metric Laplacian InnerProductSpace
open scoped Laplacian
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

/-- A shrinking local radius prescribed solely by the source stage. -/
def polynomialSourceLocalRadius (n : ℕ) : ℝ := 1 / (16 * ((n : ℝ) + 1) ^ 6)

lemma polynomialSourceLocalRadius_pos (n : ℕ) : 0 < polynomialSourceLocalRadius n := by
  unfold polynomialSourceLocalRadius
  positivity

lemma polynomialSourceLocalRadius_le_eighth (n : ℕ) :
    polynomialSourceLocalRadius n ≤ 1 / 8 := by
  have hp : 1 ≤ ((n : ℝ) + 1) ^ 6 :=
    one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg (α := ℝ) n))
  unfold polynomialSourceLocalRadius
  apply (div_le_iff₀ (by positivity)).2
  linarith only [hp]

lemma polynomialSourceLocalRadius_inv_sq (n : ℕ) :
    1 / polynomialSourceLocalRadius n ^ 2 = 256 * ((n : ℝ) + 1) ^ 12 := by
  unfold polynomialSourceLocalRadius
  field_simp [show (n : ℝ) + 1 ≠ 0 by positivity]
  ring

/-- A positive finite-source reading localized at the prescribed shrinking radius. -/
def polynomialThetaLocalReading (n : ℕ) (c : ℂ) : ℝ :=
  polynomialThetaSourceReading (sourceLocalCutoff c (polynomialSourceLocalRadius n)) n

lemma polynomialThetaLocalReading_nonneg (n : ℕ) (c : ℂ) :
    0 ≤ polynomialThetaLocalReading n c := by
  apply mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
  apply integral_nonneg
  intro z
  exact mul_nonneg (mul_nonneg (stripSourceCutoff_nonneg n z)
    (sourceLocalCutoff_nonneg _ _ _))
    (finiteThetaSourceCurvature_nonneg (polynomialSourceRegulator_pos n).le _ z)

/-- Local testing has the exact polynomial differential cost of the shrinking radius. -/
lemma abs_laplacian_polynomialSourceLocalCutoff_le (n : ℕ) (c : ℂ)
    (hc : 0 ≤ c.re ∧ c.re ≤ 1) (hcy : |c.im| ≤ (n : ℝ) / 2) (z : ℂ) :
    |Δ (fun w => stripSourceCutoff n w *
      sourceLocalCutoff c (polynomialSourceLocalRadius n) w) z| ≤
      stripSourceCutoffControl * (256 * ((n : ℝ) + 1) ^ 12) := by
  rw [stripSourceCutoff_mul_local_eq n c hc hcy (polynomialSourceLocalRadius_pos n)
    (polynomialSourceLocalRadius_le_eighth n)]
  refine (abs_sourceLocalCutoff_laplacian_le c (polynomialSourceLocalRadius n) z).trans_eq ?_
  calc
    stripSourceCutoffControl / polynomialSourceLocalRadius n ^ 2 =
        stripSourceCutoffControl * (1 / polynomialSourceLocalRadius n ^ 2) := by ring
    _ = _ := by rw [polynomialSourceLocalRadius_inv_sq]

/-- One universal coefficient controls every shrinking local trace at the prescribed stage. -/
theorem exists_polynomialThetaLocalReading_error_bound :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ n : ℕ, 1 ≤ n → ∀ c : ℂ,
      (0 ≤ c.re ∧ c.re ≤ 1) → |c.im| ≤ (n : ℝ) / 2 →
      |polynomialThetaLocalReading n c -
        zetaSourceTrace (sourceLocalCutoff c (polynomialSourceLocalRadius n))| ≤
      E / ((n : ℝ) + 1) ^ 2 := by
  obtain ⟨D, hD, hlocal⟩ := exists_polynomialSourceLocalError_bound
  have hC := stripThetaPotentialConstant_nonneg
  refine ⟨15488 * stripThetaPotentialConstant + 128 * D / Real.pi,
    by positivity, fun n hn c hc hcy => ?_⟩
  have hb := abs_laplacian_polynomialSourceLocalCutoff_le n c hc hcy
  have hfinite := abs_polynomialThetaSourceReading_sub_full_le
    (sourceLocalCutoff c (polynomialSourceLocalRadius n)) (contDiff_sourceLocalCutoff _ _)
    n (by positivity : 0 ≤ 256 * ((n : ℝ) + 1) ^ 12) hb
  have hfinite' :
      |polynomialThetaSourceReading (sourceLocalCutoff c (polynomialSourceLocalRadius n)) n -
        polynomialSourceReading (sourceLocalCutoff c (polynomialSourceLocalRadius n)) n| ≤
      15488 * stripThetaPotentialConstant / ((n : ℝ) + 1) ^ 6 := by
    refine hfinite.trans_eq ?_
    field_simp [Real.pi_ne_zero, show (n : ℝ) + 1 ≠ 0 by positivity]
    ring
  have hsource := abs_polynomialSourceReading_sub_current_le
    (sourceLocalCutoff c (polynomialSourceLocalRadius n)) (contDiff_sourceLocalCutoff _ _)
    n (fun z _ => hb z)
  rw [stripSourceCutoff_mul_local_eq n c hc hcy (polynomialSourceLocalRadius_pos n)
    (polynomialSourceLocalRadius_le_eighth n),
    xiCurrentPairing_eq_trace _ (contDiff_sourceLocalCutoff _ _)
      (hasCompactSupport_sourceLocalCutoff _ (polynomialSourceLocalRadius_pos n).ne')] at hsource
  have hsource' :
      |polynomialSourceReading (sourceLocalCutoff c (polynomialSourceLocalRadius n)) n -
        zetaSourceTrace (sourceLocalCutoff c (polynomialSourceLocalRadius n))| ≤
      (128 * D / Real.pi) / ((n : ℝ) + 1) ^ 2 := by
    refine hsource.trans ?_
    calc
      (2 * Real.pi)⁻¹ * (stripSourceCutoffControl * (256 * ((n : ℝ) + 1) ^ 12)) *
          xiLocalPotentialError (polynomialSourceRegulator n) 0 (11 * ((n : ℝ) + 1)) =
        ((2 * Real.pi)⁻¹ * (256 * ((n : ℝ) + 1) ^ 12)) *
          (stripSourceCutoffControl *
            xiLocalPotentialError (polynomialSourceRegulator n) 0 (11 * ((n : ℝ) + 1))) := by ring
      _ ≤ ((2 * Real.pi)⁻¹ * (256 * ((n : ℝ) + 1) ^ 12)) *
          (D / ((n : ℝ) + 1) ^ 14) :=
        mul_le_mul_of_nonneg_left (hlocal n hn) (by positivity)
      _ = _ := by
        field_simp [Real.pi_ne_zero, show (n : ℝ) + 1 ≠ 0 by positivity]
        ring
  have hpow : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 6 := by
    have h4 : 1 ≤ ((n : ℝ) + 1) ^ 4 :=
      one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg (α := ℝ) n))
    have h := le_mul_of_one_le_right (by positivity : 0 ≤ ((n : ℝ) + 1) ^ 2) h4
    simpa only [← pow_add] using h
  have hfinite'' := hfinite'.trans
    (div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 15488) hC)
      (by positivity) hpow)
  have ht := dist_triangle
    (polynomialThetaSourceReading (sourceLocalCutoff c (polynomialSourceLocalRadius n)) n)
    (polynomialSourceReading (sourceLocalCutoff c (polynomialSourceLocalRadius n)) n)
    (zetaSourceTrace (sourceLocalCutoff c (polynomialSourceLocalRadius n)))
  simp only [Real.dist_eq] at ht
  exact (ht.trans (add_le_add hfinite'' hsource')).trans_eq (by ring)

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.polynomialThetaLocalReading_nonneg
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_polynomialThetaLocalReading_error_bound

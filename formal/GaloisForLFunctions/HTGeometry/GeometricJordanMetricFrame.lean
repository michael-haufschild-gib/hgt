import GaloisForLFunctions.HTGeometry.StrictUpperPowerEnergy
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperatorBound
import GaloisForLFunctions.HilbertMetric.PseudospectrumSimilarity

/-!
# Explicit positive metric frames for a full Jordan chain

Geometric diagonal frames attain every condition-number budget. They rescale
every unit superdiagonal entry by the same reciprocal ratio.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Matrix Finset

def metricJordanShift (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => if i.val + 1 = j.val then 1 else 0

theorem metricJordanShift_strictUpper (n : ℕ) :
    ∀ i j, j ≤ i → metricJordanShift n i j = 0 := by
  intro i j hij
  have hn : i.val + 1 ≠ j.val := by change j.val ≤ i.val at hij; omega
  simp [metricJordanShift, hn]

theorem metricJordanShift_nilpotent (n : ℕ) : metricJordanShift n ^ (n + 1) = 0 :=
  strictUpperPower_nilpotent _ (metricJordanShift_strictUpper n)

theorem metricJordanShift_top_energy (n : ℕ) : matHSNormSq (metricJordanShift n ^ n) = 1 := by
  rw [strictUpperPower_top_energy _ (metricJordanShift_strictUpper n)]
  simp [metricJordanShift]

theorem metricJordanShift_top_hsNorm (n : ℕ) : hsNorm (metricJordanShift n ^ n) = 1 := by
  have he : hsNorm (metricJordanShift n ^ n) ^ 2 = 1 := by
    rw [hsNorm_sq]
    exact metricJordanShift_top_energy n
  have hn := hsNorm_nonneg (metricJordanShift n ^ n)
  nlinarith

theorem metricJordanShift_energy (n : ℕ) : matHSNormSq (metricJordanShift n) = n := by
  have hrow : ∀ i : Fin n, (∑ j, ‖metricJordanShift n i.castSucc j‖ ^ 2) = 1 := by
    intro i
    rw [Finset.sum_eq_single i.succ]
    · simp [metricJordanShift]
    · intro j _ hj
      have hne : i.val + 1 ≠ j.val := by
        intro h; apply hj; exact Fin.ext h.symm
      simp [metricJordanShift, hne]
    · simp
  have hlast : (∑ j, ‖metricJordanShift n (Fin.last n) j‖ ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hne : n + 1 ≠ j.val := by have := j.isLt; omega
    simp [metricJordanShift, hne]
  rw [matHSNormSq, Fin.sum_univ_castSucc, hlast]
  simp [hrow]

def geometricJordanFrame (n : ℕ) (q : ℝ) (hq : q ≠ 0) :
    (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ where
  val := Matrix.diagonal fun i => (q : ℂ) ^ i.val
  inv := Matrix.diagonal fun i => (q : ℂ)⁻¹ ^ i.val
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    have hqc : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
    simp [hqc]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    have hqc : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
    simp [hqc]

theorem geometricJordanFrame_norm (n : ℕ) {q : ℝ} (hq : 1 ≤ q) :
    ‖(geometricJordanFrame n q (by linarith) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)‖ =
      q ^ n := by
  change ‖Matrix.diagonal (fun i : Fin (n + 1) => (q : ℂ) ^ i.val)‖ = q ^ n
  rw [Matrix.l2_opNorm_diagonal]
  have hnorm : ∀ i : Fin (n + 1), ‖(q : ℂ) ^ i.val‖ = q ^ i.val := by
    intro i
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    rw [hnorm]
    exact pow_le_pow_right₀ hq (by have := i.isLt; omega)
  · have h := norm_le_pi_norm (fun i : Fin (n + 1) => (q : ℂ) ^ i.val) (Fin.last n)
    rwa [hnorm] at h

theorem geometricJordanFrame_inv_norm (n : ℕ) {q : ℝ} (hq : 1 ≤ q) :
    ‖(↑(geometricJordanFrame n q (by linarith))⁻¹ :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)‖ = 1 := by
  change ‖Matrix.diagonal (fun i : Fin (n + 1) => (q : ℂ)⁻¹ ^ i.val)‖ = 1
  rw [Matrix.l2_opNorm_diagonal]
  have hnorm : ∀ i : Fin (n + 1), ‖(q : ℂ)⁻¹ ^ i.val‖ = q⁻¹ ^ i.val := by
    intro i
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    rw [hnorm]
    exact pow_le_one₀ (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq)
  · have h := norm_le_pi_norm (fun i : Fin (n + 1) => (q : ℂ)⁻¹ ^ i.val) 0
    simpa using h

theorem geometricJordanFrame_conditionNumber (n : ℕ) {q : ℝ} (hq : 1 ≤ q) :
    HilbertMetric.similarityConditionNumber (geometricJordanFrame n q (by linarith)) = q ^ n := by
  rw [HilbertMetric.similarityConditionNumber, geometricJordanFrame_norm n hq,
    geometricJordanFrame_inv_norm n hq, mul_one]

theorem geometricJordanFrame_conjugate (n : ℕ) {q : ℝ} (hq : q ≠ 0) :
    (geometricJordanFrame n q hq : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *
        metricJordanShift n * (↑(geometricJordanFrame n q hq)⁻¹ :
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      (q : ℂ)⁻¹ • metricJordanShift n := by
  have hqc : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
  ext i j
  change ((Matrix.diagonal (fun i : Fin (n + 1) => (q : ℂ) ^ i.val) * metricJordanShift n) *
      Matrix.diagonal (fun i : Fin (n + 1) => (q : ℂ)⁻¹ ^ i.val)) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.smul_apply, smul_eq_mul, metricJordanShift]
  by_cases hij : i.val + 1 = j.val
  · simp only [if_pos hij, mul_one]
    rw [← hij, pow_succ]
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hqc, one_pow, one_mul]
  · simp [hij]

theorem geometricJordanFrame_gram_posDef (n : ℕ) {q : ℝ} (hq : q ≠ 0) :
    let P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := geometricJordanFrame n q hq
    (Pᴴ * P).PosDef := by
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_iff_isUnit.mpr (geometricJordanFrame n q hq).isUnit)

theorem matHSNormSq_scalar_smul {d : ℕ}
    (a : ℂ) (M : Matrix (Fin d) (Fin d) ℂ) :
    matHSNormSq (a • M) = ‖a‖ ^ 2 * matHSNormSq M := by
  simp only [matHSNormSq, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow,
    Finset.mul_sum]

theorem geometricJordanFrame_scaled_energy (n : ℕ) {q : ℝ} (hq : 1 ≤ q) :
    matHSNormSq ((q : ℂ)⁻¹ • metricJordanShift n) = (n : ℝ) / q ^ 2 := by
  rw [matHSNormSq_scalar_smul, metricJordanShift_energy, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  simp [div_eq_mul_inv, inv_pow, mul_comm]

end
end GaloisForLFunctions.HTGeometry

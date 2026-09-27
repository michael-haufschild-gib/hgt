import GaloisForLFunctions.RHTower.XiGaussianFixedTimeLocalization

/-!
# Exact finite normalization of one retained Xi orbit

The real affine correction fixes the selected complex value at every finite
stage, rather than only in the limit. Its size is eventually bounded by one
fixed real linear polynomial on the entire actual divisor.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

theorem eval_xiGaussianOrbitProduct_ne_zero (z : ℂ) (F : Finset XiZeroCopy) :
    evalRealPolynomial (xiGaussianSelectedAnnihilator (xiGaussianOrbitComplement z) F) z ≠ 0 := by
  classical
  rw [xiGaussianSelectedAnnihilator, eval_xiGaussianAnnihilator]
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  have h : xiSpectralPoint q ^ 2 ≠ z ∧
      xiSpectralPoint q ^ 2 ≠ (starRingEnd ℂ) z := (Finset.mem_filter.mp hq).2
  have hw := pow_ne_zero 2 (xiSpectralPoint_ne_zero q)
  rw [eval_realNormalizedConjFactor]
  apply mul_ne_zero
  · intro he
    exact h.1 ((inv_mul_eq_one₀ hw).mp (sub_eq_zero.mp he).symm)
  · rw [map_inv₀]
    intro he
    have hz := (inv_mul_eq_one₀ ((_root_.map_ne_zero (starRingEnd ℂ)).mpr hw)).mp
      (sub_eq_zero.mp he).symm
    exact h.2 (by simpa using congrArg (starRingEnd ℂ) hz)

/-- A finite real affine correction with a prescribed complex target. -/
def xiGaussianOrbitNormalizer (z v : ℂ) (F : Finset XiZeroCopy) : Polynomial ℝ :=
  realLinearInterpolator z
    (v / evalRealPolynomial (xiGaussianSelectedAnnihilator (xiGaussianOrbitComplement z) F) z)

/-- The complete real polynomial, including all selected annihilator factors. -/
def xiGaussianNormalizedOrbitPolynomial (z v : ℂ) (F : Finset XiZeroCopy) : Polynomial ℝ :=
  xiGaussianOrbitNormalizer z v F *
    xiGaussianSelectedAnnihilator (xiGaussianOrbitComplement z) F

theorem eval_xiGaussianNormalizedOrbitPolynomial_target
    (z : {z : ℂ // z.im ≠ 0}) (v : ℂ) (F : Finset XiZeroCopy) :
    evalRealPolynomial (xiGaussianNormalizedOrbitPolynomial z v F) z = v := by
  rw [xiGaussianNormalizedOrbitPolynomial, evalRealPolynomial_mul,
    xiGaussianOrbitNormalizer, evalRealLinearInterpolator z.property,
    div_mul_cancel₀ _ (eval_xiGaussianOrbitProduct_ne_zero z F)]

theorem xiGaussianNormalizedOrbitPolynomial_vanishes (z v : ℂ) (F : Finset XiZeroCopy)
    (q : {q : XiZeroCopy // q ∈ F ∧ q ∈ xiGaussianOrbitComplement z}) :
    evalRealPolynomial (xiGaussianNormalizedOrbitPolynomial z v F)
      (xiSpectralPoint q.1 ^ 2) = 0 := by
  classical
  rw [xiGaussianNormalizedOrbitPolynomial, evalRealPolynomial_mul]
  have h := xiGaussianAnnihilator_vanishes
    (F.filter (· ∈ xiGaussianOrbitComplement z))
    ⟨q.1, Finset.mem_filter.mpr q.property⟩
  change evalRealPolynomial
    (xiGaussianSelectedAnnihilator (xiGaussianOrbitComplement z) F)
      (xiSpectralPoint q.1 ^ 2) = 0 at h
  rw [h, mul_zero]

private theorem xiGaussianAffineInterpolation_factor_bound
    (z : {z : ℂ // z.im ≠ 0}) (q : XiZeroCopy) :
    1 + (|z.1.re| + ‖xiSpectralPoint q ^ 2‖) / |z.1.im| ≤
      (1 + (|z.1.re| + 2) / |z.1.im|) * ‖1 + xiSpectralPoint q ^ 2‖ := by
  let w := xiSpectralPoint q ^ 2
  have hd : 0 < |z.1.im| := abs_pos.mpr z.property
  have hnorm : ‖w‖ ≤ 2 * w.re := by
    simpa only [w, norm_pow, Complex.sq_norm] using
      (xiSpectralPoint_normSq_lt_two_mul_sq_re q).le
  have hre : 1 + w.re ≤ ‖1 + w‖ := by
    simpa only [Complex.add_re, Complex.one_re] using Complex.re_le_norm (1 + w)
  have hunit : 1 ≤ ‖1 + w‖ := by linarith [xiSpectralSq_re_pos q]
  have hw : ‖w‖ ≤ 2 * ‖1 + w‖ := by linarith
  have hnum : |z.1.re| + ‖w‖ ≤ (|z.1.re| + 2) * ‖1 + w‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hunit (abs_nonneg z.1.re)]
  calc
    _ ≤ ‖1 + w‖ + ((|z.1.re| + 2) * ‖1 + w‖) / |z.1.im| :=
      add_le_add hunit (div_le_div_of_nonneg_right hnum hd.le)
    _ = _ := by ring

/-- One constant controls every finite normalization and every divisor copy
after a single fixed head. It is independent of the growing polynomial degree. -/
theorem exists_xiGaussianOrbitNormalizer_linear_bound
    (z : {z : ℂ // z.im ≠ 0}) (v : ℂ) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ F : Finset XiZeroCopy in atTop,
      ∀ q : XiZeroCopy,
        ‖evalRealPolynomial (xiGaussianOrbitNormalizer z v F) (xiSpectralPoint q ^ 2)‖ ≤
          M * ‖evalRealPolynomial (1 + Polynomial.X) (xiSpectralPoint q ^ 2)‖ := by
  obtain ⟨a, ha, hlim⟩ := exists_xiGaussianOrbitProduct_nonzero_limit z
  have ha' : 0 < ‖a‖ / 2 := div_pos (norm_pos_iff.mpr ha) (by positivity)
  have hlarge : ∀ᶠ F : Finset XiZeroCopy in atTop,
      ‖a‖ / 2 < ‖evalRealPolynomial
        (xiGaussianSelectedAnnihilator (xiGaussianOrbitComplement z) F) z‖ :=
    hlim.norm.eventually (Ioi_mem_nhds (by linarith [norm_pos_iff.mpr ha]))
  let B := 1 + (|z.1.re| + 2) / |z.1.im|
  let V := ‖v‖ / (‖a‖ / 2)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hV : 0 ≤ V := div_nonneg (norm_nonneg _) ha'.le
  refine ⟨B * (V + 1), mul_pos hB (by linarith), ?_⟩
  filter_upwards [hlarge] with F hF q
  have hv : ‖v / evalRealPolynomial
      (xiGaussianSelectedAnnihilator (xiGaussianOrbitComplement z) F) z‖ ≤ V := by
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) ha' hF.le
  have hfactor := xiGaussianAffineInterpolation_factor_bound z q
  have hraw := norm_evalRealLinearInterpolator_le
    (α := z.1) (v := v / evalRealPolynomial
      (xiGaussianSelectedAnnihilator (xiGaussianOrbitComplement z) F) z)
    (z := xiSpectralPoint q ^ 2) z.property
  change ‖evalRealPolynomial (xiGaussianOrbitNormalizer z v F) (xiSpectralPoint q ^ 2)‖ ≤ _
  calc
    _ ≤ (1 + (|z.1.re| + ‖xiSpectralPoint q ^ 2‖) / |z.1.im|) *
        ‖v / evalRealPolynomial
          (xiGaussianSelectedAnnihilator (xiGaussianOrbitComplement z) F) z‖ := hraw
    _ ≤ (B * ‖1 + xiSpectralPoint q ^ 2‖) * V :=
      mul_le_mul hfactor hv (norm_nonneg _) (mul_nonneg hB.le (norm_nonneg _))
    _ ≤ (B * (V + 1)) * ‖evalRealPolynomial (1 + Polynomial.X) (xiSpectralPoint q ^ 2)‖ := by
      have heval : evalRealPolynomial (1 + Polynomial.X) (xiSpectralPoint q ^ 2) =
          1 + xiSpectralPoint q ^ 2 := by simp [evalRealPolynomial]
      rw [heval]
      nlinarith [mul_nonneg hB.le (norm_nonneg (1 + xiSpectralPoint q ^ 2))]

end RHTower

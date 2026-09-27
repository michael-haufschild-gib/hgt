import GaloisForLFunctions.RHTower.XiGaussianGlobalPhaseControl

/-!
# Decaying signed prime--Gamma cancellation from the actual Xi spectral gap

Splitting heat between polynomial point control and the full spectral divisor
retains the certified height gap. Every coefficient cross term and every zero
copy remains present. This bounds the absolute residual without deciding its sign.
-/

open scoped Real SchwartzMap NNReal
open MeasureTheory GaloisForLFunctions
noncomputable section

namespace RHTower

/-- The certified height floor gives a uniform positive gap for every spectral square. -/
theorem xiSpectralSq_re_gt_gap (q : XiZeroCopy) :
    (127 / 4 : ℝ) < (xiSpectralPoint q ^ 2).re := by
  have hh := xiSpectral_re_sq_gt_thirtytwo q
  have hi := xiSpectralPoint_im_sq_lt_quarter q
  rw [pow_two, Complex.mul_re]
  nlinarith only [hh, hi]

/-- A reciprocal-square heat majorant is valid at every positive time. -/
theorem xiGaussian_exp_le_reciprocal (s : {s : ℝ // 0 < s}) (q : XiZeroCopy) :
    Real.exp (-((s : ℝ) * (xiSpectralPoint q ^ 2).re)) ≤
      (2 / (s : ℝ)) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  let A := (xiSpectralPoint q ^ 2).re
  let N := ‖xiSpectralPoint q‖ ^ 2
  have hN : 0 < N := pow_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)) _
  have hsector : N < 2 * A := by
    simpa only [N, A, Complex.sq_norm] using xiSpectralPoint_normSq_lt_two_mul_sq_re q
  have hA : 0 < A := by linarith only [hN, hsector]
  have hsA := mul_pos s.property hA
  have he : Real.exp (-((s : ℝ) * A)) ≤ ((s : ℝ) * A)⁻¹ := by
    rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) hsA]
    linarith only [Real.add_one_le_exp ((s : ℝ) * A)]
  refine he.trans ?_
  change ((s : ℝ) * A)⁻¹ ≤ (2 / (s : ℝ)) * (1 / N)
  rw [← one_div, div_mul_div_comm]
  apply (div_le_div_iff₀ hsA (mul_pos s.property hN)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hsector.le s.property.le]

/-- Half of the remaining heat supplies exponential decay, half supplies summability. -/
theorem xiGaussian_halfHeat_exp_le_gap (t : {t : ℝ // 0 < t}) (q : XiZeroCopy) :
    Real.exp (-((t : ℝ) / 2 * (xiSpectralPoint q ^ 2).re)) ≤
      ((8 / (t : ℝ)) * Real.exp (-(127 * (t : ℝ) / 16))) *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  let s : {s : ℝ // 0 < s} := ⟨(t : ℝ) / 4, div_pos t.property (by positivity)⟩
  have hsmall := xiGaussian_exp_le_reciprocal s q
  have hgap : Real.exp (-((t : ℝ) / 4 * (xiSpectralPoint q ^ 2).re)) ≤
      Real.exp (-(127 * (t : ℝ) / 16)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (xiSpectralSq_re_gt_gap q).le
      (div_nonneg t.property.le (by positivity : (0 : ℝ) ≤ 4))
    linarith only [h]
  calc
    _ = Real.exp (-((t : ℝ) / 4 * (xiSpectralPoint q ^ 2).re)) *
        Real.exp (-((t : ℝ) / 4 * (xiSpectralPoint q ^ 2).re)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ ((2 / (s : ℝ)) * (1 / ‖xiSpectralPoint q‖ ^ 2)) *
        Real.exp (-(127 * (t : ℝ) / 16)) :=
      mul_le_mul hsmall hgap (Real.exp_pos _).le
        (mul_nonneg (div_nonneg (by positivity) s.property.le) (by positivity))
    _ = _ := by change (2 / ((t : ℝ) / 4) * _) * _ = _; ring

/-- Complete amplitude point control uses a single degree-only envelope. -/
theorem norm_xiScaledEvenGaussianAmplitude_le_global (P : Polynomial ℝ)
    (r : {r : ℝ // 0 < r}) (q : XiZeroCopy) :
    ‖xiScaledEvenGaussianAmplitude P r q‖ ≤
      gaussianGlobalVerticalSlopeEnvelope (2 * P.natDegree) ((r : ℝ) / 2) *
        ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ := by
  let R : ℝ≥0 := ⟨(r : ℝ) / 2, div_nonneg r.property.le (by positivity)⟩
  have him : -(1 / 2 : ℝ) ≤ (xiSpectralPoint q).im ∧ (xiSpectralPoint q).im ≤ 1 / 2 := by
    have h := xiSpectralPoint_im_sq_lt_quarter q
    constructor <;> nlinarith only [h, sq_nonneg ((xiSpectralPoint q).im + 1 / 2),
      sq_nonneg ((xiSpectralPoint q).im - 1 / 2)]
  let δ : Set.Icc (-(R : ℝ)) R := ⟨(r : ℝ) * (xiSpectralPoint q).im, by
    constructor
    · change -((r : ℝ) / 2) ≤ (r : ℝ) * (xiSpectralPoint q).im
      nlinarith only [mul_le_mul_of_nonneg_left him.1 r.property.le]
    · change (r : ℝ) * (xiSpectralPoint q).im ≤ (r : ℝ) / 2
      nlinarith only [mul_le_mul_of_nonneg_left him.2 r.property.le]⟩
  have herr := norm_entirePolynomialGaussian_vertical_sub_le (evenSquarePolynomial P) R
    ((r : ℝ) * (xiSpectralPoint q).re) δ
  have hbase := norm_polyGaussSchwartz_point_le (evenSquarePolynomial P)
    ((r : ℝ) * (xiSpectralPoint q).re)
  have ht := norm_le_norm_sub_add (xiScaledEvenGaussianAmplitude P r q)
    (polyGaussSchwartz (evenSquarePolynomial P) ((r : ℝ) * (xiSpectralPoint q).re))
  have he : entirePolynomialGaussian (evenSquarePolynomial P)
      (((r : ℝ) * (xiSpectralPoint q).re : ℝ) + ((δ : ℝ) : ℂ) * Complex.I) =
      xiScaledEvenGaussianAmplitude P r q := by
    simpa only [entirePolynomialGaussian, δ] using
      (xiScaledEvenGaussianAmplitude_vertical P r q).symm
  rw [he, natDegree_evenSquarePolynomial] at herr
  rw [natDegree_evenSquarePolynomial] at hbase
  have hs : gaussianStripSamplingFactor (2 * P.natDegree) 1 *
      (verticalPolynomialGaussianDefect (2 * P.natDegree) R + 1) ≤
      gaussianCoordinateVerticalSlope (2 * P.natDegree) R := by
    unfold gaussianCoordinateVerticalSlope
    have hC := gaussianStripSamplingFactor_nonneg (2 * P.natDegree + 1) 1
    have hL := gaussianVerticalDefectSlope_nonneg (2 * P.natDegree + 1) R
    have hfirst : 0 ≤ gaussianStripSamplingFactor (2 * P.natDegree + 1) 1 *
      gaussianVerticalDefectSlope (2 * P.natDegree + 1) R *
        (Real.sqrt (4 * π * (((2 * P.natDegree : ℕ) : ℝ) + 1)) / (2 * π)) := by positivity
    linarith only [hfirst]
  have hbound := mul_le_mul_of_nonneg_right
    (hs.trans (gaussianCoordinateVerticalSlope_le_globalEnvelope (2 * P.natDegree) R))
    (norm_nonneg ((polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)))
  change gaussianStripSamplingFactor _ 1 * (_ + 1) *
      ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ≤ _ at hbound
  change ‖xiScaledEvenGaussianAmplitude P r q‖ ≤ gaussianGlobalVerticalSlopeEnvelope
    (2 * P.natDegree) R * ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖
  nlinarith only [ht, herr, hbase, hbound]

/-- The native polynomial term has whole-mass point control at every positive time. -/
theorem norm_xiPolynomialGaussianHeatTerm_le_globalPoint (Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) (q : XiZeroCopy) :
    ‖xiPolynomialGaussianHeatTerm Q t q‖ ≤
      (xiGaussianHeatScale t : ℝ) *
        gaussianGlobalVerticalSlopeEnvelope (2 * Q.natDegree) ((xiGaussianHeatScale t : ℝ) / 2) ^ 2 *
          routeUPolynomialGaussianMass Q t := by
  let r := xiGaussianHeatScale t
  let P := xiGaussianUnscalePolynomial Q r
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_xiScaledEvenGaussianAmplitude_le_global P r q) 2
  rw [← norm_pow, xiScaledEvenGaussianAmplitude_sq] at h
  change ‖xiPolynomialGaussianHeatTerm (P.comp (Polynomial.C ((r : ℝ) ^ 2) * Polynomial.X))
      (xiGaussianScaleHeat r) q‖ ≤ _ at h
  dsimp only [P, r] at h
  rw [xiGaussianUnscalePolynomial_comp_scale, xiGaussianScaleHeat_heatScale,
    natDegree_xiGaussianUnscalePolynomial, mul_pow, xiGaussianUnscalePolynomial_norm_sq] at h
  convert h using 1; ring

/-- Half time for the whole-polynomial mass in the decaying envelope. -/
def xiGaussianHalfHeat (t : {t : ℝ // 0 < t}) : {t : ℝ // 0 < t} :=
  ⟨(t : ℝ) / 2, div_pos t.property (by positivity)⟩

/-- Explicit all-time cancellation budget after retaining the certified spectral gap. -/
def xiGaussianGapCancellationBudget (d : ℕ) (t : {t : ℝ // 0 < t}) : ℝ :=
  (8 / (t : ℝ)) * xiGaussianGlobalPhaseBudget d (xiGaussianHalfHeat t) *
    Real.exp (-(127 * (t : ℝ) / 16))

theorem xiGaussianGapCancellationBudget_mono (t : {t : ℝ // 0 < t}) :
    Monotone (fun d : ℕ => xiGaussianGapCancellationBudget d t) := by
  intro d e hde
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (xiGaussianGlobalPhaseBudget_mono (xiGaussianHalfHeat t) hde)
      (div_nonneg (by positivity) t.property.le)) (Real.exp_pos _).le

/-- The cancellation budget has an explicit negative linear heat exponent. -/
theorem xiGaussianGapCancellationBudget_eq (d : ℕ) (t : {t : ℝ // 0 < t}) :
    xiGaussianGapCancellationBudget d t =
      (8 / (t : ℝ)) * (198 / 3175 : ℝ) * (xiGaussianHeatScale (xiGaussianHalfHeat t) : ℝ) *
        (1 + 2 * Real.sqrt (4 * π * ((d : ℝ) + 3))) *
        Real.exp (-(125 * (t : ℝ) / 16) + Real.sqrt ((t : ℝ) * ((d : ℝ) + 2))) *
        (4 * (d : ℝ) + 9 + 3 / 4 * Real.sqrt ((t : ℝ) * ((d : ℝ) + 2))) ^ 2 := by
  let u := xiGaussianHalfHeat t
  let r : ℝ := xiGaussianHeatScale u
  have hrB : r * Real.sqrt (4 * π * ((d : ℝ) + 2)) =
      Real.sqrt ((t : ℝ) * ((d : ℝ) + 2)) := by
    rw [xiGaussianHeatScale_mul_degreeRoot]
    congr 1
    change 2 * ((t : ℝ) / 2) * ((d : ℝ) + 2) = _
    ring
  have he : Real.exp ((u : ℝ) / 4 + r * Real.sqrt (4 * π * ((d : ℝ) + 2))) *
      Real.exp (-(127 * (t : ℝ) / 16)) =
      Real.exp (-(125 * (t : ℝ) / 16) + Real.sqrt ((t : ℝ) * ((d : ℝ) + 2))) := by
    rw [← Real.exp_add, hrB]
    congr 1
    change ((t : ℝ) / 2) / 4 + _ + _ = _
    ring
  have hbr : 4 * (d : ℝ) + 9 + 3 / 4 * r * Real.sqrt (4 * π * ((d : ℝ) + 2)) =
      4 * (d : ℝ) + 9 + 3 / 4 * Real.sqrt ((t : ℝ) * ((d : ℝ) + 2)) := by
    rw [mul_assoc (3 / 4 : ℝ), hrB]
  rw [xiGaussianGapCancellationBudget, xiGaussianGlobalPhaseBudget_eq]
  change (8 / (t : ℝ)) * ((198 / 3175 : ℝ) * r * _ * _ * _) * _ = _
  rw [hbr]
  calc
    _ = (8 / (t : ℝ)) * (198 / 3175 : ℝ) * r *
        (1 + 2 * Real.sqrt (4 * π * ((d : ℝ) + 3))) *
        (Real.exp ((u : ℝ) / 4 + r * Real.sqrt (4 * π * ((d : ℝ) + 2))) *
          Real.exp (-(127 * (t : ℝ) / 16))) *
        (4 * (d : ℝ) + 9 + 3 / 4 * Real.sqrt ((t : ℝ) * ((d : ℝ) + 2))) ^ 2 := by ring
    _ = _ := by rw [he]

/-- Full positive energy has a coefficient-uniform decaying whole-mass upper bound. -/
theorem tsum_norm_xiPolynomialGaussianHeatTerm_le_gap (Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    (∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm Q t q‖) ≤
      xiGaussianGapCancellationBudget (2 * Q.natDegree) t *
        routeUPolynomialGaussianMass Q (xiGaussianHalfHeat t) := by
  let u := xiGaussianHalfHeat t
  let A := (xiGaussianHeatScale u : ℝ) *
    gaussianGlobalVerticalSlopeEnvelope (2 * Q.natDegree) ((xiGaussianHeatScale u : ℝ) / 2) ^ 2 *
      routeUPolynomialGaussianMass Q u
  let B := (8 / (t : ℝ)) * Real.exp (-(127 * (t : ℝ) / 16))
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg (xiGaussianHeatScale u).property.le (sq_nonneg _))
    (routeUPolynomialGaussianMass_nonneg Q u)
  have hB : 0 ≤ B := mul_nonneg (div_nonneg (by positivity) t.property.le) (Real.exp_pos _).le
  have hp (q : XiZeroCopy) : ‖xiPolynomialGaussianHeatTerm Q t q‖ ≤
      (A * B) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
    have heq : ‖xiPolynomialGaussianHeatTerm Q t q‖ =
        ‖xiPolynomialGaussianHeatTerm Q u q‖ *
          Real.exp (-((t : ℝ) / 2 * (xiSpectralPoint q ^ 2).re)) := by
      rw [norm_xiPolynomialGaussianHeatTerm, norm_xiPolynomialGaussianHeatTerm, mul_assoc,
        ← Real.exp_add]
      congr 2
      change -((t : ℝ) * _) = -((t : ℝ) / 2 * _) + -((t : ℝ) / 2 * _)
      ring
    rw [heq]
    exact (mul_le_mul (norm_xiPolynomialGaussianHeatTerm_le_globalPoint Q u q)
      (xiGaussian_halfHeat_exp_le_gap t q) (Real.exp_pos _).le hA).trans_eq (mul_assoc _ _ _).symm
  have hs := Summable.tsum_le_tsum hp (summable_norm_xiPolynomialGaussianHeatTerm t.property Q)
    (xiSpectralPoint_inv_sq_summable.mul_left (A * B))
  rw [tsum_mul_left] at hs
  have hm := mul_le_mul_of_nonneg_left xiHeatInverseNormMass_le (mul_nonneg hA hB)
  refine (hs.trans hm).trans_eq ?_
  unfold xiGaussianGapCancellationBudget xiGaussianGlobalPhaseBudget
  dsimp only [A, B, u]
  ring

/-- The complete trace is exponentially small in absolute value; its sign is not discarded. -/
theorem abs_xiPolynomialGaussianHeatTraceReal_le_gap (Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    |xiPolynomialGaussianHeatTraceReal Q t| ≤
      xiGaussianGapCancellationBudget (2 * Q.natDegree) t *
        routeUPolynomialGaussianMass Q (xiGaussianHalfHeat t) := by
  exact (Complex.abs_re_le_norm _).trans
    ((norm_tsum_le_tsum_norm (summable_norm_xiPolynomialGaussianHeatTerm t.property Q)).trans
      (tsum_norm_xiPolynomialGaussianHeatTerm_le_gap Q t))

/-- All Hankel orders and all coefficient directions retain the exponential cancellation bound. -/
theorem abs_xiHeatHankelForm_le_gap (N : ℕ) (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}) :
    |xiHeatHankelForm N a t| ≤ xiGaussianGapCancellationBudget (2 * N) t *
      routeUPolynomialGaussianMass
        (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) (xiGaussianHalfHeat t) := by
  classical
  let Q : Polynomial ℝ := ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j
  have hd : Q.natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (Polynomial.natDegree_C_mul_X_pow_le (a j) j).trans (Finset.mem_range.mp hj).le
  have h := (abs_xiPolynomialGaussianHeatTraceReal_le_gap Q t).trans
    (mul_le_mul_of_nonneg_right (xiGaussianGapCancellationBudget_mono t (Nat.mul_le_mul_left 2 hd))
      (routeUPolynomialGaussianMass_nonneg Q (xiGaussianHalfHeat t)))
  dsimp only [Q] at h
  rwa [xiPolynomialGaussianHeatTraceReal_rangeSum t.property] at h

/-- The complete three-by-three form has an absolute bound with the degree-four envelope. -/
theorem abs_xiHeatThirdQuadratic_le_gap (a b c : ℝ) (t : {t : ℝ // 0 < t}) :
    |xiHeatThirdQuadratic a b c t| ≤ xiGaussianGapCancellationBudget 4 t *
      routeUPolynomialGaussianMass (xiHeatThirdPolynomial a b c) (xiGaussianHalfHeat t) := by
  have hd : (xiHeatThirdPolynomial a b c).natDegree ≤ 2 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le
      · simp only [Polynomial.natDegree_C]; omega
      · have h := Polynomial.natDegree_C_mul_X_pow_le b 1
        simp only [pow_one] at h
        omega
    · exact Polynomial.natDegree_C_mul_X_pow_le c 2
  have h := (abs_xiPolynomialGaussianHeatTraceReal_le_gap (xiHeatThirdPolynomial a b c) t).trans
    (mul_le_mul_of_nonneg_right (xiGaussianGapCancellationBudget_mono t
      (show 2 * (xiHeatThirdPolynomial a b c).natDegree ≤ 4 by omega))
      (routeUPolynomialGaussianMass_nonneg (xiHeatThirdPolynomial a b c) (xiGaussianHalfHeat t)))
  have heq := xiHeatThirdQuadratic_eq_trace a b c (Real.log (t : ℝ))
  rw [Real.exp_log t.property] at heq
  rwa [heq]

/-- Prime, polar, and Gamma terms cancel to the explicit full-mass exponential envelope. -/
theorem abs_routeUPolynomialGaussianPrimeSource_sub_polarGamma_le_gap
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    |(routeUPolynomialGaussianPrimeSource Q t).re -
        2 * π * (Q.eval (-(1 / 4 : ℝ))) ^ 2 * Real.exp ((t : ℝ) / 4) -
        (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t x‖ * gammaHardyPhaseRate x)| ≤
      π * xiGaussianGapCancellationBudget (2 * Q.natDegree) t *
        routeUPolynomialGaussianMass Q (xiGaussianHalfHeat t) := by
  have heq := pi_mul_xiPolynomialGaussianHeatTraceReal_eq_primeGamma Q t
  have hid : (routeUPolynomialGaussianPrimeSource Q t).re -
        2 * π * (Q.eval (-(1 / 4 : ℝ))) ^ 2 * Real.exp ((t : ℝ) / 4) -
        (∫ x : ℝ, ‖routeUPolynomialGaussianDensity Q t x‖ * gammaHardyPhaseRate x) =
      -(π * xiPolynomialGaussianHeatTraceReal Q t) := by linarith only [heq]
  rw [hid, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (abs_xiPolynomialGaussianHeatTraceReal_le_gap Q t) Real.pi_pos.le

end RHTower

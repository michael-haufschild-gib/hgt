import GaloisForLFunctions.RHTower.PrimeArchEndpointCalibratedHausdorffRH
import GaloisForLFunctions.RHTower.XiEndpointOffLineQuartetHeightGap
import GaloisForLFunctions.RHTower.XiOffLineQuartetThermalOrientationBound
import GaloisForLFunctions.RHTower.AnchorTilt

/-!
# Scaled Hausdorff differences as exact Xi-divisor polynomial values

Every real polynomial pairing against the normalized prime--Gamma moment sequence is the real
part of the corresponding reciprocal-square Xi-divisor sum.  For the endpoint-calibrated
Hausdorff basis this gives

\`D_R(k,r) = Re sum_q lambda_q^(k+1) (R-lambda_q)^r\`.

The completed endpoint law, four-copy off-line charge, and transverse-orientation estimate then
prove every calibrated difference in the rectangle `k ≤ 13`, `r ≤ 43` unconditionally.  The key
point is that the arguments of `lambda` and `R - lambda` have opposite signs, so their combined
phase is bounded by the larger phase rather than their sum.  The full all-degree family remains
equivalent to RH and to the prime--polar absolute-abscissa endpoint.
-/

open scoped BigOperators Polynomial
open Polynomial Filter Topology

namespace RHTower
noncomputable section
open HTGeometry

def xiCentralPolynomialMomentTerm (p : Polynomial ℝ) (q : XiZeroCopy) : ℂ :=
  xiZeroCopyReciprocalSquare q *
    evalRealPolynomial p (xiZeroCopyReciprocalSquare q)

def xiCentralPolynomialMoment (p : Polynomial ℝ) : ℂ :=
  ∑' q : XiZeroCopy, xiCentralPolynomialMomentTerm p q

theorem summable_xiCentralPolynomialMomentTerm (p : Polynomial ℝ) :
    Summable (xiCentralPolynomialMomentTerm p) := by
  classical
  let lam : XiZeroCopy → ℂ := xiZeroCopyReciprocalSquare
  let pc : Polynomial ℂ := p.map (algebraMap ℝ ℂ)
  let moment : ℕ → XiZeroCopy → ℂ := fun k q => lam q ^ (k + 1)
  have hmoment (k : ℕ) : Summable (moment k) := by
    simpa only [lam, moment] using summable_xiZeroCopyReciprocalSquare_pow k
  have hfin : ∀ s : Finset ℕ,
      Summable (fun q : XiZeroCopy => ∑ k ∈ s, pc.coeff k * moment k q) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hks ih =>
        simpa only [Finset.sum_insert hks] using
          ((hmoment k).mul_left (pc.coeff k)).add ih
  have hsum := hfin (Finset.range (pc.natDegree + 1))
  apply hsum.congr
  intro q
  symm
  rw [xiCentralPolynomialMomentTerm]
  change lam q * evalRealPolynomial p (lam q) = _
  calc
    lam q * evalRealPolynomial p (lam q) = lam q * pc.eval (lam q) := by
      simp [pc, evalRealPolynomial]
    _ = lam q * (∑ k ∈ Finset.range (pc.natDegree + 1),
        pc.coeff k * lam q ^ k) := by rw [Polynomial.eval_eq_sum_range]
    _ = ∑ k ∈ Finset.range (pc.natDegree + 1), pc.coeff k * moment k q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [moment]
      ring

theorem xiCentralPolynomialMoment_eq_moment_sum (p : Polynomial ℝ) :
    xiCentralPolynomialMoment p =
      ∑ k ∈ Finset.range ((p.map (algebraMap ℝ ℂ)).natDegree + 1),
        (p.map (algebraMap ℝ ℂ)).coeff k * xiCentralReciprocalMoment k := by
  let lam : XiZeroCopy → ℂ := xiZeroCopyReciprocalSquare
  let pc : Polynomial ℂ := p.map (algebraMap ℝ ℂ)
  let moment : ℕ → XiZeroCopy → ℂ := fun k q => lam q ^ (k + 1)
  have hmoment (k : ℕ) : Summable (moment k) := by
    simpa only [lam, moment] using summable_xiZeroCopyReciprocalSquare_pow k
  rw [xiCentralPolynomialMoment]
  calc
    (∑' q, xiCentralPolynomialMomentTerm p q) =
        ∑' q, ∑ k ∈ Finset.range (pc.natDegree + 1),
          pc.coeff k * moment k q := by
      apply tsum_congr
      intro q
      rw [xiCentralPolynomialMomentTerm]
      change lam q * evalRealPolynomial p (lam q) = _
      calc
        lam q * evalRealPolynomial p (lam q) = lam q * pc.eval (lam q) := by
          simp [pc, evalRealPolynomial]
        _ = lam q * (∑ k ∈ Finset.range (pc.natDegree + 1),
            pc.coeff k * lam q ^ k) := by rw [Polynomial.eval_eq_sum_range]
        _ = ∑ k ∈ Finset.range (pc.natDegree + 1),
            pc.coeff k * moment k q := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          simp only [moment]
          ring
    _ = ∑ k ∈ Finset.range (pc.natDegree + 1),
        pc.coeff k * ∑' q, moment k q := by
      rw [Summable.tsum_finsetSum (fun k _ => (hmoment k).mul_left (pc.coeff k))]
      apply Finset.sum_congr rfl
      intro k hk
      rw [tsum_mul_left]
    _ = _ := by
      simp only [pc, moment, lam, tsum_xiZeroCopyReciprocalSquare_pow]

theorem normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment (n : ℕ) :
    normalizedPrimeArchMoment n = (xiCentralReciprocalMoment n).re := by
  have h := primeArchSourceMoment_eq_xiCentralReciprocalMoment n
  simpa [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm] using
    congrArg Complex.re h

theorem xiCentralPolynomialMoment_eq_sourceMomentFunctional (p : Polynomial ℝ) :
    xiCentralPolynomialMoment p =
      (HTGeometry.momentFunctional normalizedPrimeArchMoment p : ℂ) := by
  rw [xiCentralPolynomialMoment_eq_moment_sum]
  rw [Polynomial.natDegree_map_eq_of_injective
    (RingHom.injective (algebraMap ℝ ℂ))]
  have hrange : HTGeometry.momentFunctional normalizedPrimeArchMoment p =
      ∑ k ∈ Finset.range (p.natDegree + 1),
        p.coeff k * normalizedPrimeArchMoment k := by
    rw [HTGeometry.momentFunctional]
    exact p.sum_over_range
      (f := fun k c => c * normalizedPrimeArchMoment k) (by simp)
  rw [hrange]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.coeff_map]
  rw [normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment]
  have him := xiCentralReciprocalMoment_im_eq_zero k
  apply Complex.ext <;> simp [him]

theorem scaledHausdorffMomentDifference_eq_momentFunctional
    (R : ℝ) (m : ℕ → ℝ) (k r : ℕ) :
    scaledHausdorffMomentDifference R m k r =
      HTGeometry.momentFunctional m
        ((Polynomial.X : Polynomial ℝ) ^ k *
          (Polynomial.C R - Polynomial.X) ^ r) := by
  induction r generalizing k with
  | zero => simp [scaledHausdorffMomentDifference, HTGeometry.momentFunctional_X_pow]
  | succ r ih =>
      rw [scaledHausdorffMomentDifference, ih k, ih (k + 1),
        ← HTGeometry.momentFunctional_smul, ← HTGeometry.momentFunctional_sub]
      congr 1
      rw [pow_succ, pow_succ]
      simp only [Polynomial.smul_eq_C_mul]
      ring

theorem xiCentralPolynomialMoment_scaledBasis (R : ℝ) (k r : ℕ) :
    xiCentralPolynomialMoment
        ((Polynomial.X : Polynomial ℝ) ^ k *
          (Polynomial.C R - Polynomial.X) ^ r) =
      ∑' q : XiZeroCopy,
        xiZeroCopyReciprocalSquare q ^ (k + 1) *
          ((R : ℂ) - xiZeroCopyReciprocalSquare q) ^ r := by
  apply tsum_congr
  intro q
  rw [xiCentralPolynomialMomentTerm]
  simp [evalRealPolynomial]
  ring

theorem summable_xiCentralScaledHausdorffTerm (R : ℝ) (k r : ℕ) :
    Summable (fun q : XiZeroCopy =>
      xiZeroCopyReciprocalSquare q ^ (k + 1) *
        ((R : ℂ) - xiZeroCopyReciprocalSquare q) ^ r) := by
  let p : Polynomial ℝ :=
    Polynomial.X ^ k * (Polynomial.C R - Polynomial.X) ^ r
  apply (summable_xiCentralPolynomialMomentTerm p).congr
  intro q
  dsimp only [p]
  rw [xiCentralPolynomialMomentTerm]
  simp [evalRealPolynomial]
  ring

theorem scaledHausdorffMomentDifference_eq_re_xiCentralSum
    (R : ℝ) (k r : ℕ) :
    scaledHausdorffMomentDifference R normalizedPrimeArchMoment k r =
      (∑' q : XiZeroCopy,
        xiZeroCopyReciprocalSquare q ^ (k + 1) *
          ((R : ℂ) - xiZeroCopyReciprocalSquare q) ^ r).re := by
  rw [← xiCentralPolynomialMoment_scaledBasis]
  rw [scaledHausdorffMomentDifference_eq_momentFunctional]
  exact (congrArg Complex.re
    (xiCentralPolynomialMoment_eq_sourceMomentFunctional
      (Polynomial.X ^ k * (Polynomial.C R - Polynomial.X) ^ r))).symm

theorem xiZeroCopyReciprocalSquare_norm_le_offLineEndpointRadius
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ‖xiZeroCopyReciprocalSquare q‖ ≤
      xiEndpointCompletedCurvature / (4 - xiEndpointCompletedCurvature) := by
  let C := xiEndpointCompletedCurvature
  have hC : 0 < C := xiEndpointCompletedCurvature_pos
  have hC4 : 0 < 4 - C := by
    nlinarith [xiEndpointCompletedCurvature_lt_one]
  have hheight := four_le_curvature_mul_one_add_im_sq_of_offLine q hoff
  change 4 ≤ C * ((q.1 : ℂ).im ^ 2 + 1) at hheight
  have hspec : (4 - C) / C ≤ ‖xiSpectralPoint q‖ ^ 2 := by
    rw [norm_xiSpectralPoint, Complex.sq_norm, Complex.normSq_apply]
    norm_num
    have heq : (4 - C) / C = 4 / C - 1 := by field_simp [hC.ne']
    rw [heq]
    have hgamma : 4 / C - 1 ≤ (q.1 : ℂ).im ^ 2 := by
      rw [← heq, div_le_iff₀ hC]
      nlinarith
    nlinarith [sq_nonneg ((q.1 : ℂ).re - 1 / 2)]
  have hspecpos : 0 < ‖xiSpectralPoint q‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q))
  rw [xiZeroCopyReciprocalSquare, norm_pow, norm_inv, inv_pow]
  have hbasepos : 0 < (4 - C) / C := div_pos hC4 hC
  have hradius : C / (4 - C) = ((4 - C) / C)⁻¹ := by
    field_simp [hC.ne', hC4.ne']
  rw [hradius]
  exact (inv_le_inv₀ hspecpos hbasepos).2 hspec

theorem xiThermalNode_le_one_third_endpointRadius_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    xiThermalNode q ≤ (1 / 3 : ℝ) * primeArchEndpointHausdorffRadius := by
  let C := xiEndpointCompletedCurvature
  have hC : 0 < C := xiEndpointCompletedCurvature_pos
  have hC1 : 0 < 1 - C := sub_pos.mpr xiEndpointCompletedCurvature_lt_one
  have hC4 : 0 < 4 - C := by
    nlinarith [xiEndpointCompletedCurvature_lt_one]
  have hnodeNorm : xiThermalNode q ≤ ‖xiZeroCopyReciprocalSquare q‖ := by
    calc
      xiThermalNode q ≤ |xiThermalNode q| := le_abs_self _
      _ ≤ ‖xiZeroCopyReciprocalSquare q‖ :=
        Complex.abs_re_le_norm (xiZeroCopyReciprocalSquare q)
  have hnorm := xiZeroCopyReciprocalSquare_norm_le_offLineEndpointRadius q hoff
  have hratio : C / (4 - C) ≤ (1 / 3 : ℝ) * (C / (1 - C)) := by
    rw [div_le_iff₀ hC4]
    rw [show (1 / 3 : ℝ) * (C / (1 - C)) * (4 - C) =
        (C * (4 - C)) / (3 * (1 - C)) by
          field_simp [hC1.ne']]
    rw [le_div_iff₀ (mul_pos (by norm_num) hC1)]
    nlinarith
  exact hnodeNorm.trans (hnorm.trans (by
    simpa only [C, primeArchEndpointHausdorffRadius] using hratio))

/-- An off-critical reciprocal-square node lies strictly inside the quarter-radius disk set by the
prime--archimedean Hausdorff endpoint. -/
theorem xiThermalNode_lt_one_fourth_endpointRadius_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    xiThermalNode q < (1 / 4 : ℝ) * primeArchEndpointHausdorffRadius := by
  let C := xiEndpointCompletedCurvature
  have hC : 0 < C := xiEndpointCompletedCurvature_pos
  have hC1 : 0 < 1 - C := sub_pos.mpr xiEndpointCompletedCurvature_lt_one
  have hC4 : 0 < 4 - C := by
    nlinarith [xiEndpointCompletedCurvature_lt_one]
  have hden : 0 < 4 * (1 - C) := mul_pos (by norm_num) hC1
  have hnodeNorm : xiThermalNode q ≤ ‖xiZeroCopyReciprocalSquare q‖ := by
    calc
      xiThermalNode q ≤ |xiThermalNode q| := le_abs_self _
      _ ≤ ‖xiZeroCopyReciprocalSquare q‖ :=
        Complex.abs_re_le_norm (xiZeroCopyReciprocalSquare q)
  have hnorm := xiZeroCopyReciprocalSquare_norm_le_offLineEndpointRadius q hoff
  have hratio : C / (4 - C) < (1 / 4 : ℝ) * (C / (1 - C)) := by
    calc
      C / (4 - C) < C / (4 * (1 - C)) := by
        rw [div_lt_div_iff₀ hC4 hden]
        nlinarith
      _ = (1 / 4 : ℝ) * (C / (1 - C)) := by
        field_simp [hC1.ne']
  exact lt_of_le_of_lt (hnodeNorm.trans hnorm) (by
    simpa only [C, primeArchEndpointHausdorffRadius] using hratio)

theorem re_xiCentral_endpointComplement_nonneg (q : XiZeroCopy) :
    0 ≤ (xiZeroCopyReciprocalSquare q *
      ((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q)).re := by
  let z := xiZeroCopyReciprocalSquare q
  let R := primeArchEndpointHausdorffRadius
  have ha : 0 ≤ z.re := by
    simpa only [z, xiThermalNode] using (xiThermalNode_pos q).le
  have haR : z.re ≤ R := by
    simpa only [z, R, xiThermalNode] using
      xiThermalNode_le_primeArchEndpointHausdorffRadius q
  have hformula : (z * ((R : ℂ) - z)).re =
      z.re * (R - z.re) + z.im ^ 2 := by
    simp [Complex.mul_re, pow_two]
  rw [hformula]
  exact add_nonneg (mul_nonneg ha (sub_nonneg.mpr haR)) (sq_nonneg _)

theorem re_xiCentral_endpointComplement_sq_nonneg (q : XiZeroCopy) :
    0 ≤ (xiZeroCopyReciprocalSquare q *
      ((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q) ^ 2).re := by
  let z := xiZeroCopyReciprocalSquare q
  let R := primeArchEndpointHausdorffRadius
  have ha : 0 ≤ z.re := by
    simpa only [z, xiThermalNode] using (xiThermalNode_pos q).le
  have haR : z.re ≤ R := by
    simpa only [z, R, xiThermalNode] using
      xiThermalNode_le_primeArchEndpointHausdorffRadius q
  have hformula : (z * ((R : ℂ) - z) ^ 2).re =
      z.re * (R - z.re) ^ 2 + z.im ^ 2 * (2 * R - 3 * z.re) := by
    simp [Complex.mul_re, pow_two]
    ring
  rw [hformula]
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have him : z.im = 0 := by
      dsimp only [z]
      rw [xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    rw [him]
    norm_num
    exact mul_nonneg ha (sq_nonneg _)
  · have hthirds := xiThermalNode_le_one_third_endpointRadius_of_offLine q hon
    have hcoef : 0 ≤ 2 * R - 3 * z.re := by
      dsimp only [z, R] at hthirds ⊢
      rw [xiThermalNode] at hthirds
      nlinarith
    exact add_nonneg (mul_nonneg ha (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) hcoef)

theorem re_xiCentral_cube_nonneg (q : XiZeroCopy) :
    0 ≤ (xiZeroCopyReciprocalSquare q ^ 3).re := by
  let z := xiZeroCopyReciprocalSquare q
  have ha : 0 ≤ z.re := by
    simpa only [z, xiThermalNode] using (xiThermalNode_pos q).le
  have hb : z.im ^ 2 ≤ (1 / 84 : ℝ) * z.re ^ 2 := by
    simpa only [z, xiThermalNode] using
      xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q
  have hformula : (z ^ 3).re = z.re * (z.re ^ 2 - 3 * z.im ^ 2) := by
    simp [pow_succ, Complex.mul_re]
    ring
  rw [hformula]
  exact mul_nonneg ha (by nlinarith)

theorem re_xiCentral_fourthPower_nonneg (q : XiZeroCopy) :
    0 ≤ (xiZeroCopyReciprocalSquare q ^ 4).re := by
  let z := xiZeroCopyReciprocalSquare q
  have hb : z.im ^ 2 ≤ (1 / 84 : ℝ) * z.re ^ 2 := by
    simpa only [z, xiThermalNode] using
      xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q
  have hscaled : z.re ^ 2 * z.im ^ 2 ≤
      z.re ^ 2 * ((1 / 84 : ℝ) * z.re ^ 2) :=
    mul_le_mul_of_nonneg_left hb (sq_nonneg z.re)
  have hformula : (z ^ 4).re =
      z.re ^ 4 - 6 * z.re ^ 2 * z.im ^ 2 + z.im ^ 4 := by
    simp [pow_succ, Complex.mul_re]
    ring
  rw [hformula]
  nlinarith [sq_nonneg (z.im ^ 2), sq_nonneg (z.re ^ 2)]

theorem re_xiCentral_sq_mul_endpointComplement_nonneg (q : XiZeroCopy) :
    0 ≤ (xiZeroCopyReciprocalSquare q ^ 2 *
      ((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q)).re := by
  let z := xiZeroCopyReciprocalSquare q
  let R := primeArchEndpointHausdorffRadius
  have hR : 0 < R := primeArchEndpointHausdorffRadius_pos
  have ha : 0 ≤ z.re := by
    simpa only [z, xiThermalNode] using (xiThermalNode_pos q).le
  have hb0 : 0 ≤ z.im ^ 2 := sq_nonneg _
  have hb : z.im ^ 2 ≤ (1 / 84 : ℝ) * z.re ^ 2 := by
    simpa only [z, xiThermalNode] using
      xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q
  have hformula : (z ^ 2 * ((R : ℂ) - z)).re =
      z.re ^ 2 * (R - z.re) + z.im ^ 2 * (3 * z.re - R) := by
    simp [Complex.mul_re, pow_two]
    ring
  rw [hformula]
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have him : z.im = 0 := by
      dsimp only [z]
      rw [xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    rw [him]
    norm_num
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (by
      simpa only [z, R, xiThermalNode] using
        xiThermalNode_le_primeArchEndpointHausdorffRadius q))
  · have haThird := xiThermalNode_le_one_third_endpointRadius_of_offLine q hon
    have haThird' : z.re ≤ (1 / 3 : ℝ) * R := by
      simpa only [z, R, xiThermalNode] using haThird
    have hu : (2 / 3 : ℝ) * R ≤ R - z.re := by nlinarith
    have hmain : (2 / 3 : ℝ) * (z.re ^ 2 * R) ≤
        z.re ^ 2 * (R - z.re) := by
      nlinarith [mul_le_mul_of_nonneg_left hu (sq_nonneg z.re)]
    have hneg : z.im ^ 2 * (R - 3 * z.re) ≤ z.im ^ 2 * R := by
      exact mul_le_mul_of_nonneg_left (by nlinarith) hb0
    have hbR : z.im ^ 2 * R ≤ (1 / 84 : ℝ) * z.re ^ 2 * R := by
      exact mul_le_mul_of_nonneg_right hb hR.le
    nlinarith [sq_nonneg z.re, mul_nonneg (sq_nonneg z.re) hR.le]

theorem re_xiCentral_endpointComplement_cube_nonneg (q : XiZeroCopy) :
    0 ≤ (xiZeroCopyReciprocalSquare q *
      ((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q) ^ 3).re := by
  let z := xiZeroCopyReciprocalSquare q
  let R := primeArchEndpointHausdorffRadius
  have ha : 0 ≤ z.re := by
    simpa only [z, xiThermalNode] using (xiThermalNode_pos q).le
  have hb0 : 0 ≤ z.im ^ 2 := sq_nonneg _
  have hb : z.im ^ 2 ≤ (1 / 84 : ℝ) * z.re ^ 2 := by
    simpa only [z, xiThermalNode] using
      xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q
  have hformula : (z * ((R : ℂ) - z) ^ 3).re =
      z.re * (R - z.re) ^ 3 +
        3 * (R - z.re) * (R - 2 * z.re) * z.im ^ 2 - z.im ^ 4 := by
    simp [Complex.mul_re, pow_succ]
    ring
  rw [hformula]
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have him : z.im = 0 := by
      dsimp only [z]
      rw [xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    rw [him]
    norm_num
    exact mul_nonneg ha (pow_nonneg (by
      simpa only [z, R, xiThermalNode] using
        sub_nonneg.mpr (xiThermalNode_le_primeArchEndpointHausdorffRadius q)) 3)
  · have haThird := xiThermalNode_le_one_third_endpointRadius_of_offLine q hon
    have haThird' : z.re ≤ (1 / 3 : ℝ) * R := by
      simpa only [z, R, xiThermalNode] using haThird
    have hau : z.re ≤ R - z.re := by nlinarith
    have hpow : z.re ^ 3 ≤ (R - z.re) ^ 3 :=
      pow_le_pow_left₀ ha (by nlinarith) 3
    have hb' : z.im ^ 2 ≤ z.re ^ 2 := by nlinarith
    have hb4 : z.im ^ 4 ≤ z.re ^ 4 := by
      have hs := pow_le_pow_left₀ hb0 hb' 2
      nlinarith
    have ha4 : z.re ^ 4 ≤ z.re * (R - z.re) ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hpow ha]
    have hmiddle : 0 ≤
        3 * (R - z.re) * (R - 2 * z.re) * z.im ^ 2 := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (by nlinarith)) (by nlinarith)) hb0
    nlinarith

theorem re_xiCentral_sq_mul_endpointComplement_sq_nonneg (q : XiZeroCopy) :
    0 ≤ (xiZeroCopyReciprocalSquare q ^ 2 *
      ((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q) ^ 2).re := by
  let z := xiZeroCopyReciprocalSquare q
  let R := primeArchEndpointHausdorffRadius
  have ha : 0 ≤ z.re := by
    simpa only [z, xiThermalNode] using (xiThermalNode_pos q).le
  have hb0 : 0 ≤ z.im ^ 2 := sq_nonneg _
  have hb : z.im ^ 2 ≤ (1 / 84 : ℝ) * z.re ^ 2 := by
    simpa only [z, xiThermalNode] using
      xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q
  have hformula : (z ^ 2 * ((R : ℂ) - z) ^ 2).re =
      (z.re * (R - z.re) + z.im ^ 2) ^ 2 -
        z.im ^ 2 * (R - 2 * z.re) ^ 2 := by
    simp [Complex.mul_re, pow_two]
    ring
  rw [hformula]
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have him : z.im = 0 := by
      dsimp only [z]
      rw [xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    rw [him]
    norm_num
    exact sq_nonneg _
  · have haThird := xiThermalNode_le_one_third_endpointRadius_of_offLine q hon
    have haThird' : z.re ≤ (1 / 3 : ℝ) * R := by
      simpa only [z, R, xiThermalNode] using haThird
    have hRu0 : 0 ≤ R - z.re := by nlinarith
    have hR2a0 : 0 ≤ R - 2 * z.re := by nlinarith
    have hside : (R - 2 * z.re) ^ 2 ≤ (R - z.re) ^ 2 :=
      pow_le_pow_left₀ hR2a0 (by nlinarith) 2
    have hb' : z.im ^ 2 ≤ z.re ^ 2 := by nlinarith
    have hprod : z.im ^ 2 * (R - 2 * z.re) ^ 2 ≤
        z.re ^ 2 * (R - z.re) ^ 2 := by
      calc
        z.im ^ 2 * (R - 2 * z.re) ^ 2 ≤
            z.im ^ 2 * (R - z.re) ^ 2 :=
          mul_le_mul_of_nonneg_left hside hb0
        _ ≤ z.re ^ 2 * (R - z.re) ^ 2 :=
          mul_le_mul_of_nonneg_right hb' (sq_nonneg _)
    have hbase : 0 ≤ z.re * (R - z.re) := mul_nonneg ha hRu0
    nlinarith [sq_nonneg (z.re * (R - z.re)),
      mul_nonneg hbase hb0]

theorem re_xiCentral_cube_mul_endpointComplement_nonneg (q : XiZeroCopy) :
    0 ≤ (xiZeroCopyReciprocalSquare q ^ 3 *
      ((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q)).re := by
  let z := xiZeroCopyReciprocalSquare q
  let R := primeArchEndpointHausdorffRadius
  have hR : 0 < R := primeArchEndpointHausdorffRadius_pos
  have ha : 0 ≤ z.re := by
    simpa only [z, xiThermalNode] using (xiThermalNode_pos q).le
  have hb0 : 0 ≤ z.im ^ 2 := sq_nonneg _
  have hb : z.im ^ 2 ≤ (1 / 84 : ℝ) * z.re ^ 2 := by
    simpa only [z, xiThermalNode] using
      xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q
  have hformula : (z ^ 3 * ((R : ℂ) - z)).re =
      z.re ^ 3 * (R - z.re) -
        3 * z.re * (R - 2 * z.re) * z.im ^ 2 - z.im ^ 4 := by
    simp [Complex.mul_re, pow_succ]
    ring
  rw [hformula]
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have him : z.im = 0 := by
      dsimp only [z]
      rw [xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    rw [him]
    norm_num
    exact mul_nonneg (pow_nonneg ha 3) (sub_nonneg.mpr (by
      simpa only [z, R, xiThermalNode] using
        xiThermalNode_le_primeArchEndpointHausdorffRadius q))
  · have haThird := xiThermalNode_le_one_third_endpointRadius_of_offLine q hon
    have haThird' : z.re ≤ (1 / 3 : ℝ) * R := by
      simpa only [z, R, xiThermalNode] using haThird
    have hmain : (2 / 3 : ℝ) * (z.re ^ 3 * R) ≤
        z.re ^ 3 * (R - z.re) := by
      have hu : (2 / 3 : ℝ) * R ≤ R - z.re := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hu (pow_nonneg ha 3)]
    have hnegOne :
        3 * z.re * (R - 2 * z.re) * z.im ^ 2 ≤
          (1 / 28 : ℝ) * (z.re ^ 3 * R) := by
      have hfirst : 3 * z.re * (R - 2 * z.re) * z.im ^ 2 ≤
          3 * z.re * R * z.im ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg (by norm_num) ha)) hb0
      have hsecond : 3 * z.re * R * z.im ^ 2 ≤
          3 * z.re * R * ((1 / 84 : ℝ) * z.re ^ 2) :=
        mul_le_mul_of_nonneg_left hb
          (mul_nonneg (mul_nonneg (by norm_num) ha) hR.le)
      nlinarith
    have hb' : z.im ^ 2 ≤ z.re ^ 2 := by nlinarith
    have hb4 : z.im ^ 4 ≤ z.re ^ 4 := by
      have hs := pow_le_pow_left₀ hb0 hb' 2
      nlinarith
    have ha4 : z.re ^ 4 ≤ (1 / 3 : ℝ) * (z.re ^ 3 * R) := by
      nlinarith [mul_le_mul_of_nonneg_left haThird' (pow_nonneg ha 3)]
    nlinarith

theorem scaledPrimeArchEndpointHausdorffDifference_zero_one_nonnegative :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment 0 1 := by
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum,
    Complex.re_tsum (summable_xiCentralScaledHausdorffTerm
      primeArchEndpointHausdorffRadius 0 1)]
  apply tsum_nonneg
  intro q
  simpa using re_xiCentral_endpointComplement_nonneg q

theorem scaledPrimeArchEndpointHausdorffDifference_zero_two_nonnegative :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment 0 2 := by
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum,
    Complex.re_tsum (summable_xiCentralScaledHausdorffTerm
      primeArchEndpointHausdorffRadius 0 2)]
  apply tsum_nonneg
  intro q
  simpa using re_xiCentral_endpointComplement_sq_nonneg q

theorem scaledPrimeArchEndpointHausdorffDifference_two_zero_nonnegative :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment 2 0 := by
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum,
    Complex.re_tsum (summable_xiCentralScaledHausdorffTerm
      primeArchEndpointHausdorffRadius 2 0)]
  apply tsum_nonneg
  intro q
  simpa using re_xiCentral_cube_nonneg q

theorem scaledPrimeArchEndpointHausdorffDifference_one_one_nonnegative :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment 1 1 := by
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum,
    Complex.re_tsum (summable_xiCentralScaledHausdorffTerm
      primeArchEndpointHausdorffRadius 1 1)]
  apply tsum_nonneg
  intro q
  simpa using re_xiCentral_sq_mul_endpointComplement_nonneg q

theorem scaledPrimeArchEndpointHausdorffDifference_zero_three_nonnegative :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment 0 3 := by
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum,
    Complex.re_tsum (summable_xiCentralScaledHausdorffTerm
      primeArchEndpointHausdorffRadius 0 3)]
  apply tsum_nonneg
  intro q
  simpa using re_xiCentral_endpointComplement_cube_nonneg q

theorem scaledPrimeArchEndpointHausdorffDifference_three_zero_nonnegative :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment 3 0 := by
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum,
    Complex.re_tsum (summable_xiCentralScaledHausdorffTerm
      primeArchEndpointHausdorffRadius 3 0)]
  apply tsum_nonneg
  intro q
  simpa using re_xiCentral_fourthPower_nonneg q

theorem scaledPrimeArchEndpointHausdorffDifference_one_two_nonnegative :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment 1 2 := by
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum,
    Complex.re_tsum (summable_xiCentralScaledHausdorffTerm
      primeArchEndpointHausdorffRadius 1 2)]
  apply tsum_nonneg
  intro q
  simpa using re_xiCentral_sq_mul_endpointComplement_sq_nonneg q

theorem scaledPrimeArchEndpointHausdorffDifference_two_one_nonnegative :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment 2 1 := by
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum,
    Complex.re_tsum (summable_xiCentralScaledHausdorffTerm
      primeArchEndpointHausdorffRadius 2 1)]
  apply tsum_nonneg
  intro q
  simpa using re_xiCentral_cube_mul_endpointComplement_nonneg q

theorem scaledPrimeArchEndpointHausdorffDifference_zero_zero_nonnegative :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment 0 0 := by
  simpa only [scaledHausdorffMomentDifference] using
    normalizedPrimeArchMoment_zero_pos.le

theorem scaledPrimeArchEndpointHausdorffDifference_one_zero_nonnegative :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment 1 0 := by
  simpa only [scaledHausdorffMomentDifference] using
    normalizedPrimeArchMoment_one_pos.le

theorem scaledPrimeArchEndpointHausdorffDifference_totalDegree_le_three_nonnegative
    (k r : ℕ) (hdegree : k + r ≤ 3) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r := by
  have hk : k ≤ 3 := by omega
  have hr : r ≤ 3 := by omega
  interval_cases k <;> interval_cases r
  all_goals first
    | exact scaledPrimeArchEndpointHausdorffDifference_zero_zero_nonnegative
    | exact scaledPrimeArchEndpointHausdorffDifference_one_zero_nonnegative
    | exact scaledPrimeArchEndpointHausdorffDifference_two_zero_nonnegative
    | exact scaledPrimeArchEndpointHausdorffDifference_three_zero_nonnegative
    | exact scaledPrimeArchEndpointHausdorffDifference_zero_one_nonnegative
    | exact scaledPrimeArchEndpointHausdorffDifference_one_one_nonnegative
    | exact scaledPrimeArchEndpointHausdorffDifference_two_one_nonnegative
    | exact scaledPrimeArchEndpointHausdorffDifference_zero_two_nonnegative
    | exact scaledPrimeArchEndpointHausdorffDifference_one_two_nonnegative
    | exact scaledPrimeArchEndpointHausdorffDifference_zero_three_nonnegative
    | omega

/-! ### Uniform asymmetric-sector positivity on a 301-condition weighted wedge -/

theorem abs_arctan_le_abs_for_scaledHausdorff (x : ℝ) :
    |Real.arctan x| ≤ |x| := by
  have key : ∀ y : ℝ, 0 ≤ y → Real.arctan y ≤ y := by
    intro y hy
    rcases eq_or_lt_of_le hy with h | h
    · rw [← h, Real.arctan_zero]
    · exact (lt_of_lt_of_eq
        (Real.lt_tan (Real.arctan_pos.mpr h) (Real.arctan_lt_pi_div_two y))
        (Real.tan_arctan y)).le
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, abs_of_nonneg]
    · exact key x hx
    · rcases eq_or_lt_of_le hx with h | h
      · rw [← h, Real.arctan_zero]
      · exact (Real.arctan_pos.mpr h).le
  · have hx' : 0 ≤ -x := le_of_lt (neg_pos.mpr (lt_of_not_ge hx))
    have hatan : 0 ≤ Real.arctan (-x) := Real.arctan_nonneg.mpr hx'
    calc
      |Real.arctan x| = |Real.arctan (-x)| := by rw [Real.arctan_neg, abs_neg]
      _ ≤ |-x| := by
        simpa only [abs_of_nonneg hatan, abs_of_nonneg hx'] using key (-x) hx'
      _ = |x| := abs_neg x

theorem abs_arg_le_of_re_pos_for_scaledHausdorff {z : ℂ} (hz : 0 < z.re)
    {c : ℝ} (hc : |z.im| ≤ c * z.re) :
    |z.arg| ≤ c := by
  rw [arg_eq_arctan_of_re_pos hz]
  refine (abs_arctan_le_abs_for_scaledHausdorff _).trans ?_
  rw [abs_div, abs_of_pos hz]
  exact (div_le_iff₀ hz).2 (by simpa [mul_comm] using hc)

theorem pow_mul_pow_re_eq_norm_cos (z w : ℂ) (p r : ℕ) :
    (z ^ p * w ^ r).re =
      ‖z‖ ^ p * ‖w‖ ^ r * Real.cos (p * z.arg + r * w.arg) := by
  have hcomplex : z ^ p * w ^ r =
      ((‖z‖ ^ p * ‖w‖ ^ r : ℝ) : ℂ) *
        Complex.exp (((p * z.arg + r * w.arg : ℝ) : ℂ) * Complex.I) := by
    calc
      z ^ p * w ^ r =
          (((‖z‖ : ℝ) : ℂ) * Complex.exp ((z.arg : ℂ) * Complex.I)) ^ p *
            (((‖w‖ : ℝ) : ℂ) * Complex.exp ((w.arg : ℂ) * Complex.I)) ^ r := by
        rw [Complex.norm_mul_exp_arg_mul_I, Complex.norm_mul_exp_arg_mul_I]
      _ = (((‖z‖ : ℝ) : ℂ) ^ p * ((‖w‖ : ℝ) : ℂ) ^ r) *
            (Complex.exp ((z.arg : ℂ) * Complex.I) ^ p *
              Complex.exp ((w.arg : ℂ) * Complex.I) ^ r) := by ring
      _ = (((‖z‖ : ℝ) : ℂ) ^ p * ((‖w‖ : ℝ) : ℂ) ^ r) *
            Complex.exp ((p : ℂ) * ((z.arg : ℂ) * Complex.I) +
              (r : ℂ) * ((w.arg : ℂ) * Complex.I)) := by
        rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.exp_add]
      _ = ((‖z‖ ^ p * ‖w‖ ^ r : ℝ) : ℂ) *
            Complex.exp (((p * z.arg + r * w.arg : ℝ) : ℂ) * Complex.I) := by
        congr 1
        · norm_num
        · push_cast
          ring_nf
  rw [hcomplex, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  norm_num

private theorem nineThirteenHundred_mul_abs_im_le_re_of_square {z : ℂ}
    (hre : 0 ≤ z.re)
    (hsq : z.im ^ 2 ≤ (1 / 84 : ℝ) * z.re ^ 2) :
    (913 / 100 : ℝ) * |z.im| ≤ z.re := by
  apply (sq_le_sq₀ (mul_nonneg (by norm_num) (abs_nonneg _)) hre).mp
  rw [mul_pow, sq_abs]
  nlinarith

private theorem re_pow_mul_pow_nonneg_of_rational_asymmetric_sector
    (z w : ℂ) (p r : ℕ)
    (hzre : 0 < z.re) (hwre : 0 < w.re)
    (hzsector : (913 / 100 : ℝ) * |z.im| ≤ z.re)
    (hwsector : (2739 / 100 : ℝ) * |w.im| ≤ w.re)
    (hweight : 3 * p + r ≤ 43) :
    0 ≤ (z ^ p * w ^ r).re := by
  have hzarg : |z.arg| ≤ (100 / 913 : ℝ) :=
    abs_arg_le_of_re_pos_for_scaledHausdorff hzre (by nlinarith)
  have hwarg : |w.arg| ≤ (100 / 2739 : ℝ) :=
    abs_arg_le_of_re_pos_for_scaledHausdorff hwre (by nlinarith)
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hweightR : 3 * (p : ℝ) + (r : ℝ) ≤ 43 := by exact_mod_cast hweight
  have hangle : |(p : ℝ) * z.arg + (r : ℝ) * w.arg| ≤
      (4300 / 2739 : ℝ) := by
    calc
      |(p : ℝ) * z.arg + (r : ℝ) * w.arg| ≤
          |(p : ℝ) * z.arg| + |(r : ℝ) * w.arg| := abs_add_le _ _
      _ = (p : ℝ) * |z.arg| + (r : ℝ) * |w.arg| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg hr0]
      _ ≤ (p : ℝ) * (100 / 913 : ℝ) + (r : ℝ) * (100 / 2739 : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hzarg hp0)
          (mul_le_mul_of_nonneg_left hwarg hr0)
      _ ≤ 4300 / 2739 := by nlinarith
  have hpi : (4300 / 2739 : ℝ) < Real.pi / 2 := by
    nlinarith [Real.pi_gt_d20]
  have hangleMem : (p : ℝ) * z.arg + (r : ℝ) * w.arg ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [abs_le] at hangle
    constructor <;> nlinarith
  rw [pow_mul_pow_re_eq_norm_cos]
  exact mul_nonneg
    (mul_nonneg (pow_nonneg (norm_nonneg z) p) (pow_nonneg (norm_nonneg w) r))
    (Real.cos_nonneg_of_mem_Icc hangleMem)

/-! ### Opposite-phase rectangular positivity -/

/-- If two right-half-plane factors have opposite imaginary parts, their powered arguments
partially cancel.  Hence separate half-plane bounds on the two powered arguments imply positivity;
one does not need to add the two argument budgets. -/
private theorem re_pow_mul_pow_nonneg_of_opposite_phase_rectangle
    (z w : ℂ) (p r : ℕ)
    (hzre : 0 < z.re) (hwre : 0 < w.re)
    (hwim : w.im = -z.im)
    (hzsector : (913 / 100 : ℝ) * |z.im| ≤ z.re)
    (hwsector : (2739 / 100 : ℝ) * |w.im| ≤ w.re)
    (hp : p ≤ 14) (hr : r ≤ 43) :
    0 ≤ (z ^ p * w ^ r).re := by
  have hzarg : |z.arg| ≤ (100 / 913 : ℝ) :=
    abs_arg_le_of_re_pos_for_scaledHausdorff hzre (by nlinarith)
  have hwarg : |w.arg| ≤ (100 / 2739 : ℝ) :=
    abs_arg_le_of_re_pos_for_scaledHausdorff hwre (by nlinarith)
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hpR : (p : ℝ) ≤ 14 := by exact_mod_cast hp
  have hrR : (r : ℝ) ≤ 43 := by exact_mod_cast hr
  let x : ℝ := (p : ℝ) * z.arg
  let y : ℝ := (r : ℝ) * w.arg
  let M : ℝ := 4300 / 2739
  have hx : |x| ≤ M := by
    calc
      |x| = (p : ℝ) * |z.arg| := by
        simp only [x, abs_mul, abs_of_nonneg hp0]
      _ ≤ (p : ℝ) * (100 / 913 : ℝ) :=
        mul_le_mul_of_nonneg_left hzarg hp0
      _ ≤ M := by dsimp only [M]; nlinarith
  have hy : |y| ≤ M := by
    calc
      |y| = (r : ℝ) * |w.arg| := by
        simp only [y, abs_mul, abs_of_nonneg hr0]
      _ ≤ (r : ℝ) * (100 / 2739 : ℝ) :=
        mul_le_mul_of_nonneg_left hwarg hr0
      _ ≤ M := by dsimp only [M]; nlinarith
  have hangle : |x + y| ≤ M := by
    rw [abs_le]
    have hxI := (abs_le.mp hx)
    have hyI := (abs_le.mp hy)
    by_cases hzim : 0 ≤ z.im
    · have hzarg0 : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr hzim
      have hwim0 : w.im ≤ 0 := by rw [hwim]; linarith
      have hwarg0 : w.arg ≤ 0 := by
        rw [arg_eq_arctan_of_re_pos hwre]
        have hratio : 0 ≤ -(w.im / w.re) := by
          exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hwim0 hwre.le)
        have h := Real.arctan_nonneg.mpr hratio
        rw [Real.arctan_neg] at h
        linarith
      have hx0 : 0 ≤ x := mul_nonneg hp0 hzarg0
      have hy0 : y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0 hwarg0
      constructor
      · exact hyI.1.trans (by linarith)
      · exact (by linarith : x + y ≤ x).trans hxI.2
    · have hzim0 : z.im ≤ 0 := le_of_not_ge hzim
      have hzarg0 : z.arg ≤ 0 := by
        rw [arg_eq_arctan_of_re_pos hzre]
        have hratio : 0 ≤ -(z.im / z.re) := by
          exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hzim0 hzre.le)
        have h := Real.arctan_nonneg.mpr hratio
        rw [Real.arctan_neg] at h
        linarith
      have hwim0 : 0 ≤ w.im := by rw [hwim]; linarith
      have hwarg0 : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hwim0
      have hx0 : x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0 hzarg0
      have hy0 : 0 ≤ y := mul_nonneg hr0 hwarg0
      constructor
      · exact hxI.1.trans (by linarith)
      · exact (by linarith : x + y ≤ y).trans hyI.2
  have hpi : M < Real.pi / 2 := by
    dsimp only [M]
    nlinarith [Real.pi_gt_d20]
  have hangleMem : x + y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [abs_le] at hangle
    exact ⟨(neg_le_neg hpi.le).trans hangle.1, hangle.2.trans hpi.le⟩
  change 0 ≤ (z ^ p * w ^ r).re
  rw [pow_mul_pow_re_eq_norm_cos]
  change 0 ≤ ‖z‖ ^ p * ‖w‖ ^ r * Real.cos (x + y)
  exact mul_nonneg
    (mul_nonneg (pow_nonneg (norm_nonneg z) p) (pow_nonneg (norm_nonneg w) r))
    (Real.cos_nonneg_of_mem_Icc hangleMem)

/-- Every individual reciprocal-square Xi-divisor atom is nonnegative on the full
endpoint-calibrated rectangle `k ≤ 13`, `r ≤ 43`. -/
theorem re_xiCentral_scaledBasis_rectangle_nonneg
    (q : XiZeroCopy) (k r : ℕ) (hk : k ≤ 13) (hr : r ≤ 43) :
    0 ≤ (xiZeroCopyReciprocalSquare q ^ (k + 1) *
      ((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q) ^ r).re := by
  let z := xiZeroCopyReciprocalSquare q
  let R := primeArchEndpointHausdorffRadius
  let w : ℂ := (R : ℂ) - z
  have hR : 0 < R := primeArchEndpointHausdorffRadius_pos
  have hzre : 0 < z.re := by
    simpa only [z, xiThermalNode] using xiThermalNode_pos q
  have hzre0 : 0 ≤ z.re := hzre.le
  have hsq : z.im ^ 2 ≤ (1 / 84 : ℝ) * z.re ^ 2 := by
    simpa only [z, xiThermalNode] using
      xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have him : z.im = 0 := by
      dsimp only [z]
      rw [xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    have hzReal : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    have hwReal : w = ((R - z.re : ℝ) : ℂ) := by
      dsimp only [w]
      rw [hzReal]
      norm_num
    have hzleR : z.re ≤ R := by
      simpa only [z, R, xiThermalNode] using
        xiThermalNode_le_primeArchEndpointHausdorffRadius q
    change 0 ≤ (z ^ (k + 1) * w ^ r).re
    rw [hzReal, hwReal]
    norm_cast
    exact mul_nonneg (pow_nonneg hzre0 (k + 1))
      (pow_nonneg (sub_nonneg.mpr hzleR) r)
  · have hzQuarter : z.re < (1 / 4 : ℝ) * R := by
      simpa only [z, R, xiThermalNode] using
        xiThermalNode_lt_one_fourth_endpointRadius_of_offLine q hon
    have hwre : 0 < w.re := by
      dsimp only [w]
      simp only [Complex.sub_re, Complex.ofReal_re]
      nlinarith
    have hzsector : (913 / 100 : ℝ) * |z.im| ≤ z.re :=
      nineThirteenHundred_mul_abs_im_le_re_of_square hzre0 hsq
    have hwsector : (2739 / 100 : ℝ) * |w.im| ≤ w.re := by
      dsimp only [w]
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg,
        Complex.sub_re, Complex.ofReal_re]
      nlinarith
    have hwim : w.im = -z.im := by
      dsimp only [w]
      simp
    have hp : k + 1 ≤ 14 := by omega
    change 0 ≤ (z ^ (k + 1) * w ^ r).re
    exact re_pow_mul_pow_nonneg_of_opposite_phase_rectangle z w (k + 1) r
      hzre hwre hwim hzsector hwsector hp hr

/-- The full endpoint-calibrated rectangle `k ≤ 13`, `r ≤ 43` is unconditionally nonnegative.
This is a finite family of `14 * 44 = 616` conditions inside the all-degree family equivalent to
RH. -/
theorem scaledPrimeArchEndpointHausdorffDifference_rectangle_nonnegative
    (k r : ℕ) (hk : k ≤ 13) (hr : r ≤ 43) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r := by
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum,
    Complex.re_tsum (summable_xiCentralScaledHausdorffTerm
      primeArchEndpointHausdorffRadius k r)]
  apply tsum_nonneg
  intro q
  exact re_xiCentral_scaledBasis_rectangle_nonneg q k r hk hr

/-- Compatibility corollary for the earlier 301-condition weighted wedge. -/
theorem re_xiCentral_scaledBasis_weightedDegree_le_forty_nonneg
    (q : XiZeroCopy) (k r : ℕ) (hweight : 3 * k + r ≤ 40) :
    0 ≤ (xiZeroCopyReciprocalSquare q ^ (k + 1) *
      ((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q) ^ r).re := by
  exact re_xiCentral_scaledBasis_rectangle_nonneg q k r (by omega) (by omega)

/-- Compatibility corollary for the earlier 301-condition weighted wedge. -/
theorem scaledPrimeArchEndpointHausdorffDifference_weightedDegree_le_forty_nonnegative
    (k r : ℕ) (hweight : 3 * k + r ≤ 40) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r := by
  exact scaledPrimeArchEndpointHausdorffDifference_rectangle_nonnegative
    k r (by omega) (by omega)

/-- Compatibility corollary for the earlier 196-condition weighted wedge. -/
theorem re_xiCentral_scaledBasis_weightedDegree_le_twentySix_nonneg
    (q : XiZeroCopy) (k r : ℕ) (hweight : 2 * k + r ≤ 26) :
    0 ≤ (xiZeroCopyReciprocalSquare q ^ (k + 1) *
      ((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q) ^ r).re := by
  exact re_xiCentral_scaledBasis_weightedDegree_le_forty_nonneg q k r (by omega)

/-- Compatibility corollary for the earlier 196-condition weighted wedge. -/
theorem scaledPrimeArchEndpointHausdorffDifference_weightedDegree_le_twentySix_nonnegative
    (k r : ℕ) (hweight : 2 * k + r ≤ 26) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r := by
  exact scaledPrimeArchEndpointHausdorffDifference_weightedDegree_le_forty_nonnegative
    k r (by omega)

/-- Complete endpoint-calibrated positivity is equivalent to its still-unresolved complement of
the unconditional `14 × 44` rectangle. -/
theorem scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_rectangleTailNonnegative :
    ScaledHausdorffMomentDifferencesNonnegative primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment ↔
      ∀ k r : ℕ, 13 < k ∨ 43 < r →
        0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment k r := by
  constructor
  · intro hall k r htail
    exact hall k r
  · intro htail k r
    by_cases hk : k ≤ 13
    · by_cases hr : r ≤ 43
      · exact scaledPrimeArchEndpointHausdorffDifference_rectangle_nonnegative k r hk hr
      · exact htail k r (Or.inr (by omega))
    · exact htail k r (Or.inl (by omega))

/-- **Rectangle-reduced prime--polar endpoint obligation.**  The absolute-convergence abscissa
bound is equivalent to positivity only outside the 616 conditions already discharged
unconditionally. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_rectangleHausdorffTailNonnegative
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) ↔
      ∀ k r : ℕ, 13 < k ∨ 43 < r →
        0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment k r := by
  exact
    (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_scaledPrimeArchHausdorffMomentDifferencesNonnegative
      hL hN).trans
      scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_rectangleTailNonnegative

/-- Compatibility reduction to the complement of the earlier 301-condition wedge. -/
theorem scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_weightedTailNonnegative :
    ScaledHausdorffMomentDifferencesNonnegative primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment ↔
      ∀ k r : ℕ, 40 < 3 * k + r →
        0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment k r := by
  constructor
  · intro hall k r htail
    exact hall k r
  · intro htail k r
    by_cases hweight : 3 * k + r ≤ 40
    · exact scaledPrimeArchEndpointHausdorffDifference_weightedDegree_le_forty_nonnegative
        k r hweight
    · exact htail k r (by omega)

/-- Compatibility reduction of the prime--polar endpoint to the earlier weighted tail. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_weightedHausdorffTailNonnegative
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) ↔
      ∀ k r : ℕ, 40 < 3 * k + r →
        0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment k r := by
  exact
    (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_scaledPrimeArchHausdorffMomentDifferencesNonnegative
      hL hN).trans
      scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_weightedTailNonnegative

/-- Symmetric-core corollary: each divisor atom is nonnegative through total degree thirteen. -/
theorem re_xiCentral_scaledBasis_totalDegree_le_thirteen_nonneg
    (q : XiZeroCopy) (k r : ℕ) (hdegree : k + r ≤ 13) :
    0 ≤ (xiZeroCopyReciprocalSquare q ^ (k + 1) *
      ((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q) ^ r).re := by
  exact re_xiCentral_scaledBasis_weightedDegree_le_twentySix_nonneg q k r (by omega)

/-- Symmetric-core corollary: the complete total-degree-thirteen triangle is unconditionally
nonnegative. -/
theorem scaledPrimeArchEndpointHausdorffDifference_totalDegree_le_thirteen_nonnegative
    (k r : ℕ) (hdegree : k + r ≤ 13) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r := by
  exact scaledPrimeArchEndpointHausdorffDifference_weightedDegree_le_twentySix_nonnegative
    k r (by omega)

end
end RHTower

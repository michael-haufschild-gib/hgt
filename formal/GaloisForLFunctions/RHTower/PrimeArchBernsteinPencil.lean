import GaloisForLFunctions.RHTower.PrimeArchCofinalHausdorffDiagonalRH
import GaloisForLFunctions.RHTower.PrimeArchScaledHausdorffDivisorValueRelation

/-!
# The prime--Gamma Bernstein pencil and its exact total-variation defect

The canonical Bernstein masses have two complementary descriptions. Their `l1` norm is exactly
the zeroth source mass plus twice their total negative mass. Their generating polynomial is also
exactly a reciprocal-square Xi-divisor pencil. Hence one scalar source defect simultaneously
controls every value of that divisor pencil on the closed unit disk.

This is unconditional source infrastructure. It replaces no sign by assumption and feeds no
zero-derived positive carrier into the source. The next analytic task is to read the exponential
growth rate of the pencil from the nonreal reciprocal-square support.
-/

open scoped BigOperators Polynomial
open Polynomial

namespace RHTower

noncomputable section

open HTGeometry

/-- Evaluation of a moment functional on one Bernstein basis vector. -/
def bernsteinCoefficient (m : ℕ → ℝ) (n i : ℕ) : ℝ :=
  momentFunctional m (bernsteinPolynomial ℝ n i)

/-- Total variation of the degree-`n` Bernstein coefficient vector. -/
def bernsteinCoefficientL1 (m : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), |bernsteinCoefficient m n i|

/-- The polynomial whose coefficients are the degree-`n` Bernstein masses. -/
def bernsteinCoefficientTransform (m : ℕ → ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (n + 1), (bernsteinCoefficient m n i : ℂ) * w ^ i

/-- Bernstein coefficients sum to the zeroth moment. -/
lemma sum_bernsteinCoefficient (m : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), bernsteinCoefficient m n i = m 0 := by
  simp only [bernsteinCoefficient]
  rw [← momentFunctional_sum, bernsteinPolynomial.sum]
  simpa using momentFunctional_X_pow m 0

/-- **Exact order-unit defect identity.** Bernstein total variation is the zeroth mass plus twice
the total negative mass. -/
theorem bernsteinCoefficientL1_eq_mass_add_two_negativeMass
    (m : ℕ → ℝ) (N : ℕ) :
    bernsteinCoefficientL1 m (N + 1) =
      m 0 + 2 * hausdorffBernsteinNegativeMass m N := by
  rw [bernsteinCoefficientL1, hausdorffBernsteinNegativeMass]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ =>
      (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))⁻) (N + 2)]
  have hsum := sum_bernsteinCoefficient m (N + 1)
  simp only [bernsteinCoefficient] at hsum ⊢
  rw [show N + 2 = N + 1 + 1 by omega, ← hsum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have h := abs_sub_eq_two_nsmul_negPart
    (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))
  simp only [nsmul_eq_mul] at h
  calc
    |momentFunctional m (bernsteinPolynomial ℝ (N + 1) i)| =
        2 * (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))⁻ +
          momentFunctional m (bernsteinPolynomial ℝ (N + 1) i) :=
      (sub_eq_iff_eq_add.mp h)
    _ = _ := by ring

/-- The total variation of the Bernstein coefficient vector bounds its transform throughout the
closed unit disk. -/
theorem norm_bernsteinCoefficientTransform_le_l1
    (m : ℕ → ℝ) (n : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖bernsteinCoefficientTransform m n w‖ ≤ bernsteinCoefficientL1 m n := by
  rw [bernsteinCoefficientTransform, bernsteinCoefficientL1]
  calc
    ‖∑ i ∈ Finset.range (n + 1),
        (bernsteinCoefficient m n i : ℂ) * w ^ i‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        ‖(bernsteinCoefficient m n i : ℂ) * w ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), |bernsteinCoefficient m n i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      calc
        |bernsteinCoefficient m n i| * ‖w‖ ^ i ≤
            |bernsteinCoefficient m n i| * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg w) hw)
            (abs_nonneg _)
        _ = _ := mul_one _
    _ = _ := rfl

/-- Scaling the moments by `R^n` is polynomial composition by `X / R`. -/
lemma momentFunctional_radiusNormalized_eq_comp_scale
    (R : ℝ) (m : ℕ → ℝ) (p : Polynomial ℝ) :
    momentFunctional (radiusNormalizedMoment R m) p =
      momentFunctional m (p.comp (Polynomial.C R⁻¹ * Polynomial.X)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [momentFunctional_add, hp, hq, Polynomial.add_comp, momentFunctional_add]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial,
        ← Polynomial.smul_eq_C_mul, momentFunctional_smul,
        momentFunctional_X_pow, Polynomial.smul_comp,
        Polynomial.X_pow_comp, momentFunctional_smul]
      rw [show (Polynomial.C R⁻¹ * Polynomial.X) ^ n =
          R⁻¹ ^ n • Polynomial.X ^ n by
        rw [mul_pow]
        simp only [smul_eq_C_mul, map_pow]]
      rw [momentFunctional_smul, momentFunctional_X_pow]
      simp [radiusNormalizedMoment, div_eq_mul_inv, inv_pow, mul_comm]

/-- The reciprocal-square divisor functional after scaling its polynomial coordinate by `R`. -/
def xiCentralRadiusNormalizedPolynomialMoment (R : ℝ) (p : Polynomial ℝ) : ℂ :=
  xiCentralPolynomialMoment (p.comp (Polynomial.C R⁻¹ * Polynomial.X))

/-- Evaluation commutes with radius normalization of the polynomial coordinate. -/
lemma evalRealPolynomial_comp_radiusScale (R : ℝ) (p : Polynomial ℝ) (z : ℂ) :
    evalRealPolynomial (p.comp (Polynomial.C R⁻¹ * Polynomial.X)) z =
      evalRealPolynomial p (z / (R : ℂ)) := by
  simp only [evalRealPolynomial, Polynomial.eval_map, Polynomial.eval₂_comp,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  congr 1
  push_cast
  simp [div_eq_mul_inv, mul_comm]

/-- The radius-normalized divisor functional is exactly the radius-normalized prime--Gamma moment
functional. -/
lemma xiCentralRadiusNormalizedPolynomialMoment_eq_source
    (R : ℝ) (p : Polynomial ℝ) :
    xiCentralRadiusNormalizedPolynomialMoment R p =
      (momentFunctional (radiusNormalizedMoment R normalizedPrimeArchMoment) p : ℂ) := by
  rw [xiCentralRadiusNormalizedPolynomialMoment,
    xiCentralPolynomialMoment_eq_sourceMomentFunctional]
  rw [momentFunctional_radiusNormalized_eq_comp_scale]

/-- Divisor-sum form of the radius-normalized polynomial functional. -/
lemma xiCentralRadiusNormalizedPolynomialMoment_eq_tsum
    (R : ℝ) (p : Polynomial ℝ) :
    xiCentralRadiusNormalizedPolynomialMoment R p =
      ∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q *
        evalRealPolynomial p (xiZeroCopyReciprocalSquare q / (R : ℂ)) := by
  rw [xiCentralRadiusNormalizedPolynomialMoment, xiCentralPolynomialMoment]
  apply tsum_congr
  intro q
  rw [xiCentralPolynomialMomentTerm]
  rw [evalRealPolynomial_comp_radiusScale]

/-- Absolute summability of every radius-normalized polynomial divisor packet. -/
lemma summable_xiCentralRadiusNormalizedPolynomialTerm
    (R : ℝ) (p : Polynomial ℝ) :
    Summable (fun q : XiZeroCopy => xiZeroCopyReciprocalSquare q *
      evalRealPolynomial p (xiZeroCopyReciprocalSquare q / (R : ℂ))) := by
  let ps := p.comp (Polynomial.C R⁻¹ * Polynomial.X)
  have h := summable_xiCentralPolynomialMomentTerm ps
  apply h.congr
  intro q
  rw [xiCentralPolynomialMomentTerm]
  simpa only [ps] using congrArg
    (fun z => xiZeroCopyReciprocalSquare q * z)
    (evalRealPolynomial_comp_radiusScale R p (xiZeroCopyReciprocalSquare q))

/-- The circle pencil generated by the radius-normalized reciprocal-square divisor. -/
def xiCentralBernsteinPencil (R : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q *
    (1 - xiZeroCopyReciprocalSquare q / (R : ℂ) +
      (xiZeroCopyReciprocalSquare q / (R : ℂ)) * w) ^ n

/-- **Prime--Gamma/Xi Bernstein-pencil identity.** The generating polynomial of the source
Bernstein masses is exactly the radius-normalized reciprocal-square divisor pencil. -/
theorem bernsteinCoefficientTransform_source_eq_xiCentralBernsteinPencil
    (R : ℝ) (n : ℕ) (w : ℂ) :
    bernsteinCoefficientTransform
        (radiusNormalizedMoment R normalizedPrimeArchMoment) n w =
      xiCentralBernsteinPencil R n w := by
  rw [bernsteinCoefficientTransform, xiCentralBernsteinPencil]
  calc
    (∑ i ∈ Finset.range (n + 1),
        (bernsteinCoefficient (radiusNormalizedMoment R normalizedPrimeArchMoment) n i : ℂ) *
          w ^ i) =
      ∑ i ∈ Finset.range (n + 1),
        xiCentralRadiusNormalizedPolynomialMoment R (bernsteinPolynomial ℝ n i) * w ^ i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [xiCentralRadiusNormalizedPolynomialMoment_eq_source]
          rfl
    _ = ∑ i ∈ Finset.range (n + 1),
        (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q *
          evalRealPolynomial (bernsteinPolynomial ℝ n i)
            (xiZeroCopyReciprocalSquare q / (R : ℂ))) * w ^ i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [xiCentralRadiusNormalizedPolynomialMoment_eq_tsum]
    _ = ∑ i ∈ Finset.range (n + 1),
        ∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q *
          evalRealPolynomial (bernsteinPolynomial ℝ n i)
            (xiZeroCopyReciprocalSquare q / (R : ℂ)) * w ^ i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [tsum_mul_right]
    _ = ∑' q : XiZeroCopy, ∑ i ∈ Finset.range (n + 1),
        (xiZeroCopyReciprocalSquare q *
          evalRealPolynomial (bernsteinPolynomial ℝ n i)
            (xiZeroCopyReciprocalSquare q / (R : ℂ)) * w ^ i) := by
          rw [Summable.tsum_finsetSum (fun i _ =>
            (summable_xiCentralRadiusNormalizedPolynomialTerm R
              (bernsteinPolynomial ℝ n i)).mul_right (w ^ i))]
    _ = _ := by
      apply tsum_congr
      intro q
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      rw [show 1 - xiZeroCopyReciprocalSquare q / (R : ℂ) +
          xiZeroCopyReciprocalSquare q / (R : ℂ) * w =
          xiZeroCopyReciprocalSquare q / (R : ℂ) * w +
            (1 - xiZeroCopyReciprocalSquare q / (R : ℂ)) by ring,
        add_pow]
      apply Finset.sum_congr rfl
      intro i hi
      rw [bernsteinPolynomial]
      simp only [evalRealPolynomial, Polynomial.eval_map, Polynomial.eval₂_mul,
        Polynomial.eval₂_natCast, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_sub, Polynomial.eval₂_one]
      ring

/-- **Unit-disk source control law.** Every unit-disk value of the reciprocal-square Bernstein
pencil is bounded by the zeroth prime--Gamma mass plus twice the Bernstein negative-mass defect. -/
theorem norm_xiCentralBernsteinPencil_le_mass_add_two_negativeMass
    (R : ℝ) (N : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖xiCentralBernsteinPencil R (N + 1) w‖ ≤
      normalizedPrimeArchMoment 0 +
        2 * hausdorffBernsteinNegativeMass
          (radiusNormalizedMoment R normalizedPrimeArchMoment) N := by
  rw [← bernsteinCoefficientTransform_source_eq_xiCentralBernsteinPencil]
  calc
    ‖bernsteinCoefficientTransform
        (radiusNormalizedMoment R normalizedPrimeArchMoment) (N + 1) w‖ ≤
      bernsteinCoefficientL1
        (radiusNormalizedMoment R normalizedPrimeArchMoment) (N + 1) :=
      norm_bernsteinCoefficientTransform_le_l1 _ _ hw
    _ = radiusNormalizedMoment R normalizedPrimeArchMoment 0 +
        2 * hausdorffBernsteinNegativeMass
          (radiusNormalizedMoment R normalizedPrimeArchMoment) N :=
      bernsteinCoefficientL1_eq_mass_add_two_negativeMass _ _
    _ = _ := by simp [radiusNormalizedMoment]

end

end RHTower

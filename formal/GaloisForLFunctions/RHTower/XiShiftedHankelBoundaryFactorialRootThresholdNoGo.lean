import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryKreinCrossing
import GaloisForLFunctions.HTGeometry.FactorialPositiveCarrierOrientationNoGo
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryReverseBesselCarrier

/-!
# Squared-factorial carrier threshold law and orientation no-go

The reverse-Bessel realization of a shifted-Xi boundary packet uses the squared-factorial
coefficient transform

`P^sharp_r(t) = sum_j c_j t^j / ((r+j)!)^2`.

For any positive atomic carrier with squared-factorial moments, its first omitted coefficient
combination is exactly the carrier mass tested against `t^r P^sharp_r(t)`.  This file proves that
identity for arbitrary finite carriers.

It then gives a hostile pair at the first nontrivial face.  Two strictly positive two-atom carriers
have the same squared-factorial moments through order two, the same positive singular Hankel face,
and the same transformed null polynomial

`P^sharp_2(t) = (t - 9) / 36`,

but their first crossings are respectively `37/144` and `-19/72`.  Thus real/simple/positive root
geometry of the adaptive factorial transform, and positivity of the carrier on either side, do not
orient the crossing.  The missing Xi theorem must control the source-specific weighted mass balance
across the adaptive roots.
-/

open Matrix Polynomial MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Squared-factorial moments of a finite atomic carrier. -/
def squaredFactorialAtomicMoment {ι : Type*} [Fintype ι]
    (weight node : ι → ℝ) (k : ℕ) : ℝ :=
  (∑ i, weight i * node i ^ k) / ((k.factorial : ℝ) ^ 2)

/-- **Squared-factorial carrier law.**  A consecutive coefficient packet combines before the
carrier sum, and the resulting test is exactly `t^r P^sharp_r(t)`. -/
theorem sum_mul_squaredFactorialAtomicMoment_eq_factorialCarrier
    {ι : Type*} [Fintype ι] (weight node : ι → ℝ)
    (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    ∑ j : Fin N, c j * squaredFactorialAtomicMoment weight node (r + (j : ℕ)) =
      ∑ i : ι, weight i * node i ^ r *
        xiShiftedBoundaryFactorialCarrierPolynomial r c (node i) := by
  classical
  simp only [squaredFactorialAtomicMoment,
    xiShiftedBoundaryFactorialCarrierPolynomial]
  simp_rw [Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  have hfac : (((r + (j : ℕ)).factorial : ℝ) ^ 2) ≠ 0 := by positivity
  field_simp [hfac]

def squaredFactorialPositiveCarrierWeight : Fin 2 → ℝ := ![48 / 49, 1 / 49]
def squaredFactorialPositiveCarrierNode : Fin 2 → ℝ := ![3 / 4, 13]
def squaredFactorialNegativeCarrierWeight : Fin 2 → ℝ := ![12 / 13, 1 / 13]
def squaredFactorialNegativeCarrierNode : Fin 2 → ℝ := ![1 / 2, 7]

theorem squaredFactorialPositiveCarrier_strictlyPositive :
    ∀ i, 0 < squaredFactorialPositiveCarrierWeight i ∧
      0 < squaredFactorialPositiveCarrierNode i := by
  intro i
  fin_cases i <;>
    norm_num [squaredFactorialPositiveCarrierWeight, squaredFactorialPositiveCarrierNode]

theorem squaredFactorialNegativeCarrier_strictlyPositive :
    ∀ i, 0 < squaredFactorialNegativeCarrierWeight i ∧
      0 < squaredFactorialNegativeCarrierNode i := by
  intro i
  fin_cases i <;>
    norm_num [squaredFactorialNegativeCarrierWeight, squaredFactorialNegativeCarrierNode]

@[simp] theorem squaredFactorialPositiveCarrierMoment_zero :
    squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
      squaredFactorialPositiveCarrierNode 0 = 1 := by
  norm_num [squaredFactorialAtomicMoment, squaredFactorialPositiveCarrierWeight,
    squaredFactorialPositiveCarrierNode, Fin.sum_univ_two]

@[simp] theorem squaredFactorialPositiveCarrierMoment_one :
    squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
      squaredFactorialPositiveCarrierNode 1 = 1 := by
  norm_num [squaredFactorialAtomicMoment, squaredFactorialPositiveCarrierWeight,
    squaredFactorialPositiveCarrierNode, Fin.sum_univ_two]

@[simp] theorem squaredFactorialPositiveCarrierMoment_two :
    squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
      squaredFactorialPositiveCarrierNode 2 = 1 := by
  norm_num [squaredFactorialAtomicMoment, squaredFactorialPositiveCarrierWeight,
    squaredFactorialPositiveCarrierNode, Fin.sum_univ_two]

@[simp] theorem squaredFactorialPositiveCarrierMoment_three :
    squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
      squaredFactorialPositiveCarrierNode 3 = 181 / 144 := by
  norm_num [squaredFactorialAtomicMoment, squaredFactorialPositiveCarrierWeight,
    squaredFactorialPositiveCarrierNode, Fin.sum_univ_two]

@[simp] theorem squaredFactorialNegativeCarrierMoment_zero :
    squaredFactorialAtomicMoment squaredFactorialNegativeCarrierWeight
      squaredFactorialNegativeCarrierNode 0 = 1 := by
  norm_num [squaredFactorialAtomicMoment, squaredFactorialNegativeCarrierWeight,
    squaredFactorialNegativeCarrierNode, Fin.sum_univ_two]

@[simp] theorem squaredFactorialNegativeCarrierMoment_one :
    squaredFactorialAtomicMoment squaredFactorialNegativeCarrierWeight
      squaredFactorialNegativeCarrierNode 1 = 1 := by
  norm_num [squaredFactorialAtomicMoment, squaredFactorialNegativeCarrierWeight,
    squaredFactorialNegativeCarrierNode, Fin.sum_univ_two]

@[simp] theorem squaredFactorialNegativeCarrierMoment_two :
    squaredFactorialAtomicMoment squaredFactorialNegativeCarrierWeight
      squaredFactorialNegativeCarrierNode 2 = 1 := by
  norm_num [squaredFactorialAtomicMoment, squaredFactorialNegativeCarrierWeight,
    squaredFactorialNegativeCarrierNode, Fin.sum_univ_two]

@[simp] theorem squaredFactorialNegativeCarrierMoment_three :
    squaredFactorialAtomicMoment squaredFactorialNegativeCarrierWeight
      squaredFactorialNegativeCarrierNode 3 = 53 / 72 := by
  norm_num [squaredFactorialAtomicMoment, squaredFactorialNegativeCarrierWeight,
    squaredFactorialNegativeCarrierNode, Fin.sum_univ_two]

def squaredFactorialCarrierNoGoKernel : Fin 2 → ℝ := ![-1, 1]

/-- The adaptive polynomial seen by the exact reverse-Bessel carrier has one positive root, at
`t = 9`. -/
theorem squaredFactorialCarrierNoGoPolynomial_eq (t : ℝ) :
    xiShiftedBoundaryFactorialCarrierPolynomial 2 squaredFactorialCarrierNoGoKernel t =
      (t - 9) / 36 := by
  norm_num [xiShiftedBoundaryFactorialCarrierPolynomial,
    squaredFactorialCarrierNoGoKernel, Fin.sum_univ_two]
  ring

theorem squaredFactorialCarrierNoGoPolynomial_eq_zero_iff (t : ℝ) :
    xiShiftedBoundaryFactorialCarrierPolynomial 2 squaredFactorialCarrierNoGoKernel t = 0 ↔
      t = 9 := by
  rw [squaredFactorialCarrierNoGoPolynomial_eq]
  constructor <;> intro h
  · linarith
  · rw [h]
    norm_num

theorem squaredFactorialCarrierNoGoPolynomial_neg {t : ℝ} (ht : t < 9) :
    xiShiftedBoundaryFactorialCarrierPolynomial 2 squaredFactorialCarrierNoGoKernel t < 0 := by
  rw [squaredFactorialCarrierNoGoPolynomial_eq]
  linarith

theorem squaredFactorialCarrierNoGoPolynomial_pos {t : ℝ} (ht : 9 < t) :
    0 < xiShiftedBoundaryFactorialCarrierPolynomial 2 squaredFactorialCarrierNoGoKernel t := by
  rw [squaredFactorialCarrierNoGoPolynomial_eq]
  linarith

/-- The negative-orientation carrier is supported entirely below the adaptive root. -/
theorem squaredFactorialNegativeCarrierNode_lt_root :
    ∀ i, squaredFactorialNegativeCarrierNode i < 9 := by
  intro i
  fin_cases i <;> norm_num [squaredFactorialNegativeCarrierNode]

/-- The positive-orientation carrier straddles the same adaptive root. -/
theorem squaredFactorialPositiveCarrierNode_straddles_root :
    squaredFactorialPositiveCarrierNode 0 < 9 ∧
      9 < squaredFactorialPositiveCarrierNode 1 := by
  norm_num [squaredFactorialPositiveCarrierNode]

theorem squaredFactorialPositiveCarrier_head_posDef :
    (HTGeometry.momentHankelMatrix
      (squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
        squaredFactorialPositiveCarrierNode) 1).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · exact HTGeometry.momentHankelMatrix_isHermitian _ _
  · intro x hx
    have hx0 : x 0 ≠ 0 := by
      intro hx0
      apply hx
      funext i
      fin_cases i
      exact hx0
    simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_one,
      HTGeometry.momentHankelMatrix]
    norm_num only [Fin.val_zero, zero_add]
    rw [squaredFactorialPositiveCarrierMoment_zero]
    nlinarith [sq_pos_of_ne_zero hx0]

/-- The common size-two face is genuinely positive semidefinite, not merely singular. -/
theorem squaredFactorialPositiveCarrier_face_posSemidef :
    (HTGeometry.momentHankelMatrix
      (squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
        squaredFactorialPositiveCarrierNode) 2).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · exact HTGeometry.momentHankelMatrix_isHermitian _ _
  · intro x
    simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      HTGeometry.momentHankelMatrix]
    norm_num only [Fin.val_zero, Fin.val_one, Nat.zero_add, Nat.add_zero]
    rw [squaredFactorialPositiveCarrierMoment_zero,
      squaredFactorialPositiveCarrierMoment_one,
      squaredFactorialPositiveCarrierMoment_two]
    nlinarith [sq_nonneg (x 0 + x 1)]

theorem squaredFactorialCarrierNoGoKernel_ne_zero :
    squaredFactorialCarrierNoGoKernel ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [squaredFactorialCarrierNoGoKernel] at h0

theorem squaredFactorialPositiveCarrier_kernel :
    HTGeometry.momentHankelMatrix
        (squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
          squaredFactorialPositiveCarrierNode) 2 *ᵥ
      squaredFactorialCarrierNoGoKernel = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, HTGeometry.momentHankelMatrix,
      squaredFactorialCarrierNoGoKernel]

theorem squaredFactorialNegativeCarrier_kernel :
    HTGeometry.momentHankelMatrix
        (squaredFactorialAtomicMoment squaredFactorialNegativeCarrierWeight
          squaredFactorialNegativeCarrierNode) 2 *ᵥ
      squaredFactorialCarrierNoGoKernel = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, HTGeometry.momentHankelMatrix,
      squaredFactorialCarrierNoGoKernel]

theorem squaredFactorialCarriers_sameFace :
    HTGeometry.momentHankelMatrix
        (squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
          squaredFactorialPositiveCarrierNode) 2 =
      HTGeometry.momentHankelMatrix
        (squaredFactorialAtomicMoment squaredFactorialNegativeCarrierWeight
          squaredFactorialNegativeCarrierNode) 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HTGeometry.momentHankelMatrix]

theorem squaredFactorialCarrierNoGo_monicNullPolynomial :
    HTGeometry.finiteHankelNullMonicPolynomial squaredFactorialCarrierNoGoKernel = X - C 1 := by
  have hraw : HTGeometry.finiteHankelNullPolynomial squaredFactorialCarrierNoGoKernel =
      X - C 1 := by
    rw [HTGeometry.finiteHankelNullPolynomial, Polynomial.ofFn_eq_sum_monomial,
      Fin.sum_univ_two]
    simp [squaredFactorialCarrierNoGoKernel, monomial_one_right_eq_X_pow]
    ring
  rw [HTGeometry.finiteHankelNullMonicPolynomial, hraw]
  have hdeg : (C (1 : ℝ)).degree < (X : Polynomial ℝ).degree := by simp
  rw [Polynomial.leadingCoeff_sub_of_degree_lt hdeg, Polynomial.leadingCoeff_X]
  simp

theorem squaredFactorialPositiveCarrier_crossing :
    HTGeometry.finiteHankelBoundaryNullCrossingForm
      (squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
        squaredFactorialPositiveCarrierNode) squaredFactorialCarrierNoGoKernel =
      37 / 144 := by
  rw [HTGeometry.finiteHankelBoundaryNullCrossingForm,
    squaredFactorialCarrierNoGo_monicNullPolynomial,
    HTGeometry.momentInner_def]
  norm_num only [Nat.reduceAdd]
  have hpoly : ((X : Polynomial ℝ) - C 1) * (X * (X - C 1)) =
      (X ^ 3 - X ^ 2 - X ^ 2) + X ^ 1 := by
    norm_num
    ring
  rw [hpoly, HTGeometry.momentFunctional_add,
    HTGeometry.momentFunctional_sub,
    HTGeometry.momentFunctional_sub]
  rw [
    HTGeometry.momentFunctional_X_pow,
    HTGeometry.momentFunctional_X_pow,
    HTGeometry.momentFunctional_X_pow]
  rw [squaredFactorialPositiveCarrierMoment_three,
    squaredFactorialPositiveCarrierMoment_two,
    squaredFactorialPositiveCarrierMoment_one]
  norm_num

theorem squaredFactorialNegativeCarrier_crossing :
    HTGeometry.finiteHankelBoundaryNullCrossingForm
      (squaredFactorialAtomicMoment squaredFactorialNegativeCarrierWeight
        squaredFactorialNegativeCarrierNode) squaredFactorialCarrierNoGoKernel =
      -(19 / 72) := by
  rw [HTGeometry.finiteHankelBoundaryNullCrossingForm,
    squaredFactorialCarrierNoGo_monicNullPolynomial,
    HTGeometry.momentInner_def]
  norm_num only [Nat.reduceAdd]
  have hpoly : ((X : Polynomial ℝ) - C 1) * (X * (X - C 1)) =
      (X ^ 3 - X ^ 2 - X ^ 2) + X ^ 1 := by
    norm_num
    ring
  rw [hpoly, HTGeometry.momentFunctional_add,
    HTGeometry.momentFunctional_sub,
    HTGeometry.momentFunctional_sub]
  rw [
    HTGeometry.momentFunctional_X_pow,
    HTGeometry.momentFunctional_X_pow,
    HTGeometry.momentFunctional_X_pow]
  rw [squaredFactorialNegativeCarrierMoment_three,
    squaredFactorialNegativeCarrierMoment_two,
    squaredFactorialNegativeCarrierMoment_one]
  norm_num

/-- The positive crossing is exactly positive carrier mass tested against `t^2 P^sharp(t)`. -/
theorem squaredFactorialPositiveCarrier_crossing_eq_rootThresholdMass :
    HTGeometry.finiteHankelBoundaryNullCrossingForm
        (squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
          squaredFactorialPositiveCarrierNode) squaredFactorialCarrierNoGoKernel =
      ∑ i : Fin 2, squaredFactorialPositiveCarrierWeight i *
        squaredFactorialPositiveCarrierNode i ^ 2 *
          xiShiftedBoundaryFactorialCarrierPolynomial 2
            squaredFactorialCarrierNoGoKernel (squaredFactorialPositiveCarrierNode i) := by
  rw [squaredFactorialPositiveCarrier_crossing]
  norm_num [squaredFactorialPositiveCarrierWeight, squaredFactorialPositiveCarrierNode,
    squaredFactorialCarrierNoGoPolynomial_eq, Fin.sum_univ_two]

/-- The negative crossing is the same root-threshold observable on the second positive carrier. -/
theorem squaredFactorialNegativeCarrier_crossing_eq_rootThresholdMass :
    HTGeometry.finiteHankelBoundaryNullCrossingForm
        (squaredFactorialAtomicMoment squaredFactorialNegativeCarrierWeight
          squaredFactorialNegativeCarrierNode) squaredFactorialCarrierNoGoKernel =
      ∑ i : Fin 2, squaredFactorialNegativeCarrierWeight i *
        squaredFactorialNegativeCarrierNode i ^ 2 *
          xiShiftedBoundaryFactorialCarrierPolynomial 2
            squaredFactorialCarrierNoGoKernel (squaredFactorialNegativeCarrierNode i) := by
  rw [squaredFactorialNegativeCarrier_crossing]
  norm_num [squaredFactorialNegativeCarrierWeight, squaredFactorialNegativeCarrierNode,
    squaredFactorialCarrierNoGoPolynomial_eq, Fin.sum_univ_two]

/-- **Adaptive-root orientation no-go.**  Exact squared-factorial normalization, strict carrier
positivity, a common positive singular face, and one identical real/simple/positive adaptive root
still permit both Krein orientations. -/
theorem squaredFactorialCarrierRootThresholdOrientationNoGo :
    (∀ i, 0 < squaredFactorialPositiveCarrierWeight i ∧
      0 < squaredFactorialPositiveCarrierNode i) ∧
    (∀ i, 0 < squaredFactorialNegativeCarrierWeight i ∧
      0 < squaredFactorialNegativeCarrierNode i) ∧
    HTGeometry.momentHankelMatrix
        (squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
          squaredFactorialPositiveCarrierNode) 2 =
      HTGeometry.momentHankelMatrix
        (squaredFactorialAtomicMoment squaredFactorialNegativeCarrierWeight
          squaredFactorialNegativeCarrierNode) 2 ∧
    (HTGeometry.momentHankelMatrix
      (squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
        squaredFactorialPositiveCarrierNode) 1).PosDef ∧
    (HTGeometry.momentHankelMatrix
      (squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
        squaredFactorialPositiveCarrierNode) 2).PosSemidef ∧
    squaredFactorialCarrierNoGoKernel ≠ 0 ∧
    HTGeometry.momentHankelMatrix
        (squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
          squaredFactorialPositiveCarrierNode) 2 *ᵥ
      squaredFactorialCarrierNoGoKernel = 0 ∧
    HTGeometry.momentHankelMatrix
        (squaredFactorialAtomicMoment squaredFactorialNegativeCarrierWeight
          squaredFactorialNegativeCarrierNode) 2 *ᵥ
      squaredFactorialCarrierNoGoKernel = 0 ∧
    (∀ t : ℝ,
      xiShiftedBoundaryFactorialCarrierPolynomial 2 squaredFactorialCarrierNoGoKernel t = 0 ↔
        t = 9) ∧
    (∀ i, squaredFactorialNegativeCarrierNode i < 9) ∧
    squaredFactorialPositiveCarrierNode 0 < 9 ∧
    9 < squaredFactorialPositiveCarrierNode 1 ∧
    HTGeometry.finiteHankelBoundaryNullCrossingForm
      (squaredFactorialAtomicMoment squaredFactorialPositiveCarrierWeight
        squaredFactorialPositiveCarrierNode) squaredFactorialCarrierNoGoKernel = 37 / 144 ∧
    HTGeometry.finiteHankelBoundaryNullCrossingForm
      (squaredFactorialAtomicMoment squaredFactorialNegativeCarrierWeight
        squaredFactorialNegativeCarrierNode) squaredFactorialCarrierNoGoKernel = -(19 / 72) := by
  exact ⟨squaredFactorialPositiveCarrier_strictlyPositive,
    squaredFactorialNegativeCarrier_strictlyPositive,
    squaredFactorialCarriers_sameFace,
    squaredFactorialPositiveCarrier_head_posDef,
    squaredFactorialPositiveCarrier_face_posSemidef,
    squaredFactorialCarrierNoGoKernel_ne_zero,
    squaredFactorialPositiveCarrier_kernel,
    squaredFactorialNegativeCarrier_kernel,
    squaredFactorialCarrierNoGoPolynomial_eq_zero_iff,
    squaredFactorialNegativeCarrierNode_lt_root,
    squaredFactorialPositiveCarrierNode_straddles_root.1,
    squaredFactorialPositiveCarrierNode_straddles_root.2,
    squaredFactorialPositiveCarrier_crossing,
    squaredFactorialNegativeCarrier_crossing⟩

/-! ## Full-support exponential carriers

The preceding atomic model is not relying on atomic support.  A positive exponential component
of mean `a` has raw `k`-th moment `k! a^k`; after squared-factorial normalization this is exactly
`a^k/k!`.  Hence the earlier factorial-carrier no-go is the moment sequence of a strictly positive
full-support mixture of exponentials, and its crossing is the integral of `t^r P^sharp_r(t)`.
-/

/-- Positive mixture of exponential densities with component means `scale i`. -/
def exponentialMixtureDensity {ι : Type*} [Fintype ι]
    (weight scale : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, weight i * (scale i)⁻¹ * Real.exp (-((scale i)⁻¹ * t))

theorem integrableOn_pow_mul_exponentialMixtureDensity
    {ι : Type*} [Fintype ι] (weight scale : ι → ℝ)
    (hscale : ∀ i, 0 < scale i) (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k * exponentialMixtureDensity weight scale t)
      (Set.Ioi (0 : ℝ)) := by
  classical
  unfold exponentialMixtureDensity
  rw [show (fun t : ℝ => t ^ k * ∑ i, weight i * (scale i)⁻¹ *
      Real.exp (-((scale i)⁻¹ * t))) =
      fun t : ℝ => ∑ i, (weight i * (scale i)⁻¹) *
        (t ^ k * Real.exp (-((scale i)⁻¹ * t))) by
    funext t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  apply integrable_finsetSum Finset.univ
  intro i _
  exact (integrableOn_pow_mul_exp_neg_mul_Ioi (inv_pos.mpr (hscale i)) k).const_mul
    (weight i * (scale i)⁻¹)

/-- Raw moments of an exponential mixture. -/
theorem integral_pow_mul_exponentialMixtureDensity
    {ι : Type*} [Fintype ι] (weight scale : ι → ℝ)
    (hscale : ∀ i, 0 < scale i) (k : ℕ) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ k * exponentialMixtureDensity weight scale t) =
      (k.factorial : ℝ) * ∑ i, weight i * scale i ^ k := by
  classical
  unfold exponentialMixtureDensity
  rw [show (fun t : ℝ => t ^ k * ∑ i, weight i * (scale i)⁻¹ *
      Real.exp (-((scale i)⁻¹ * t))) =
      fun t : ℝ => ∑ i, (weight i * (scale i)⁻¹) *
        (t ^ k * Real.exp (-((scale i)⁻¹ * t))) by
    funext t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [MeasureTheory.integral_finsetSum Finset.univ]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [MeasureTheory.integral_const_mul,
      integral_pow_mul_exp_neg_mul_Ioi (inv_pos.mpr (hscale i))]
    have hne : scale i ≠ 0 := ne_of_gt (hscale i)
    rw [inv_pow]
    field_simp [hne]
    ring
  · intro i _
    exact (integrableOn_pow_mul_exp_neg_mul_Ioi (inv_pos.mpr (hscale i)) k).const_mul
      (weight i * (scale i)⁻¹)

/-- **Exponential-mixture factorial carrier law.**  The exact squared-factorial adaptive test is
the root-threshold integral of `t^r P^sharp_r(t)` against a full-support exponential mixture. -/
theorem integral_factorialCarrier_mul_exponentialMixtureDensity
    {ι : Type*} [Fintype ι] (weight scale : ι → ℝ)
    (hscale : ∀ i, 0 < scale i) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    (∫ t in Set.Ioi (0 : ℝ),
        t ^ r * xiShiftedBoundaryFactorialCarrierPolynomial r c t *
          exponentialMixtureDensity weight scale t) =
      ∑ j : Fin N, c j *
        ((∑ i, weight i * scale i ^ (r + (j : ℕ))) /
          (((r + (j : ℕ)).factorial : ℝ))) := by
  classical
  have hpoint :
      (fun t : ℝ =>
        t ^ r * xiShiftedBoundaryFactorialCarrierPolynomial r c t *
          exponentialMixtureDensity weight scale t) =
      fun t : ℝ => ∑ j : Fin N,
        (c j / (((r + (j : ℕ)).factorial : ℝ) ^ 2)) *
          (t ^ (r + (j : ℕ)) * exponentialMixtureDensity weight scale t) := by
    funext t
    unfold xiShiftedBoundaryFactorialCarrierPolynomial
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add]
    ring
  rw [hpoint, MeasureTheory.integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro j _
    rw [MeasureTheory.integral_const_mul,
      integral_pow_mul_exponentialMixtureDensity weight scale hscale]
    have hfac : ((r + (j : ℕ)).factorial : ℝ) ≠ 0 := by positivity
    field_simp [hfac]
  · intro j _
    exact (integrableOn_pow_mul_exponentialMixtureDensity weight scale hscale
      (r + (j : ℕ))).const_mul
        (c j / (((r + (j : ℕ)).factorial : ℝ) ^ 2))

theorem factorialCarrierNoGoKernel_eq_squaredFactorialCarrierNoGoKernel :
    HTGeometry.factorialCarrierNoGoKernel = squaredFactorialCarrierNoGoKernel := by
  funext i
  fin_cases i <;>
    simp [HTGeometry.factorialCarrierNoGoKernel, squaredFactorialCarrierNoGoKernel]

theorem factorialCarrierNoGoPolynomial_eq (t : ℝ) :
    xiShiftedBoundaryFactorialCarrierPolynomial 2 HTGeometry.factorialCarrierNoGoKernel t =
      (t - 9) / 36 := by
  rw [factorialCarrierNoGoKernel_eq_squaredFactorialCarrierNoGoKernel,
    squaredFactorialCarrierNoGoPolynomial_eq]

theorem factorialPositiveExponentialMixtureDensity_pos (t : ℝ) :
    0 < exponentialMixtureDensity HTGeometry.factorialPositiveCarrierWeight
      HTGeometry.factorialPositiveCarrierNode t := by
  unfold exponentialMixtureDensity
  rw [Fin.sum_univ_two]
  norm_num [HTGeometry.factorialPositiveCarrierWeight,
    HTGeometry.factorialPositiveCarrierNode]
  positivity

theorem factorialNegativeExponentialMixtureDensity_pos (t : ℝ) :
    0 < exponentialMixtureDensity HTGeometry.factorialNegativeCarrierWeight
      HTGeometry.factorialNegativeCarrierNode t := by
  unfold exponentialMixtureDensity
  rw [Fin.sum_univ_two]
  norm_num [HTGeometry.factorialNegativeCarrierWeight,
    HTGeometry.factorialNegativeCarrierNode]
  positivity

/-- The positive Krein crossing is the adaptive root-threshold integral against a strictly positive
full-support exponential mixture. -/
theorem factorialPositiveCarrier_crossing_eq_exponentialRootThresholdIntegral :
    HTGeometry.finiteHankelBoundaryNullCrossingForm
        (HTGeometry.factorialTwoAtomMoment HTGeometry.factorialPositiveCarrierWeight
          HTGeometry.factorialPositiveCarrierNode) HTGeometry.factorialCarrierNoGoKernel =
      ∫ t in Set.Ioi (0 : ℝ),
        t ^ 2 * xiShiftedBoundaryFactorialCarrierPolynomial 2
          HTGeometry.factorialCarrierNoGoKernel t *
            exponentialMixtureDensity HTGeometry.factorialPositiveCarrierWeight
              HTGeometry.factorialPositiveCarrierNode t := by
  have hlast : HTGeometry.factorialCarrierNoGoKernel (Fin.last 1) ≠ 0 := by
    change (1 : ℝ) ≠ 0
    norm_num
  rw [HTGeometry.finiteHankelBoundaryNullCrossingForm_eq_monicRemainder
      _ _ HTGeometry.factorialPositiveCarrier_kernel hlast,
    HTGeometry.factorialPositiveCarrier_monicRemainder]
  rw [integral_factorialCarrier_mul_exponentialMixtureDensity
    HTGeometry.factorialPositiveCarrierWeight HTGeometry.factorialPositiveCarrierNode
    (fun i => (HTGeometry.factorialPositiveCarrier_strictlyPositive i).2) 2
    HTGeometry.factorialCarrierNoGoKernel]
  norm_num [HTGeometry.factorialCarrierNoGoKernel,
    HTGeometry.factorialPositiveCarrierWeight,
    HTGeometry.factorialPositiveCarrierNode, Fin.sum_univ_two]

/-- The same strictly positive full-support carrier class realizes the opposite crossing. -/
theorem factorialNegativeCarrier_crossing_eq_exponentialRootThresholdIntegral :
    HTGeometry.finiteHankelBoundaryNullCrossingForm
        (HTGeometry.factorialTwoAtomMoment HTGeometry.factorialNegativeCarrierWeight
          HTGeometry.factorialNegativeCarrierNode) HTGeometry.factorialCarrierNoGoKernel =
      ∫ t in Set.Ioi (0 : ℝ),
        t ^ 2 * xiShiftedBoundaryFactorialCarrierPolynomial 2
          HTGeometry.factorialCarrierNoGoKernel t *
            exponentialMixtureDensity HTGeometry.factorialNegativeCarrierWeight
              HTGeometry.factorialNegativeCarrierNode t := by
  have hlast : HTGeometry.factorialCarrierNoGoKernel (Fin.last 1) ≠ 0 := by
    change (1 : ℝ) ≠ 0
    norm_num
  rw [HTGeometry.finiteHankelBoundaryNullCrossingForm_eq_monicRemainder
      _ _ HTGeometry.factorialNegativeCarrier_kernel hlast,
    HTGeometry.factorialNegativeCarrier_monicRemainder]
  rw [integral_factorialCarrier_mul_exponentialMixtureDensity
    HTGeometry.factorialNegativeCarrierWeight HTGeometry.factorialNegativeCarrierNode
    (fun i => (HTGeometry.factorialNegativeCarrier_strictlyPositive i).2) 2
    HTGeometry.factorialCarrierNoGoKernel]
  norm_num [HTGeometry.factorialCarrierNoGoKernel,
    HTGeometry.factorialNegativeCarrierWeight,
    HTGeometry.factorialNegativeCarrierNode, Fin.sum_univ_two]

/-- **Full-support adaptive-root no-go.**  Both carriers have strictly positive density at every
real point and share one adaptive polynomial with the unique positive root `9`, yet their exact
root-threshold integrals have opposite signs. -/
theorem fullSupportFactorialCarrierRootThresholdOrientationNoGo :
    (∀ t : ℝ, 0 < exponentialMixtureDensity HTGeometry.factorialPositiveCarrierWeight
      HTGeometry.factorialPositiveCarrierNode t) ∧
    (∀ t : ℝ, 0 < exponentialMixtureDensity HTGeometry.factorialNegativeCarrierWeight
      HTGeometry.factorialNegativeCarrierNode t) ∧
    (∀ t : ℝ,
      xiShiftedBoundaryFactorialCarrierPolynomial 2 HTGeometry.factorialCarrierNoGoKernel t = 0 ↔
        t = 9) ∧
    HTGeometry.finiteHankelBoundaryNullCrossingForm
      (HTGeometry.factorialTwoAtomMoment HTGeometry.factorialPositiveCarrierWeight
        HTGeometry.factorialPositiveCarrierNode) HTGeometry.factorialCarrierNoGoKernel = 7 / 24 ∧
    HTGeometry.finiteHankelBoundaryNullCrossingForm
      (HTGeometry.factorialTwoAtomMoment HTGeometry.factorialNegativeCarrierWeight
        HTGeometry.factorialNegativeCarrierNode) HTGeometry.factorialCarrierNoGoKernel = -(1 / 12) := by
  have hnoGo := HTGeometry.factorialPositiveCarrierOrientationNoGo
  exact ⟨factorialPositiveExponentialMixtureDensity_pos,
    factorialNegativeExponentialMixtureDensity_pos,
    fun t => by
      rw [factorialCarrierNoGoPolynomial_eq]
      constructor <;> intro h
      · linarith
      · rw [h]
        norm_num,
    hnoGo.2.2.2.2.2.2.1,
    hnoGo.2.2.2.2.2.2.2⟩

end

end RHTower

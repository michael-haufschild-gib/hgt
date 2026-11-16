import GaloisForLFunctions.HTGeometry.SuperPoincareCentral
import GaloisForLFunctions.HTGeometry.HLSKinematics

/-!
# Null polarizations and Clifford central charges

The homogeneous lift `q ↦ (‖q‖, i q)` is injective and isotropic for the complex
Euclidean form. Its polarization is twice the nonnegative Cauchy–Schwarz defect,
which gives the central charge of the associated pair of Clifford generators.
-/

open scoped BigOperators
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.RepresentationLifting.Spinor
noncomputable section

def euclideanComplexForm (n : ℕ) : QuadraticForm ℂ (Option (Fin n) → ℂ) :=
  Matrix.toQuadraticForm' (1 : Matrix (Option (Fin n)) (Option (Fin n)) ℂ)

theorem euclideanComplexForm_apply (n : ℕ) (v : Option (Fin n) → ℂ) :
    euclideanComplexForm n v = v none ^ 2 + ∑ i, v (some i) ^ 2 := by
  simp [euclideanComplexForm, Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply,
    Matrix.one_apply, Fintype.sum_option, pow_two]

def radialLength {n : ℕ} (q : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, q i ^ 2)

/-- A homogeneous null lift, defined even at the zero vector. -/
def nullPolarization {n : ℕ} (q : Fin n → ℝ) : Option (Fin n) → ℂ
  | none => radialLength q
  | some i => Complex.I * (q i : ℂ)

theorem nullPolarization_injective (n : ℕ) : Function.Injective (@nullPolarization n) := by
  intro q r h
  funext i
  have hi := congrFun h (some i)
  change Complex.I * (q i : ℂ) = Complex.I * (r i : ℂ) at hi
  exact Complex.ofReal_injective (mul_left_cancel₀ Complex.I_ne_zero hi)

theorem nullPolarization_square {n : ℕ} (q : Fin n → ℝ) :
    euclideanComplexForm n (nullPolarization q) = 0 := by
  rw [euclideanComplexForm_apply]
  simp only [nullPolarization, mul_pow, Complex.I_sq, neg_one_mul, Finset.sum_neg_distrib]
  rw [← Complex.ofReal_pow, radialLength, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp

theorem nullPolarization_overlap {n : ℕ} (q r : Fin n → ℝ) :
    QuadraticMap.polar (euclideanComplexForm n) (nullPolarization q) (nullPolarization r) =
      (2 * (radialLength q * radialLength r - ∑ i, q i * r i) : ℂ) := by
  rw [QuadraticMap.polar, nullPolarization_square, nullPolarization_square, sub_zero, sub_zero,
    euclideanComplexForm_apply]
  simp only [Pi.add_apply, nullPolarization]
  have he (i : Fin n) : (Complex.I * (q i : ℂ) + Complex.I * (r i : ℂ)) ^ 2 =
      -((q i : ℂ) ^ 2) - (r i : ℂ) ^ 2 - 2 * (q i : ℂ) * (r i : ℂ) := by
    calc
      _ = Complex.I ^ 2 * ((q i : ℂ) + (r i : ℂ)) ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  simp only [he, Finset.sum_sub_distrib, Finset.sum_neg_distrib, mul_assoc,
    ← Finset.mul_sum]
  have hq : (radialLength q : ℂ) ^ 2 = ∑ i, (q i : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, radialLength, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp
  have hr : (radialLength r : ℂ) ^ 2 = ∑ i, (r i : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, radialLength, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp
  push_cast
  linear_combination hq + hr

/-- The overlap is the Cauchy–Schwarz defect of the two real vectors. -/
theorem polarizationOverlap_nonneg {n : ℕ} (q r : Fin n → ℝ) :
    0 ≤ radialLength q * radialLength r - ∑ i, q i * r i := by
  have hq : radialLength q ^ 2 = ∑ i, q i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hr : radialLength r ^ 2 = ∑ i, r i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hrad : 0 ≤ radialLength q * radialLength r :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hs : (∑ i, q i * r i) ^ 2 ≤ (radialLength q * radialLength r) ^ 2 := by
    rw [mul_pow, hq, hr]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ q r
  by_cases hsum : 0 ≤ ∑ i, q i * r i
  · exact sub_nonneg.mpr ((sq_le_sq₀ hsum hrad).mp hs)
  · linarith only [hsum, hrad]

theorem nullPolarization_clifford_square {n : ℕ} (q : Fin n → ℝ) :
    CliffordAlgebra.ι (euclideanComplexForm n) (nullPolarization q) *
      CliffordAlgebra.ι (euclideanComplexForm n) (nullPolarization q) = 0 := by
  rw [CliffordAlgebra.ι_sq_scalar, nullPolarization_square, map_zero]

theorem nullPolarization_centralCharge {n : ℕ} (q r : Fin n → ℝ) :
    (cliffordPairD1N2Central (euclideanComplexForm n) (nullPolarization q)
      (nullPolarization r)).centralCharge =
      algebraMap ℂ (CliffordAlgebra (euclideanComplexForm n))
        (2 * (radialLength q * radialLength r - ∑ i, q i * r i) : ℂ) := by
  change algebraMap ℂ _ (QuadraticMap.polar _ _ _) = _
  rw [nullPolarization_overlap]

#print axioms nullPolarization_injective
#print axioms nullPolarization_square
#print axioms nullPolarization_overlap
#print axioms polarizationOverlap_nonneg
#print axioms nullPolarization_clifford_square
#print axioms nullPolarization_centralCharge

end
end GaloisForLFunctions.RepresentationLifting.Spinor

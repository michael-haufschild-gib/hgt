import Mathlib.Tactic
import Mathlib.Algebra.Module.LinearMap.Star

/-!
# The graded-adjoint square law for Deninger's `K_R`

Let `γ` be a self-adjoint involution in a complex star algebra.  Left multiplication by `γ`
followed by star,

`κ_γ(a) = γ * star a`,

is conjugate-linear and satisfies `κ_γ²(a) = γ * a * γ`.  It therefore squares to `+1` on
the even sector and to `-1` on the odd sector.  This is the algebraic coefficient mechanism
required by Deninger's `K_R`.

The final declarations record the standard even-Fredholm-module consequence: even coefficients
and an odd phase make a represented quantized form homogeneous in the parity of its number of
commutators.  No arithmetic realization, positivity, or Riemann-hypothesis premise is used.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

section Grading

variable {A : Type*} [Ring A]

/-- Conjugation by a proposed grading element. -/
def gradingConjugation (γ a : A) : A := γ * a * γ

/-- The even sector of conjugation by `γ`. -/
def IsGradingEven (γ a : A) : Prop := gradingConjugation γ a = a

/-- The odd sector of conjugation by `γ`. -/
def IsGradingOdd (γ a : A) : Prop := gradingConjugation γ a = -a

/-- If `γ² = 1`, conjugation by `γ` is an involution. -/
theorem gradingConjugation_involutive {γ : A} (hγsq : γ * γ = 1) :
    Function.Involutive (gradingConjugation γ) := by
  intro a
  simp only [gradingConjugation]
  calc
    γ * (γ * a * γ) * γ = (γ * γ) * a * (γ * γ) := by noncomm_ring
    _ = a := by rw [hγsq]; simp

/-- Conjugation by an involution preserves multiplication. -/
theorem gradingConjugation_mul {γ : A} (hγsq : γ * γ = 1) (a b : A) :
    gradingConjugation γ (a * b) =
      gradingConjugation γ a * gradingConjugation γ b := by
  simp only [gradingConjugation]
  calc
    γ * (a * b) * γ = γ * a * (γ * γ) * b * γ := by rw [hγsq]; simp [mul_assoc]
    _ = (γ * a * γ) * (γ * b * γ) := by noncomm_ring

/-- The unit is even for conjugation by an involution. -/
theorem grading_one_even {γ : A} (hγsq : γ * γ = 1) :
    IsGradingEven γ 1 := by
  simp [IsGradingEven, gradingConjugation, hγsq]

/-- An even times an even element is even. -/
theorem grading_even_mul_even {γ a b : A} (hγsq : γ * γ = 1)
    (ha : IsGradingEven γ a) (hb : IsGradingEven γ b) :
    IsGradingEven γ (a * b) := by
  rw [IsGradingEven, gradingConjugation_mul hγsq, ha, hb]

/-- An even times an odd element is odd. -/
theorem grading_even_mul_odd {γ a b : A} (hγsq : γ * γ = 1)
    (ha : IsGradingEven γ a) (hb : IsGradingOdd γ b) :
    IsGradingOdd γ (a * b) := by
  rw [IsGradingOdd, gradingConjugation_mul hγsq, ha, hb]
  exact mul_neg a b

/-- An odd times an even element is odd. -/
theorem grading_odd_mul_even {γ a b : A} (hγsq : γ * γ = 1)
    (ha : IsGradingOdd γ a) (hb : IsGradingEven γ b) :
    IsGradingOdd γ (a * b) := by
  rw [IsGradingOdd, gradingConjugation_mul hγsq, ha, hb]
  exact neg_mul a b

/-- An odd times an odd element is even. -/
theorem grading_odd_mul_odd {γ a b : A} (hγsq : γ * γ = 1)
    (ha : IsGradingOdd γ a) (hb : IsGradingOdd γ b) :
    IsGradingEven γ (a * b) := by
  rw [IsGradingEven, gradingConjugation_mul hγsq, ha, hb]
  exact neg_mul_neg a b

/-- Multiplication of parity bits: `false` is even and `true` is odd. -/
def kRealParityMul : Bool → Bool → Bool
  | false, q => q
  | true, false => true
  | true, true => false

/-- A uniform predicate for the even and odd grading sectors. -/
def IsGradingHomogeneous (γ : A) : Bool → A → Prop
  | false, a => IsGradingEven γ a
  | true, a => IsGradingOdd γ a

/-- Products of homogeneous elements multiply their parity bits. -/
theorem grading_homogeneous_mul {γ a b : A} {p q : Bool} (hγsq : γ * γ = 1)
    (ha : IsGradingHomogeneous γ p a) (hb : IsGradingHomogeneous γ q b) :
    IsGradingHomogeneous γ (kRealParityMul p q) (a * b) := by
  cases p <;> cases q
  · exact grading_even_mul_even hγsq ha hb
  · exact grading_even_mul_odd hγsq ha hb
  · exact grading_odd_mul_even hγsq ha hb
  · exact grading_odd_mul_odd hγsq ha hb

/-- A commutator with an odd phase sends an even coefficient to the odd sector. -/
theorem grading_commutator_odd {γ F a : A} (hγsq : γ * γ = 1)
    (hF : IsGradingOdd γ F) (ha : IsGradingEven γ a) :
    IsGradingOdd γ (F * a - a * F) := by
  calc
    gradingConjugation γ (F * a - a * F) =
        gradingConjugation γ (F * a) - gradingConjugation γ (a * F) := by
          simp [gradingConjugation, mul_sub, sub_mul]
    _ = gradingConjugation γ F * gradingConjugation γ a -
        gradingConjugation γ a * gradingConjugation γ F := by
          rw [gradingConjugation_mul hγsq, gradingConjugation_mul hγsq]
    _ = (-F) * a - a * (-F) := by rw [hF, ha]
    _ = -(F * a - a * F) := by noncomm_ring

/-- Product of commutators in a represented quantized differential form. -/
def quantizedCommutatorProduct (F : A) : List A → A
  | [] => 1
  | a :: as => (F * a - a * F) * quantizedCommutatorProduct F as

/-- Parity of the number of commutators: `false` is even and `true` is odd. -/
def quantizedDegreeParity : List A → Bool
  | [] => false
  | _ :: as => kRealParityMul true (quantizedDegreeParity as)

/-- A product of commutators with an odd phase has its degree parity. -/
theorem quantizedCommutatorProduct_homogeneous {γ F : A} (hγsq : γ * γ = 1)
    (hF : IsGradingOdd γ F) (as : List A)
    (has : ∀ a ∈ as, IsGradingEven γ a) :
    IsGradingHomogeneous γ (quantizedDegreeParity as)
      (quantizedCommutatorProduct F as) := by
  induction as with
  | nil =>
      exact grading_one_even hγsq
  | cons a as ih =>
      exact grading_homogeneous_mul hγsq
        (grading_commutator_odd hγsq hF (has a (by simp)))
        (ih fun b hb => has b (by simp [hb]))

/--
An even leading coefficient followed by quantized commutators has parity equal to form degree.
-/
theorem quantizedForm_homogeneous {γ F a₀ : A} (hγsq : γ * γ = 1)
    (hF : IsGradingOdd γ F) (ha₀ : IsGradingEven γ a₀) (as : List A)
    (has : ∀ a ∈ as, IsGradingEven γ a) :
    IsGradingHomogeneous γ (quantizedDegreeParity as)
      (a₀ * quantizedCommutatorProduct F as) := by
  have ha₀' : IsGradingHomogeneous γ false a₀ := ha₀
  have hprod := quantizedCommutatorProduct_homogeneous hγsq hF as has
  simpa [kRealParityMul] using grading_homogeneous_mul hγsq ha₀' hprod

end Grading

section GradedStar

variable {A : Type*} [Ring A] [StarRing A]

/-- Left multiplication by `γ` followed by star. -/
def gradedAdjoint (γ a : A) : A := γ * star a

/-- The square of the graded adjoint is conjugation by a self-adjoint `γ`. -/
theorem gradedAdjoint_sq {γ a : A} (hγstar : star γ = γ) :
    gradedAdjoint γ (gradedAdjoint γ a) = gradingConjugation γ a := by
  simp [gradedAdjoint, gradingConjugation, hγstar, mul_assoc]

/-- Star of an even element commutes on the right with the grading involution. -/
theorem star_right_comm_of_grading_even {γ a : A} (hγsq : γ * γ = 1)
    (hγstar : star γ = γ) (ha : IsGradingEven γ a) :
    star a * γ = γ * star a := by
  have hstar : γ * star a * γ = star a := by
    simpa [IsGradingEven, gradingConjugation, hγstar, mul_assoc] using congrArg star ha
  calc
    star a * γ = (γ * γ) * (star a * γ) := by rw [hγsq, one_mul]
    _ = γ * (γ * star a * γ) := by noncomm_ring
    _ = γ * star a := by rw [hstar]

/-- Star of an odd element anticommutes on the right with the grading involution. -/
theorem star_right_anticomm_of_grading_odd {γ a : A} (hγsq : γ * γ = 1)
    (hγstar : star γ = γ) (ha : IsGradingOdd γ a) :
    star a * γ = -(γ * star a) := by
  have hstar : γ * star a * γ = -star a := by
    simpa [IsGradingOdd, gradingConjugation, hγstar, mul_assoc] using congrArg star ha
  calc
    star a * γ = (γ * γ) * (star a * γ) := by rw [hγsq, one_mul]
    _ = γ * (γ * star a * γ) := by noncomm_ring
    _ = γ * (-star a) := by rw [hstar]
    _ = -(γ * star a) := by rw [mul_neg]

/-- The graded adjoint preserves the even sector. -/
theorem gradedAdjoint_even {γ a : A} (hγsq : γ * γ = 1)
    (hγstar : star γ = γ) (ha : IsGradingEven γ a) :
    IsGradingEven γ (gradedAdjoint γ a) := by
  rw [IsGradingEven, gradingConjugation, gradedAdjoint]
  calc
    γ * (γ * star a) * γ = star a * γ := by
      rw [← mul_assoc γ γ, hγsq, one_mul]
    _ = γ * star a := star_right_comm_of_grading_even hγsq hγstar ha

/-- The graded adjoint preserves the odd sector. -/
theorem gradedAdjoint_odd {γ a : A} (hγsq : γ * γ = 1)
    (hγstar : star γ = γ) (ha : IsGradingOdd γ a) :
    IsGradingOdd γ (gradedAdjoint γ a) := by
  rw [IsGradingOdd, gradingConjugation, gradedAdjoint]
  calc
    γ * (γ * star a) * γ = star a * γ := by
      rw [← mul_assoc γ γ, hγsq, one_mul]
    _ = -(γ * star a) := star_right_anticomm_of_grading_odd hγsq hγstar ha

/-- The graded adjoint squares to `+1` on the even sector. -/
theorem gradedAdjoint_sq_of_even {γ a : A} (hγstar : star γ = γ)
    (ha : IsGradingEven γ a) :
    gradedAdjoint γ (gradedAdjoint γ a) = a := by
  rw [gradedAdjoint_sq hγstar, ha]

/-- The graded adjoint squares to `-1` on the odd sector. -/
theorem gradedAdjoint_sq_of_odd {γ a : A} (hγstar : star γ = γ)
    (ha : IsGradingOdd γ a) :
    gradedAdjoint γ (gradedAdjoint γ a) = -a := by
  rw [gradedAdjoint_sq hγstar, ha]

section Complex

variable [Algebra ℂ A] [StarModule ℂ A]

/-- The graded adjoint is conjugate-linear over `ℂ`. -/
theorem gradedAdjoint_smul (γ a : A) (z : ℂ) :
    gradedAdjoint γ (z • a) = star z • gradedAdjoint γ a := by
  simp [gradedAdjoint, Algebra.mul_smul_comm]

/-- The graded adjoint bundled as a complex conjugate-linear map. -/
def gradedAdjointₛₗ (γ : A) : A →ₗ⋆[ℂ] A where
  toFun := gradedAdjoint γ
  map_add' a b := by simp [gradedAdjoint, mul_add]
  map_smul' z a := by
    rw [gradedAdjoint_smul]
    rfl

end Complex

end GradedStar

end RHTower
end GaloisForLFunctions

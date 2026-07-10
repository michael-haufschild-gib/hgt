import GaloisForLFunctions.DifferentialIndependence
import Mathlib.Tactic

/-!
# Several commuting difference operators and one derivation

This file supplies the algebraic interface used by the simultaneous telescoping layer. It records
several commuting field automorphisms which fix the coefficient field and commute with the
derivation, defines the action of a constant-coefficient differential operator, and proves that
one linear differential relation among compatible primitives produces the same primitive in every
telescoping equation.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- A field with several pairwise commuting automorphisms which fix `C` and commute with the
derivation. -/
structure CommutingDifferenceDifferentialField
    (ι C K : Type*) [Field C] [Field K] [Algebra C K] [Differential K] where
  aut : ι → K ≃+* K
  aut_comm : ∀ i j x, aut i (aut j x) = aut j (aut i x)
  aut_deriv : ∀ i x, aut i x′ = (aut i x)′
  aut_algebraMap : ∀ i c, aut i (algebraMap C K c) = algebraMap C K c

/-- The action of `L ∈ C[δ]` on `x`, with the polynomial exponent interpreted as derivative
order. -/
def differentialOperatorApply
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (L : Polynomial C) (x : K) : K :=
  L.sum fun n c => algebraMap C K c * differentialJet n x

@[simp]
theorem differentialOperatorApply_zero
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K] (x : K) :
    differentialOperatorApply (0 : Polynomial C) x = 0 := by
  simp [differentialOperatorApply]

/-- Difference automorphisms commute with every differential jet. -/
theorem CommutingDifferenceDifferentialField.aut_differentialJet
    {ι C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (i : ι) (n : ℕ) (x : K) :
    S.aut i (differentialJet n x) = differentialJet n (S.aut i x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, differentialJet_succ, S.aut_deriv, ih]

theorem differentialJet_sub
    {K : Type*} [Field K] [Differential K] (n : ℕ) (x y : K) :
    differentialJet n (x - y) = differentialJet n x - differentialJet n y := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, differentialJet_succ, differentialJet_succ, ih, map_sub]

/-- Constant-coefficient differential operators are additive. -/
theorem differentialOperatorApply_sub
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (L : Polynomial C) (x y : K) :
    differentialOperatorApply L (x - y) =
      differentialOperatorApply L x - differentialOperatorApply L y := by
  classical
  unfold differentialOperatorApply
  simp_rw [differentialJet_sub, mul_sub]
  rw [Polynomial.sum_def, Polynomial.sum_def, Polynomial.sum_def]
  simp only [Finset.sum_sub_distrib]

/-- A difference automorphism commutes with every constant-coefficient differential operator. -/
theorem CommutingDifferenceDifferentialField.aut_differentialOperatorApply
    {ι C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (i : ι) (L : Polynomial C) (x : K) :
    S.aut i (differentialOperatorApply L x) =
      differentialOperatorApply L (S.aut i x) := by
  classical
  unfold differentialOperatorApply
  rw [Polynomial.sum_def, Polynomial.sum_def]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul, S.aut_algebraMap, S.aut_differentialJet]

/-- The additive defect `(σᵢ - 1)x`. -/
def CommutingDifferenceDifferentialField.defect
    {ι C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (i : ι) (x : K) : K :=
  S.aut i x - x

/-- Applying a constant-coefficient differential operator commutes with taking a defect. -/
theorem CommutingDifferenceDifferentialField.defect_differentialOperatorApply
    {ι C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (i : ι) (L : Polynomial C) (x : K) :
    S.defect i (differentialOperatorApply L x) =
      differentialOperatorApply L (S.defect i x) := by
  rw [CommutingDifferenceDifferentialField.defect, S.aut_differentialOperatorApply]
  exact (differentialOperatorApply_sub L (S.aut i x) x).symm

theorem CommutingDifferenceDifferentialField.defect_add
    {ι C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (i : ι) (x y : K) :
    S.defect i (x + y) = S.defect i x + S.defect i y := by
  simp only [CommutingDifferenceDifferentialField.defect, map_add]
  abel

theorem CommutingDifferenceDifferentialField.defect_sum
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (i : ι)
    (A : Finset κ) (x : κ → K) :
    S.defect i (∑ k ∈ A, x k) = ∑ k ∈ A, S.defect i (x k) := by
  simp only [CommutingDifferenceDifferentialField.defect, map_sum]
  rw [Finset.sum_sub_distrib]

/-- A family `yₖ` with compatible primitive equations `(σᵢ - 1)yₖ = aᵢₖ`. -/
def CompatiblePrimitiveSystem
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K)
    (y : κ → K) (a : ι → κ → K) : Prop :=
  ∀ i k, S.defect i (y k) = a i k

/-- An element fixed by every difference automorphism. -/
def JointFixed
    {ι C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (x : K) : Prop :=
  ∀ i, S.aut i x = x

/-- The defects of a compatible primitive system satisfy the pairwise integrability equations. -/
theorem CompatiblePrimitiveSystem.cocycle
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K)
    {y : κ → K} {a : ι → κ → K} (hsys : CompatiblePrimitiveSystem S y a) :
    ∀ i j k, S.defect i (a j k) = S.defect j (a i k) := by
  intro i j k
  rw [← hsys j k, ← hsys i k]
  simp only [CommutingDifferenceDifferentialField.defect, map_sub]
  rw [S.aut_comm]
  abel

/-- Joint fixedness is exactly vanishing of all additive defects. -/
theorem jointFixed_iff_defect_eq_zero
    {ι C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (x : K) :
    JointFixed S x ↔ ∀ i, S.defect i x = 0 := by
  simp [JointFixed, CommutingDifferenceDifferentialField.defect, sub_eq_zero]

theorem CommutingDifferenceDifferentialField.defect_eq_zero_of_jointFixed
    {ι C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) {x : K}
    (hx : JointFixed S x) (i : ι) : S.defect i x = 0 := by
  rw [CommutingDifferenceDifferentialField.defect, hx i, sub_self]

/-- One linear differential relation among compatible primitives gives one common primitive `g`
in all simultaneous telescoping equations. -/
theorem simultaneous_telescoping_of_linear_relation
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K)
    (A : Finset κ) (y : κ → K) (a : ι → κ → K)
    (hsys : CompatiblePrimitiveSystem S y a)
    (L : κ → Polynomial C) (g c : K) (hc : JointFixed S c)
    (hrel : ∑ k ∈ A, differentialOperatorApply (L k) (y k) = g + c) :
    ∀ i, S.defect i g =
      ∑ k ∈ A, differentialOperatorApply (L k) (a i k) := by
  intro i
  have hdef := congrArg (S.defect i) hrel
  rw [S.defect_sum] at hdef
  simp_rw [S.defect_differentialOperatorApply, hsys i] at hdef
  rw [S.defect_add, S.defect_eq_zero_of_jointFixed hc i, add_zero] at hdef
  exact hdef.symm

end

end GaloisForLFunctions

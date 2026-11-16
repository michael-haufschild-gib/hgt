import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import GaloisForLFunctions.HTGeometry.ReflectionShiftGroupoid

/-!
# Exact difference matrices and collision coordinates

All pairwise differences contain exactly one fewer independent coordinate
than the original nonempty configuration. The missing coordinate is common
translation. A rooted row gives explicit coordinates on the quotient, and
all collision hyperplanes have trivial common intersection there.
-/

noncomputable section

namespace GaloisForLFunctions.HilbertMetric

variable {K I : Type*} [Field K]

/-- The linear map recording every oriented pairwise displacement. -/
def pairDifferenceMap : (I → K) →ₗ[K] Matrix I I K where
  toFun a i j := a j - a i
  map_add' a b := by
    ext i j
    change (a j + b j) - (a i + b i) = (a j - a i) + (b j - b i)
    ring
  map_smul' c a := by
    ext i j
    change c * a j - c * a i = c * (a j - a i)
    ring

/-- Exact matrices are displacement matrices of configurations. -/
def exactDifferenceSpace (K I : Type*) [Field K] : Submodule K (Matrix I I K) :=
  LinearMap.range pairDifferenceMap

/-- The only lost information is the common translation of all coordinates. -/
theorem pairDifferenceMap_eq_iff (i₀ : I) (a b : I → K) :
    pairDifferenceMap a = pairDifferenceMap b ↔
      ∀ i, a i - b i = a i₀ - b i₀ := by
  constructor
  · intro h i
    have he := congrFun (congrFun h i₀) i
    change a i - a i₀ = b i - b i₀ at he
    linear_combination he
  · intro h
    ext i j
    change a j - a i = b j - b i
    linear_combination h j - h i

/-- The kernel is precisely the constant configurations. -/
theorem pairDifferenceMap_mem_ker_iff (i₀ : I) (a : I → K) :
    a ∈ LinearMap.ker pairDifferenceMap ↔ ∀ i, a i = a i₀ := by
  change pairDifferenceMap a = 0 ↔ _
  rw [← map_zero pairDifferenceMap, pairDifferenceMap_eq_iff i₀]
  simp only [Pi.zero_apply, sub_zero]

/-- Exactness is equivalent to the additive triangle law. -/
theorem mem_exactDifferenceSpace_iff (i₀ : I) (A : Matrix I I K) :
    A ∈ exactDifferenceSpace K I ↔ ∀ i j k, A i j + A j k = A i k := by
  constructor
  · rintro ⟨a, rfl⟩ i j k
    change (a j - a i) + (a k - a j) = a k - a i
    ring
  · intro h
    refine ⟨A i₀, ?_⟩
    ext i j
    change A i₀ j - A i₀ i = A i j
    linear_combination -(h i₀ i j)

/-- Quotienting configurations by their constant kernel gives exact matrices. -/
def pairDifferenceQuotientEquiv :
    ((I → K) ⧸ LinearMap.ker (pairDifferenceMap (K := K) (I := I))) ≃ₗ[K]
      exactDifferenceSpace K I :=
  LinearMap.quotKerEquivRange (pairDifferenceMap (K := K) (I := I))

/-- Rooted coordinates on exact matrices; inverse inserts a zero anchor. -/
def exactDifferenceCoordinates (n : ℕ) :
    exactDifferenceSpace K (Fin (n + 1)) ≃ₗ[K] (Fin n → K) where
  toFun A i := A.1 0 i.succ
  invFun v := ⟨pairDifferenceMap (Fin.cases 0 v), ⟨Fin.cases 0 v, rfl⟩⟩
  left_inv A := by
    apply Subtype.ext
    rcases A with ⟨A, a, rfl⟩
    ext i j
    change Fin.cases 0 (fun k => a k.succ - a 0) j -
      Fin.cases 0 (fun k => a k.succ - a 0) i = a j - a i
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j <;> simp
  right_inv v := by
    funext i
    change Fin.cases 0 v i.succ - Fin.cases 0 v 0 = v i
    simp
  map_add' A B := rfl
  map_smul' c A := rfl

/-- The exact-matrix space has the expected dimension in every field. -/
theorem finrank_exactDifferenceSpace (n : ℕ) :
    Module.finrank K (exactDifferenceSpace K (Fin (n + 1))) = n := by
  rw [(exactDifferenceCoordinates (K := K) n).finrank_eq]
  simp

/-- Collision with the anchor is exactly vanishing of one rooted coordinate. -/
theorem exactDifferenceCoordinates_collision (n : ℕ)
    (A : exactDifferenceSpace K (Fin (n + 1))) (i : Fin n) :
    exactDifferenceCoordinates n A i = 0 ↔ A.1 0 i.succ = 0 := Iff.rfl

/-- The rooted collision arrangement is essential: its common intersection is zero. -/
theorem exactDifference_rootCollisions_iff (n : ℕ)
    (A : exactDifferenceSpace K (Fin (n + 1))) :
    (∀ i : Fin n, A.1 0 i.succ = 0) ↔ A = 0 := by
  constructor
  · intro h
    apply (exactDifferenceCoordinates n).injective
    change (fun i : Fin n => A.1 0 i.succ) = (fun _ => 0)
    funext i
    exact h i
  · rintro rfl
    intro i
    rfl

/-- Existing shifted-function differences form an exact matrix at every evaluation point. -/
theorem shiftDifference_mem_exactDifferenceSpace (L : ℂ → ℂ) (a : I → ℂ) (s : ℂ) :
    (fun i j => HTGeometry.shiftDifference L (a j) (a i) s) ∈
      exactDifferenceSpace ℂ I :=
  ⟨fun i => L (s + a i), rfl⟩

/-- Equality of all shifted differences is exactly an undetectable common offset. -/
theorem shiftDifference_matrix_eq_iff (i₀ : I) (L M : ℂ → ℂ) (a : I → ℂ) (s : ℂ) :
    (fun i j => HTGeometry.shiftDifference L (a j) (a i) s) =
        (fun i j => HTGeometry.shiftDifference M (a j) (a i) s) ↔
      ∀ i, L (s + a i) - M (s + a i) = L (s + a i₀) - M (s + a i₀) :=
  pairDifferenceMap_eq_iff i₀ _ _

#print axioms pairDifferenceQuotientEquiv
#print axioms finrank_exactDifferenceSpace
#print axioms exactDifference_rootCollisions_iff
#print axioms shiftDifference_matrix_eq_iff

end GaloisForLFunctions.HilbertMetric

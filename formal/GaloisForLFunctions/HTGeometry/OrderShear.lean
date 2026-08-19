import GaloisForLFunctions.HTGeometry.HumbertAction

/-!
# Shears over an order

An elementary shear over the order is a transvection, and its matrix of embeddings at each place is
the transvection with the embedded coefficient.  When the shear moves a later basis vector by an
earlier one it is unipotent upper triangular at every place, so by the placewise description of the
action it twists each of the `d` Gram–Schmidt data without changing any of their diagonals.

This is the move that size reduction over an order uses; the coefficient is supplied by rounding.

* `orderShear` : the shear, as an element of `SL_n(R)`.
* `placeMatrix_orderShear` : **its matrix of embeddings is the embedded transvection.**
* `isUnipotentUpper_transvection` : it is unipotent upper triangular.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {nb d : ℕ} {R : Type*} [CommRing R]

theorem transvection_apply (j i a b : Fin nb) (c : R) :
    Matrix.transvection j i c a b
      = (if a = b then (1 : R) else 0) + (if a = j ∧ b = i then c else 0) := by
  classical
  have h1 : (1 : Matrix (Fin nb) (Fin nb) R) a b = (if a = b then (1 : R) else 0) := by
    by_cases hab : a = b
    · rw [hab, Matrix.one_apply_eq, if_pos rfl]
    · rw [Matrix.one_apply_ne hab, if_neg hab]
  have h2 : Matrix.single j i c a b = (if a = j ∧ b = i then c else 0) := by
    by_cases h : a = j ∧ b = i
    · simp [h]
    · simp [Matrix.single_apply, h]
      tauto
  show ((1 : Matrix (Fin nb) (Fin nb) R) + Matrix.single j i c) a b = _
  rw [Matrix.add_apply, h1, h2]

/-- **The embeddings of a transvection are the embedded transvections.** -/
theorem placeMatrix_orderShear (T : RealOrderData R d) (v : Fin d) (j i : Fin nb) (α : R) :
    placeMatrix T v (Matrix.transvection j i α) = Matrix.transvection j i (T.emb v α) := by
  classical
  ext a b
  show T.emb v (Matrix.transvection j i α a b) = _
  rw [transvection_apply, transvection_apply, map_add]
  have e1 : T.emb v (if a = b then (1 : R) else 0) = (if a = b then (1 : ℝ) else 0) := by
    by_cases hab : a = b <;> simp [hab]
  have e2 : T.emb v (if a = j ∧ b = i then α else 0)
      = (if a = j ∧ b = i then T.emb v α else 0) := by
    by_cases h : a = j ∧ b = i <;> simp [h]
  rw [e1, e2]

/-- A transvection moving a later index by an earlier one is unipotent upper triangular. -/
theorem isUnipotentUpper_transvection {j i : Fin nb} (hji : j < i) (c : ℝ) :
    IsUnipotentUpper (Matrix.transvection j i c) := by
  classical
  constructor
  · intro a b hba
    rw [transvection_apply]
    have h1 : ¬ (a = b) := fun h => absurd (h ▸ hba) (lt_irrefl _)
    have h2 : ¬ (a = j ∧ b = i) := by
      rintro ⟨rfl, rfl⟩
      exact absurd hji (not_lt.2 (le_of_lt hba))
    rw [if_neg h1, if_neg h2, add_zero]
  · intro a
    rw [transvection_apply]
    have h2 : ¬ (a = j ∧ a = i) := by
      rintro ⟨rfl, h⟩
      exact absurd (h ▸ hji) (lt_irrefl _)
    rw [if_pos rfl, if_neg h2, add_zero]

/-- The elementary shear over an order, as an element of the special linear group. -/
def orderShear {j i : Fin nb} (hji : j ≠ i) (α : R) :
    Matrix.SpecialLinearGroup (Fin nb) R :=
  ⟨Matrix.transvection j i α, Matrix.det_transvection_of_ne j i hji α⟩

@[simp]
theorem orderShear_coe {j i : Fin nb} (hji : j ≠ i) (α : R) :
    ((orderShear hji α : Matrix.SpecialLinearGroup (Fin nb) R) :
      Matrix (Fin nb) (Fin nb) R) = Matrix.transvection j i α := rfl

/-- **A shear twists each Gram–Schmidt datum without changing its diagonal.** -/
theorem humbertForm_shear (T : RealOrderData R d) (Jv : Fin d → JacobiData nb)
    {j i : Fin nb} (hji : j < i) (α : R) :
    (orderRepR T.basis (Matrix.transvection j i α))ᵀ
        * humbertForm T (Matrix.of fun a b => fun v => (Jv v).form a b)
        * orderRepR T.basis (Matrix.transvection j i α)
      = humbertForm T (Matrix.of fun a b => fun v =>
          ((Jv v).twist (isUnipotentUpper_transvection hji (T.emb v α))).form a b) := by
  rw [humbertForm_congr]
  congr 1
  refine funext fun a => funext fun b => funext fun v => ?_
  show ((placeMatrix T v (Matrix.transvection j i α))ᵀ
      * (Matrix.of fun x y => (Jv v).form x y)
      * placeMatrix T v (Matrix.transvection j i α)) a b
    = ((Jv v).twist (isUnipotentUpper_transvection hji (T.emb v α))).form a b
  rw [placeMatrix_orderShear, JacobiData.twist_form]
  rfl

end GaloisForLFunctions.HTGeometry

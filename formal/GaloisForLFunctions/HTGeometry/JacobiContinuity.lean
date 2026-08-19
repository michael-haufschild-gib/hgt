import GaloisForLFunctions.HTGeometry.JacobiUniqueness
import GaloisForLFunctions.HTGeometry.PositiveDefiniteConeAction

/-!
# The Jacobi coordinates depend continuously on the form

The diagonal is a ratio of consecutive leading minors, hence continuous on the cone where all leading
minors are positive; the unipotent factor is then computed from the form and the diagonal by the LDL
recursion, so it is continuous by induction on the row index.

* `coneMat`, `jacOf` : the form and its Jacobi data.
* `continuous_jacOf_d`, `continuous_jacOf_U` : **the coordinates are continuous.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- A point of the cone, read as a matrix. -/
def coneMat (A : posDefCone n) : Matrix (Fin n) (Fin n) ℝ :=
  ((A : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ)

theorem continuous_coneMat : Continuous (coneMat (n := n)) :=
  continuous_subtype_val.comp continuous_subtype_val

theorem coneMat_posDef (A : posDefCone n) : (coneMat A).PosDef := A.2

/-- The Jacobi data of a point of the cone. -/
noncomputable def jacOf (A : posDefCone n) : JacobiData n :=
  Classical.choose (exists_jacobiData (coneMat_posDef A))

theorem jacOf_form (A : posDefCone n) : (jacOf A).form = coneMat A :=
  Classical.choose_spec (exists_jacobiData (coneMat_posDef A))

/-- A leading minor of a point of the cone. -/
noncomputable def minorDet {k : ℕ} (hk : k ≤ n) (A : posDefCone n) : ℝ :=
  (leadingBlock hk (coneMat A)).det

theorem continuous_minorDet {k : ℕ} (hk : k ≤ n) : Continuous (minorDet (n := n) hk) := by
  refine Continuous.matrix_det ?_
  exact continuous_matrix fun i j => continuous_coneMat.matrix_elem _ _

theorem minorDet_pos {k : ℕ} (hk : k ≤ n) (A : posDefCone n) : 0 < minorDet hk A := by
  rw [minorDet, ← jacOf_form A, det_leadingBlock_form hk (jacOf A)]
  exact Finset.prod_pos fun m _ => (jacOf A).pos _

theorem jacOf_d_eq (A : posDefCone n) (l : Fin n) :
    (jacOf A).d l = minorDet l.isLt A / minorDet (Nat.le_of_succ_le l.isLt) A := by
  have h := det_leadingBlock_succ (jacOf A) l.isLt
  rw [jacOf_form] at h
  have hll : (⟨(l : ℕ), l.isLt⟩ : Fin n) = l := Fin.ext rfl
  rw [hll] at h
  rw [eq_div_iff (ne_of_gt (minorDet_pos (Nat.le_of_succ_le l.isLt) A))]
  rw [minorDet, minorDet, mul_comm]
  exact h.symm

/-- **The Jacobi diagonal is continuous.** -/
theorem continuous_jacOf_d (l : Fin n) : Continuous (fun A : posDefCone n => (jacOf A).d l) := by
  have heq : (fun A : posDefCone n => (jacOf A).d l)
      = fun A : posDefCone n => minorDet l.isLt A / minorDet (Nat.le_of_succ_le l.isLt) A := by
    funext A
    exact jacOf_d_eq A l
  rw [heq]
  exact Continuous.div (continuous_minorDet _) (continuous_minorDet _)
    fun A => ne_of_gt (minorDet_pos _ A)

theorem jacOf_U_eq (A : posDefCone n) (i j : Fin n) :
    (jacOf A).U i j
      = (coneMat A i j - ∑ m ∈ Finset.univ.filter (fun m : Fin n => m < i),
          (jacOf A).d m * (jacOf A).U m i * (jacOf A).U m j) / (jacOf A).d i := by
  have h := (jacOf A).ldl_recursion i j
  rw [jacOf_form] at h
  rw [eq_div_iff (ne_of_gt ((jacOf A).pos i)), mul_comm]
  exact h

/-- **The unipotent factor is continuous.** -/
theorem continuous_jacOf_U (i j : Fin n) :
    Continuous (fun A : posDefCone n => (jacOf A).U i j) := by
  classical
  have key : ∀ k : ℕ, ∀ i : Fin n, (i : ℕ) = k → ∀ j : Fin n,
      Continuous (fun A : posDefCone n => (jacOf A).U i j) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
        intro i hi j
        have heq : (fun A : posDefCone n => (jacOf A).U i j)
            = fun A : posDefCone n =>
              (coneMat A i j - ∑ m ∈ Finset.univ.filter (fun m : Fin n => m < i),
                (jacOf A).d m * (jacOf A).U m i * (jacOf A).U m j) / (jacOf A).d i := by
          funext A
          exact jacOf_U_eq A i j
        rw [heq]
        refine Continuous.div ?_ (continuous_jacOf_d i) fun A => ne_of_gt ((jacOf A).pos i)
        refine Continuous.sub (continuous_coneMat.matrix_elem i j) ?_
        refine continuous_finsetSum _ fun m hm => ?_
        rw [Finset.mem_filter] at hm
        have hmk : (m : ℕ) < k := by
          have := Fin.lt_def.1 hm.2
          omega
        exact ((continuous_jacOf_d m).mul (ih (m : ℕ) hmk m rfl i)).mul (ih (m : ℕ) hmk m rfl j)
  exact key (i : ℕ) i rfl j

end GaloisForLFunctions.HTGeometry

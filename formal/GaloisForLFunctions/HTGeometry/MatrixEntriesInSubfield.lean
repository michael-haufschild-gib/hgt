import GaloisForLFunctions.HTGeometry.ThreeParticleLegsRing
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Matrices with entries in an intermediate field

Closure of the entrywise-membership predicate under the matrix operations used by the Sutherland
solve: sums, products, tensor legs, determinants, adjugates and hence inverses.  This is the
bookkeeping that turns "the linear system has coefficients in `S`" into "its unique solution has
entries in `S`".
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Every entry of a matrix lies in a given intermediate field. -/
def EntriesIn (S : IntermediateField F E) {m n : Type*} (A : Matrix m n E) : Prop :=
  ∀ i j, A i j ∈ S

namespace EntriesIn

variable {S : IntermediateField F E} {m n p : Type*}

theorem add {A B : Matrix m n E} (hA : EntriesIn S A) (hB : EntriesIn S B) :
    EntriesIn S (A + B) := fun i j => S.add_mem (hA i j) (hB i j)

theorem sub {A B : Matrix m n E} (hA : EntriesIn S A) (hB : EntriesIn S B) :
    EntriesIn S (A - B) := fun i j => S.sub_mem (hA i j) (hB i j)

theorem neg {A : Matrix m n E} (hA : EntriesIn S A) : EntriesIn S (-A) :=
  fun i j => S.neg_mem (hA i j)

theorem smul {c : E} (hc : c ∈ S) {A : Matrix m n E} (hA : EntriesIn S A) :
    EntriesIn S (c • A) := fun i j => S.mul_mem hc (hA i j)

theorem mul [Fintype n] [DecidableEq n] {A : Matrix m n E} {B : Matrix n p E}
    (hA : EntriesIn S A) (hB : EntriesIn S B) : EntriesIn S (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subalgebra.sum_mem _ fun k _ => S.mul_mem (hA i k) (hB k j)

theorem one [DecidableEq m] : EntriesIn S (1 : Matrix m m E) := by
  intro i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem zero : EntriesIn S (0 : Matrix m n E) := fun _ _ => S.zero_mem

theorem single [DecidableEq m] [DecidableEq n] (i₀ : m) (j₀ : n) :
    EntriesIn S (Matrix.single i₀ j₀ (1 : E)) := by
  intro i j
  by_cases h : i₀ = i ∧ j₀ = j <;> simp [h]

theorem map_algebraMap (A : Matrix m n F) : EntriesIn S (A.map (algebraMap F E)) :=
  fun i j => S.algebraMap_mem (A i j)

theorem legLeft {κ : Type*} [DecidableEq κ] {A : Matrix (κ × κ) (κ × κ) E}
    (hA : EntriesIn S A) : EntriesIn S (HTGeometry.legLeft A) := by
  intro i j
  rw [legLeft_apply]
  exact S.mul_mem (hA _ _) (one (S := S) (m := κ) i.2.2 j.2.2)

theorem legRight {κ : Type*} [DecidableEq κ] {A : Matrix (κ × κ) (κ × κ) E}
    (hA : EntriesIn S A) : EntriesIn S (HTGeometry.legRight A) := by
  intro i j
  rw [legRight_apply]
  exact S.mul_mem (one (S := S) (m := κ) i.1 j.1) (hA _ _)

theorem det [Fintype m] [DecidableEq m] {A : Matrix m m E} (hA : EntriesIn S A) :
    A.det ∈ S := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  have hprod : (∏ i, A (σ i) i) ∈ S := Subalgebra.prod_mem _ fun i _ => hA _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]
    exact hprod
  · rw [h]
    simpa using S.neg_mem hprod

theorem updateRow [DecidableEq m] {A : Matrix m n E} (hA : EntriesIn S A) (i₀ : m)
    {v : n → E} (hv : ∀ j, v j ∈ S) : EntriesIn S (A.updateRow i₀ v) := by
  intro i j
  by_cases h : i = i₀
  · subst h; simpa using hv j
  · simpa [Matrix.updateRow_ne h] using hA i j

theorem adjugate [Fintype m] [DecidableEq m] {A : Matrix m m E} (hA : EntriesIn S A) :
    EntriesIn S A.adjugate := by
  intro i j
  rw [Matrix.adjugate_apply]
  refine det (updateRow hA j ?_)
  intro k
  by_cases h : i = k <;> simp [h]

theorem inv [Fintype m] [DecidableEq m] {A : Matrix m m E} (hA : EntriesIn S A) :
    EntriesIn S A⁻¹ := by
  intro i j
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact S.mul_mem (S.inv_mem (det hA)) (adjugate hA i j)

theorem mulVec [Fintype n] {A : Matrix m n E} (hA : EntriesIn S A) {v : n → E}
    (hv : ∀ j, v j ∈ S) (i : m) : (A *ᵥ v) i ∈ S := by
  rw [Matrix.mulVec, dotProduct]
  exact Subalgebra.sum_mem _ fun k _ => S.mul_mem (hA i k) (hv k)

end EntriesIn

end GaloisForLFunctions.HTGeometry

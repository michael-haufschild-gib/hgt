import GaloisForLFunctions.HTGeometry.SiegelDescentStep

/-!
# The integral unimodular orbit

The moves of lattice basis reduction are congruences by integral matrices with an invertible
integral inverse: the shears that size-reduce and the permutation matrices that swap.  This file
records that class and its closure properties, and the orbit of a form under it.

* `IsIntUnimodular` : a real matrix that is the cast of an invertible integral matrix.
* `IsIntUnimodular.mul`, `isIntUnimodular_one` : closure.
* `IsIntUnipotent.isIntUnimodular`, `isIntUnimodular_permMatrix` : the two moves qualify.
* `InOrbit` : the congruates of a form by such matrices, closed under both moves.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- A real matrix that is the cast of an invertible integral matrix. -/
def IsIntUnimodular (γ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ g : Matrix (Fin n) (Fin n) ℤ, IsUnit g ∧ ∀ a b, γ a b = (g a b : ℝ)

theorem isIntUnimodular_one : IsIntUnimodular (1 : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  refine ⟨1, isUnit_one, fun a b => ?_⟩
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem IsIntUnimodular.mul {γ δ : Matrix (Fin n) (Fin n) ℝ}
    (hγ : IsIntUnimodular γ) (hδ : IsIntUnimodular δ) : IsIntUnimodular (γ * δ) := by
  obtain ⟨g, hgu, hg⟩ := hγ
  obtain ⟨h, hhu, hh⟩ := hδ
  refine ⟨g * h, hgu.mul hhu, fun a b => ?_⟩
  rw [Matrix.mul_apply, Matrix.mul_apply]
  push_cast
  exact Finset.sum_congr rfl fun m _ => by rw [hg a m, hh m b]

/-- An integral shear is unimodular: its integral form is upper triangular with unit diagonal. -/
theorem IsIntUnipotent.isIntUnimodular {γ : Matrix (Fin n) (Fin n) ℝ}
    (hγ : IsIntUnipotent γ) : IsIntUnimodular γ := by
  classical
  obtain ⟨g, hg⟩ := hγ.1
  have hglow : ∀ a b : Fin n, b < a → g a b = 0 := by
    intro a b hba
    have := hγ.2.1 a b hba
    rw [hg a b] at this
    exact_mod_cast this
  have hgdiag : ∀ a : Fin n, g a a = 1 := by
    intro a
    have := hγ.2.2 a
    rw [hg a a] at this
    exact_mod_cast this
  have hdet : g.det = 1 := by
    have hbt : g.BlockTriangular id := fun a b hab => hglow a b hab
    rw [Matrix.det_of_upperTriangular hbt]
    simp [hgdiag]
  exact ⟨g, (Matrix.isUnit_iff_isUnit_det g).2 (by rw [hdet]; exact isUnit_one), hg⟩

/-- The integral permutation matrix. -/
def permMatrixInt (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun a b => if b = σ a then 1 else 0

theorem permMatrix_eq_cast (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    permMatrix σ a b = ((permMatrixInt σ a b : ℤ) : ℝ) := by
  by_cases h : b = σ a <;> simp [permMatrix, permMatrixInt, h]

theorem permMatrixInt_mul_inv (σ : Equiv.Perm (Fin n)) :
    permMatrixInt σ * permMatrixInt σ⁻¹ = 1 := by
  classical
  ext a c
  rw [Matrix.mul_apply]
  refine (Finset.sum_eq_single (σ a) (fun b _ hb => ?_)
    (fun hcon => absurd (Finset.mem_univ (σ a)) hcon)).trans ?_
  · show (if b = σ a then (1 : ℤ) else 0) * _ = 0
    simp [hb]
  · show (if σ a = σ a then (1 : ℤ) else 0) * (if c = σ⁻¹ (σ a) then 1 else 0)
      = (1 : Matrix (Fin n) (Fin n) ℤ) a c
    rw [if_pos rfl, one_mul]
    have hinv : σ⁻¹ (σ a) = a := by simp
    rw [hinv]
    by_cases hca : c = a
    · simp [hca, Matrix.one_apply]
    · simp [hca, Ne.symm hca]

theorem isIntUnimodular_permMatrix (σ : Equiv.Perm (Fin n)) :
    IsIntUnimodular (permMatrix σ) := by
  classical
  haveI : Invertible (permMatrixInt σ) :=
    ⟨permMatrixInt σ⁻¹, by
      have := permMatrixInt_mul_inv σ⁻¹
      rwa [inv_inv] at this, permMatrixInt_mul_inv σ⟩
  exact ⟨permMatrixInt σ, isUnit_of_invertible _, permMatrix_eq_cast σ⟩

/-- The congruates of a form by an integral unimodular matrix. -/
def InOrbit (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ γ : Matrix (Fin n) (Fin n) ℝ, IsIntUnimodular γ ∧ B = γᵀ * A * γ

theorem inOrbit_refl (A : Matrix (Fin n) (Fin n) ℝ) : InOrbit A A :=
  ⟨1, isIntUnimodular_one, by rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]⟩

theorem InOrbit.congr {A B : Matrix (Fin n) (Fin n) ℝ} (hB : InOrbit A B)
    {δ : Matrix (Fin n) (Fin n) ℝ} (hδ : IsIntUnimodular δ) : InOrbit A (δᵀ * B * δ) := by
  obtain ⟨γ, hγ, rfl⟩ := hB
  refine ⟨γ * δ, hγ.mul hδ, ?_⟩
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

end GaloisForLFunctions.HTGeometry

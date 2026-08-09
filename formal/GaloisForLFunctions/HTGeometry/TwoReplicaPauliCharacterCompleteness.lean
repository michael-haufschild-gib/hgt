import GaloisForLFunctions.HTGeometry.FiniteQubitPauliComplexBasis
import GaloisForLFunctions.HTGeometry.PauliCharacterFirstDefectCovariance

/-!
# The paired-Pauli characters exhaust the two-replica space

The phase-free Pauli labels carry a product, and the conjugation sign is multiplicative in it.  A
Kronecker product of two Pauli strings therefore sits in the character subspace of the product
label.  Since Kronecker products of Pauli strings span the two-replica matrix algebra — the Pauli
strings are a complex basis of each factor, and a standard basis matrix on a product index is a
Kronecker product of standard basis matrices — the character subspaces exhaust the whole space.

This is the completeness half of the character decomposition; independence is already proved.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped Kronecker BigOperators

noncomputable section

/-! ## The phase-free Pauli label product -/

/-- Product of two phase-free one-qubit Pauli labels. -/
def pauliLabelMul : Option (Fin 3) → Option (Fin 3) → Option (Fin 3)
  | none, q => q
  | some a, none => some a
  | some a, some b => if a = b then none else some (-(a + b))

/-- **The conjugation sign is multiplicative in the label.** -/
theorem boolPauliConjugationSign_pauliLabelMul (r p q : Option (Fin 3)) :
    boolPauliConjugationSign r (pauliLabelMul p q)
      = boolPauliConjugationSign r p * boolPauliConjugationSign r q := by
  rcases r with _ | x
  · simp [boolPauliConjugationSign]
  rcases p with _ | a
  · simp [pauliLabelMul, boolPauliConjugationSign]
  rcases q with _ | b
  · simp [pauliLabelMul, boolPauliConjugationSign]
  fin_cases x <;> fin_cases a <;> fin_cases b <;>
    simp +decide [boolPauliConjugationSign]

/-- Pointwise product of two phase-free global Pauli labels. -/
def finitePauliLabelMul {σ : Type*} (P Q : σ → Option (Fin 3)) : σ → Option (Fin 3) :=
  fun s => pauliLabelMul (P s) (Q s)

/-- **The global conjugation sign is multiplicative in the label.** -/
theorem finitePauliConjugationSign_finitePauliLabelMul {σ : Type*} [Fintype σ]
    (R P Q : σ → Option (Fin 3)) :
    finitePauliConjugationSign R (finitePauliLabelMul P Q)
      = finitePauliConjugationSign R P * finitePauliConjugationSign R Q := by
  rw [finitePauliConjugationSign, finitePauliConjugationSign, finitePauliConjugationSign,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun s _ => boolPauliConjugationSign_pauliLabelMul _ _ _

/-! ## Kronecker Pauli products are character vectors -/

/-- **A Kronecker product of Pauli strings has the character of the product label.** -/
theorem kroneckerPauli_mem_characterSubspace {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P₁ P₂ : σ → Option (Fin 3)) :
    (finitePauliMatrix P₁ ⊗ₖ finitePauliMatrix P₂)
      ∈ finiteTwoReplicaPauliCharacterSubspace (finitePauliLabelMul P₁ P₂) := by
  rw [mem_finiteTwoReplicaPauliCharacterSubspace_iff]
  intro Q
  show finiteTwoReplicaPairedPauli Q * (finitePauliMatrix P₁ ⊗ₖ finitePauliMatrix P₂) *
      finiteTwoReplicaPairedPauli Q = _
  rw [finiteTwoReplicaPairedPauli, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    finitePauliMatrix_conj, finitePauliMatrix_conj, Matrix.smul_kronecker,
    Matrix.kronecker_smul, smul_smul, finitePauliConjugationSign_finitePauliLabelMul]

/-! ## Kronecker products of Pauli strings span -/

theorem single_kronecker_single {m n : Type*} [DecidableEq m] [DecidableEq n]
    (i k : m) (j l : n) :
    (Matrix.single i k (1 : ℂ)) ⊗ₖ (Matrix.single j l (1 : ℂ))
      = Matrix.single (i, j) (k, l) (1 : ℂ) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.single, Matrix.of_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- **Kronecker products span the matrix algebra of a product index.** -/
theorem map₂_kroneckerBilinear_top_top {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] :
    Submodule.map₂ (Matrix.kroneckerBilinear (R := ℂ) (α := ℂ) (l := m) (m := m) (n := n) (p := n))
        ⊤ ⊤ = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← (Matrix.stdBasis ℂ (m × n) (m × n)).span_eq]
  refine Submodule.span_le.mpr ?_
  rintro X ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, rfl⟩
  rw [Matrix.stdBasis_eq_single, ← single_kronecker_single]
  exact Submodule.apply_mem_map₂ _ Submodule.mem_top Submodule.mem_top

/-- **Kronecker products of Pauli strings span the two-replica matrix algebra.** -/
theorem span_kroneckerPauli_eq_top (σ : Type*) [Fintype σ] [DecidableEq σ] :
    Submodule.span ℂ
        (Set.image2 (fun A B => A ⊗ₖ B)
          (Set.range (finitePauliMatrix (σ := σ)))
          (Set.range (finitePauliMatrix (σ := σ)))) = ⊤ := by
  have hmap := Submodule.map₂_span_span ℂ
    (Matrix.kroneckerBilinear (R := ℂ) (α := ℂ)
      (l := FiniteQubitConfiguration σ) (m := FiniteQubitConfiguration σ)
      (n := FiniteQubitConfiguration σ) (p := FiniteQubitConfiguration σ))
    (Set.range (finitePauliMatrix (σ := σ))) (Set.range (finitePauliMatrix (σ := σ)))
  rw [span_range_finitePauliMatrix, map₂_kroneckerBilinear_top_top] at hmap
  exact hmap.symm

/-- **The paired-Pauli character subspaces exhaust the two-replica space.** -/
theorem finiteTwoReplicaPauliCharacterSubspace_iSup_eq_top (σ : Type*) [Fintype σ]
    [DecidableEq σ] :
    (⨆ P : σ → Option (Fin 3), finiteTwoReplicaPauliCharacterSubspace P) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← span_kroneckerPauli_eq_top σ]
  refine Submodule.span_le.mpr ?_
  rintro X ⟨A, ⟨P₁, rfl⟩, B, ⟨P₂, rfl⟩, rfl⟩
  exact Submodule.mem_iSup_of_mem _ (kroneckerPauli_mem_characterSubspace P₁ P₂)

end

end GaloisForLFunctions.HTGeometry

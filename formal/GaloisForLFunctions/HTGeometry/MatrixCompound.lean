import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Compound matrices

The `k`-th compound of a square matrix is the matrix of the `k`-th exterior power of the
associated linear map, in the basis of exterior products of standard basis vectors.  Its entries
are the `k × k` minors of the original matrix.

Functoriality of the exterior power gives the Cauchy–Binet identity `C_k (A B) = C_k A · C_k B`
for free, and the minor formula gives compatibility with the conjugate transpose.  Together with
the diagonal computation `C_k (diagonal d) = diagonal (fun s => ∏ i ∈ s, d i)` these are the four
facts that turn a statement about the product of the largest `k` eigenvalues into a statement
about a single largest eigenvalue one exterior power up.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Module

/-! ## Enumerating a subset of fixed cardinality -/

section Enum

variable {ι : Type*} [LinearOrder ι]

/-- The increasing enumeration of a `k`-element subset. -/
noncomputable def subsetEnum {k : ℕ} (s : Set.powersetCard ι k) : Fin k → ι :=
  fun i => Set.powersetCard.ofFinEmbEquiv.symm s i

theorem subsetEnum_injective {k : ℕ} (s : Set.powersetCard ι k) :
    Function.Injective (subsetEnum s) :=
  fun _ _ h => (Set.powersetCard.ofFinEmbEquiv.symm s).injective h

theorem subsetEnum_mem {k : ℕ} (s : Set.powersetCard ι k) (i : Fin k) :
    subsetEnum s i ∈ (s : Finset ι) := by
  rw [subsetEnum, Set.powersetCard.ofFinEmbEquiv_symm_apply]
  exact Finset.orderEmbOfFin_mem s.val s.prop i

theorem prod_subsetEnum {M : Type*} [CommMonoid M] {k : ℕ} (s : Set.powersetCard ι k)
    (d : ι → M) : ∏ i, d (subsetEnum s i) = ∏ i ∈ (s : Finset ι), d i := by
  classical
  rw [← Finset.prod_coe_sort (s : Finset ι) d]
  exact Fintype.prod_equiv (Set.powersetCard.orderIsoOfFin s).toEquiv _ _ fun _ => rfl

theorem exists_mem_subsetEnum_notMem {k : ℕ} {s t : Set.powersetCard ι k} (hst : s ≠ t) :
    ∃ j : Fin k, subsetEnum s j ∉ (t : Finset ι) := by
  obtain ⟨a, has, hat⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne s t).1 hst
  obtain ⟨j, hj⟩ : a ∈ Set.range (Set.powersetCard.ofFinEmbEquiv.symm s) :=
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s a).2 has
  exact ⟨j, by
    rw [subsetEnum, hj]
    exact fun h => hat (Set.powersetCard.mem_coe_iff.1 h)⟩

end Enum

/-! ## The compound matrix -/

section Compound

variable {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  {R : Type*} [CommRing R]

/-- The `k`-th compound of a square matrix: the matrix of the `k`-th exterior power of the
associated linear map, in the exterior-power basis of the standard basis. -/
noncomputable def compound (k : ℕ) (A : Matrix ι ι R) :
    Matrix (Set.powersetCard ι k) (Set.powersetCard ι k) R :=
  LinearMap.toMatrix ((Pi.basisFun R ι).exteriorPower k) ((Pi.basisFun R ι).exteriorPower k)
    (exteriorPower.map k (Matrix.toLin (Pi.basisFun R ι) (Pi.basisFun R ι) A))

omit [LinearOrder ι] in
theorem basisFun_coord_toLin (A : Matrix ι ι R) (i j : ι) :
    (Pi.basisFun R ι).coord i
      (Matrix.toLin (Pi.basisFun R ι) (Pi.basisFun R ι) A ((Pi.basisFun R ι) j)) = A i j := by
  have h := LinearMap.toMatrix_apply (Pi.basisFun R ι) (Pi.basisFun R ι)
    (Matrix.toLin (Pi.basisFun R ι) (Pi.basisFun R ι) A) i j
  rw [LinearMap.toMatrix_toLin] at h
  exact h.symm

/-- **The entries of the compound are the minors.** -/
theorem compound_apply (k : ℕ) (A : Matrix ι ι R) (s t : Set.powersetCard ι k) :
    compound k A s t = (Matrix.of fun i j => A (subsetEnum s j) (subsetEnum t i)).det := by
  classical
  rw [compound, LinearMap.toMatrix_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.basis_repr_apply,
    show exteriorPower.ιMulti_family R k
      (⇑(Matrix.toLin (Pi.basisFun R ι) (Pi.basisFun R ι) A) ∘ ⇑(Pi.basisFun R ι)) t
      = exteriorPower.ιMulti R k
        (fun i => Matrix.toLin (Pi.basisFun R ι) (Pi.basisFun R ι) A
          ((Pi.basisFun R ι) (subsetEnum t i))) from rfl,
    exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1
  ext i j
  exact basisFun_coord_toLin A _ _

/-! ## Multiplicativity -/

/-- **Cauchy–Binet.**  The compound of a product is the product of the compounds. -/
theorem compound_mul (k : ℕ) (A B : Matrix ι ι R) :
    compound k (A * B) = compound k A * compound k B := by
  rw [compound, compound, compound, Matrix.toLin_mul (Pi.basisFun R ι) (Pi.basisFun R ι)
      (Pi.basisFun R ι), exteriorPower.map_comp, LinearMap.toMatrix_comp _
      ((Pi.basisFun R ι).exteriorPower k)]

@[simp] theorem compound_one (k : ℕ) : compound k (1 : Matrix ι ι R) = 1 := by
  rw [compound, Matrix.toLin_one, exteriorPower.map_id, LinearMap.toMatrix_id]

/-! ## Diagonal matrices -/

/-- **The compound of a diagonal matrix is diagonal**, with the subset products as entries. -/
theorem compound_diagonal (k : ℕ) (d : ι → R) :
    compound k (Matrix.diagonal d)
      = Matrix.diagonal (fun s : Set.powersetCard ι k => ∏ i ∈ (s : Finset ι), d i) := by
  classical
  ext s t
  rw [compound_apply, Matrix.diagonal_apply]
  by_cases hst : s = t
  · subst hst
    rw [if_pos rfl,
      show (Matrix.of fun i j => Matrix.diagonal d (subsetEnum s j) (subsetEnum s i))
        = Matrix.diagonal (fun i => d (subsetEnum s i)) from by
          ext i j
          by_cases hij : i = j
          · subst hij
            simp
          · rw [Matrix.of_apply,
              Matrix.diagonal_apply_ne _ fun h => hij (subsetEnum_injective s h).symm,
              Matrix.diagonal_apply_ne _ hij],
      Matrix.det_diagonal, prod_subsetEnum]
  · rw [if_neg hst]
    obtain ⟨j, hj⟩ := exists_mem_subsetEnum_notMem hst
    refine Matrix.det_eq_zero_of_column_eq_zero j fun i => ?_
    rw [Matrix.of_apply, Matrix.diagonal_apply_ne']
    intro hcon
    exact hj (hcon ▸ subsetEnum_mem t i)

/-! ## Units -/

/-- **The compound of an invertible matrix is invertible.** -/
theorem compound_mul_compound_inv {k : ℕ} {A B : Matrix ι ι R} (hAB : A * B = 1) :
    compound k A * compound k B = 1 := by
  rw [← compound_mul, hAB, compound_one]

theorem compound_mulVec_surjective {k : ℕ} {A B : Matrix ι ι R} (hAB : A * B = 1)
    (x : Set.powersetCard ι k → R) :
    ∃ y : Set.powersetCard ι k → R, compound k A *ᵥ y = x :=
  ⟨compound k B *ᵥ x, by
    rw [Matrix.mulVec_mulVec, compound_mul_compound_inv hAB, Matrix.one_mulVec]⟩

/-! ## The conjugate transpose -/

variable [StarRing R]

/-- **The compound commutes with the conjugate transpose.** -/
theorem compound_conjTranspose (k : ℕ) (A : Matrix ι ι R) :
    compound k Aᴴ = (compound k A)ᴴ := by
  ext s t
  rw [Matrix.conjTranspose_apply, compound_apply, compound_apply,
    show (Matrix.of fun i j => Aᴴ (subsetEnum s j) (subsetEnum t i))
      = (Matrix.of fun i j => A (subsetEnum t j) (subsetEnum s i))ᴴ from by
        ext i j
        simp [Matrix.conjTranspose_apply],
    Matrix.det_conjTranspose]

theorem compound_isHermitian {k : ℕ} {A : Matrix ι ι R} (hA : A.IsHermitian) :
    (compound k A).IsHermitian := by
  rw [Matrix.IsHermitian, ← compound_conjTranspose, hA]

theorem compound_unitary {k : ℕ} {A : Matrix ι ι R} (hA : A ∈ Matrix.unitaryGroup ι R) :
    compound k A ∈ Matrix.unitaryGroup (Set.powersetCard ι k) R := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA ⊢
  rw [Matrix.star_eq_conjTranspose] at hA ⊢
  rw [← compound_conjTranspose, ← compound_mul, hA, compound_one]

end Compound

end GaloisForLFunctions.HTGeometry

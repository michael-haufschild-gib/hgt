import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation

/-!
# Scalar-extension Hasse splitting for cyclic Galois algebras

Package a nonzero cyclic Galois algebra together with its defining-field degree.  Scalar extension
to that cyclic field is algebra-equivalent to the full companion matrix algebra.  Consequently
equality and vanishing are detected entrywise, one matrix entry detects every nonzero tensor, and
every matrix has a unique scalar-extended cyclic-algebra ancestor.

This is direct central-simple scalar-extension infrastructure: it uses simplicity preservation to
obtain injectivity and finite-dimensionality to obtain the full splitting isomorphism.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

noncomputable section

/-- Intrinsic data of one nonzero cyclic Galois algebra and its defining-field degree. -/
structure CyclicGaloisScalarExtensionDatum
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] where
  predDegree : ℕ
  degree_eq : Module.finrank K L = predDegree + 1
  parameter : K
  parameter_ne_zero : parameter ≠ 0

namespace CyclicGaloisScalarExtensionDatum

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- Defining-field scalar extension is the full companion matrix algebra. -/
noncomputable def matrixAlgEquiv (D : CyclicGaloisScalarExtensionDatum K L) :
    L ⊗[K] (cyclicGaloisAlgebra K L D.parameter) ≃ₐ[L]
      Matrix (Fin (D.predDegree + 1)) (Fin (D.predDegree + 1)) L :=
  cyclicGaloisAlgebraScalarExtensionMatrixAlgEquiv K L D.predDegree D.degree_eq
    D.parameter D.parameter_ne_zero

/-- Matrix-entry Hasse congruence after scalar extension to the cyclic defining field. -/
theorem congr_scalarExtensionEntry_hasse_iff
    (D : CyclicGaloisScalarExtensionDatum K L)
    (x y : L ⊗[K] (cyclicGaloisAlgebra K L D.parameter)) :
    x = y ↔ ∀ i j, D.matrixAlgEquiv x i j = D.matrixAlgEquiv y i j := by
  constructor
  · rintro rfl
    exact fun _ _ ↦ rfl
  · intro h
    apply D.matrixAlgEquiv.injective
    ext i j
    exact h i j

/-- A scalar-extended cyclic element vanishes exactly when every matrix entry vanishes. -/
theorem eq_zero_scalarExtensionEntry_hasse_iff
    (D : CyclicGaloisScalarExtensionDatum K L)
    (x : L ⊗[K] (cyclicGaloisAlgebra K L D.parameter)) :
    x = 0 ↔ ∀ i j, D.matrixAlgEquiv x i j = 0 := by
  rw [D.congr_scalarExtensionEntry_hasse_iff]
  simp

/-- Every nonzero scalar-extended cyclic element is detected by one matrix entry. -/
theorem exists_scalarExtensionEntry_ne_zero_of_ne_zero
    (D : CyclicGaloisScalarExtensionDatum K L)
    (x : L ⊗[K] (cyclicGaloisAlgebra K L D.parameter)) (hx : x ≠ 0) :
    ∃ i j, D.matrixAlgEquiv x i j ≠ 0 := by
  by_contra h
  push Not at h
  exact hx ((D.eq_zero_scalarExtensionEntry_hasse_iff x).2 h)

/-- Every matrix has one unique global scalar-extended cyclic-algebra ancestor. -/
theorem matrix_existsUnique_scalarExtension_preimage
    (D : CyclicGaloisScalarExtensionDatum K L)
    (M : Matrix (Fin (D.predDegree + 1)) (Fin (D.predDegree + 1)) L) :
    ∃! x : L ⊗[K] (cyclicGaloisAlgebra K L D.parameter),
      D.matrixAlgEquiv x = M := by
  exact ⟨D.matrixAlgEquiv.symm M, D.matrixAlgEquiv.apply_symm_apply M,
    fun x hx ↦ D.matrixAlgEquiv.injective
      (hx.trans (D.matrixAlgEquiv.apply_symm_apply M).symm)⟩

end CyclicGaloisScalarExtensionDatum

end

end GaloisForLFunctions.HTGeometry.ABHN

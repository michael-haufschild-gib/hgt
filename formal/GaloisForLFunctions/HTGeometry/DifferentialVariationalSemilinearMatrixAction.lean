import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveBuildingCarrier
import GaloisForLFunctions.HTGeometry.DifferentialOperatorSemilinearMatrix

/-!
# Semilinear operator matrices on the differential variational carrier

This leaf embeds the differential-operator ring into its completed pseudodifferential skew field,
transports invertible operator matrices through that embedding, and combines the result with the
corpus theorem that every finite free semilinear automorphism has a two-sided invertible operator
matrix.  It supplies the exact matrix input consumed by the projective semilinear lattice action.
-/

open scoped Differential
open nonZeroDivisors OreLocalization

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

/-- Canonical ring embedding from differential operators into the completed pseudodifferential
skew field. -/
def diffOpToCompletedPseudoRingHom : DiffOp K →+* CompletedPseudoDiffOp K :=
  UniformSpace.Completion.coeRingHom.comp
    ((WithVal.equiv (pseudoDiffOpValuation (K := K))).symm.toRingHom.comp
      numeratorRingHom)

@[simp]
theorem diffOpToCompletedPseudoRingHom_apply (p : DiffOp K) :
    diffOpToCompletedPseudoRingHom p =
      ((WithVal.toVal (pseudoDiffOpValuation (K := K))
        (numeratorRingHom p : PseudoDiffOp K) :
          WithVal (pseudoDiffOpValuation (K := K))) : CompletedPseudoDiffOp K) := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An invertible differential-operator matrix remains invertible after completed-skew embedding. -/
def completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit
    (A : (Matrix ι ι (DiffOp K))ˣ) :
    (Matrix ι ι (CompletedPseudoDiffOp K))ˣ :=
  Units.map (diffOpToCompletedPseudoRingHom (K := K)).mapMatrix.toMonoidHom A

@[simp]
theorem completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit_val
    (A : (Matrix ι ι (DiffOp K))ˣ) :
    (completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit A :
        Matrix ι ι (CompletedPseudoDiffOp K)) =
      (A : Matrix ι ι (DiffOp K)).map diffOpToCompletedPseudoRingHom := rfl

/-- Package the coefficient-twisted inverse equations as an operator-matrix unit. -/
def operatorMatrixUnitOfSemilinearInverse
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (A A' : Matrix ι ι (DiffOp K))
    (hAA' : A * A'.map (mapRingEquiv σ hσ : DiffOp K →+* DiffOp K) = 1)
    (hA'A : A'.map (mapRingEquiv σ hσ : DiffOp K →+* DiffOp K) * A = 1) :
    (Matrix ι ι (DiffOp K))ˣ where
  val := A
  inv := A'.map (mapRingEquiv σ hσ : DiffOp K →+* DiffOp K)
  val_inv := hAA'
  inv_val := hA'A

section SemilinearMatrix

variable {M : Type*} [AddCommGroup M] [Module (DiffOp K) M] {r : ℕ}

/-- Every semilinear automorphism of a finite free differential-operator module has a genuine
invertible matrix on the completed projective building carrier. -/
theorem exists_completedPseudoDiffOpMatrixUnit_of_semilinear_equiv
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (b : Module.Basis (Fin r) (DiffOp K) M)
    (T T' : M → M)
    (hTadd : ∀ x y, T (x + y) = T x + T y)
    (hTsmul : ∀ (a : DiffOp K) (x : M),
      T (a • x) = mapRingEquiv σ hσ a • T x)
    (hT'add : ∀ x y, T' (x + y) = T' x + T' y)
    (hT'smul : ∀ (a : DiffOp K) (x : M),
      T' (a • x) = (mapRingEquiv σ hσ).symm a • T' x)
    (hTT' : ∀ x, T (T' x) = x) (hT'T : ∀ x, T' (T x) = x) :
    ∃ A A' : Matrix (Fin r) (Fin r) (DiffOp K),
      ∃ Ahat : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ,
        (∀ i, T (b i) = ∑ j, A i j • b j) ∧
        (∀ i, T' (b i) = ∑ j, A' i j • b j) ∧
        (Ahat : Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K)) =
          A.map diffOpToCompletedPseudoRingHom := by
  obtain ⟨A, A', hA, hA', hAA', hA'A⟩ :=
    isUnit_matrix_of_semilinear_equiv (mapRingEquiv σ hσ) b T T'
      hTadd hTsmul hT'add hT'smul hTT' hT'T
  let Aunit : (Matrix (Fin r) (Fin r) (DiffOp K))ˣ :=
    operatorMatrixUnitOfSemilinearInverse σ hσ A A' hAA' hA'A
  let Ahat := completedPseudoDiffOpMatrixUnitOfOperatorMatrixUnit Aunit
  refine ⟨A, A', Ahat, hA, hA', ?_⟩
  rfl

end SemilinearMatrix

end
end GaloisForLFunctions.HTGeometry.DiffOp

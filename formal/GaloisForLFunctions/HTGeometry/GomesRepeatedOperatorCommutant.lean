import GaloisForLFunctions.HTGeometry.GomesScalarMatrixCentralizer

/-!
# Full symmetries of repeated operators

Repeating an operator on a finite product replaces its full centralizer by matrices
over that centralizer. Off-diagonal entries allow actual mixing of the copies.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

variable (R : Type*) [CommSemiring R]
variable (ι : Type*) [Fintype ι] [DecidableEq ι]
variable {V : Type*} [AddCommMonoid V] [Module R V]

/-- The same endomorphism acting on each component of a finite product. -/
def gomesRepeatedEndomorphism (T : Module.End R V) : Module.End R (ι → V) where
  toFun f i := T (f i)
  map_add' f g := by ext i; exact map_add T (f i) (g i)
  map_smul' r f := by ext i; exact map_smul T r (f i)

omit [Fintype ι] in
/-- A repeated endomorphism acts on each single-component input without mixing it. -/
theorem gomesRepeatedEndomorphism_single (T : Module.End R V) (j : ι) (v : V) :
    gomesRepeatedEndomorphism R ι T (Pi.single j v) = Pi.single j (T v) := by
  ext i
  by_cases h : j = i
  · subst i
    simp [gomesRepeatedEndomorphism]
  · simp [gomesRepeatedEndomorphism, Ne.symm h]

/-- Block coordinates turn repetition into a scalar matrix with operator coefficients. -/
theorem gomesRepeatedEndomorphism_matrix (T : Module.End R V) :
    endVecAlgEquivMatrixEnd ι R R V (gomesRepeatedEndomorphism R ι T) =
      Matrix.scalar ι T := by
  ext i j v
  change T ((Pi.single j v : ι → V) i) = ((Matrix.scalar ι T) i j) v
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

/-- Every symmetry of a repeated operator is an arbitrary matrix of single-copy symmetries. -/
def gomesRepeatedEndomorphismCommutantEquiv (T : Module.End R V) :
    (Subalgebra.centralizer R {gomesRepeatedEndomorphism R ι T}) ≃ₐ[R]
      Matrix ι ι (Subalgebra.centralizer R {T}) :=
  (gomesCentralizerTransportEquiv R (endVecAlgEquivMatrixEnd ι R R V)
    (gomesRepeatedEndomorphism R ι T)).trans
      ((Subalgebra.equivOfEq _ _ (congrArg
        (fun U : Matrix ι ι (Module.End R V) => Subalgebra.centralizer R {U})
          (gomesRepeatedEndomorphism_matrix R ι T))).trans
            (gomesScalarMatrixCentralizerEquiv R ι T))

end GaloisForLFunctions.HTGeometry

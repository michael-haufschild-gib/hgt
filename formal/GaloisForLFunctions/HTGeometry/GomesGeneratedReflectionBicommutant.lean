import GaloisForLFunctions.HTGeometry.GomesDerivativeReflectionGeneratedAlgebra
import GaloisForLFunctions.HTGeometry.GomesReflectionJointMatrixCommutant

/-!
# A proper generated algebra with scalar commutant and full bicommutant

The exact constant-line algebra is strictly smaller than the ambient formal
matrix algebra, yet taking commutants twice recovers the entire ambient algebra.
This is a concrete sharp reconstruction failure with the missing invariant known.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
variable (K : Type*) [Field K] [CharZero K]

/-- The commutant of the entire generated algebra consists exactly of scalar formal matrices. -/
theorem gomesDerivativeReflectionGeneratedAlgebra_centralizer_mem_iff
    (c : K) (M : Matrix (Fin 2) (Fin 2) (PowerSeries K)) :
    M ∈ Subalgebra.centralizer (PowerSeries K)
      (gomesDerivativeReflectionGeneratedAlgebra K c : Set (Matrix (Fin 2) (Fin 2) (PowerSeries K))) ↔
        ∃ F : PowerSeries K, M = Matrix.scalar (Fin 2) F := by
  constructor
  · intro h
    rw [Subalgebra.mem_centralizer_iff] at h
    apply (gomesDerivativeReflectionMatrix_joint_commutant K c M).mp
    exact ⟨(h _ (gomesDerivativeReflectionGeneratedAlgebra_derivative_mem K c)).symm,
      (h _ (gomesDerivativeReflectionGeneratedAlgebra_reflection_mem K c)).symm⟩
  · rintro ⟨F, rfl⟩
    rw [Subalgebra.mem_centralizer_iff]
    intro N hN
    exact (Matrix.scalar_commute F (Commute.all F) N).eq.symm

/-- The bicommutant of the proper constant-line algebra is the full formal matrix algebra. -/
theorem gomesDerivativeReflectionGeneratedAlgebra_doubleCentralizer (c : K) :
    Subalgebra.centralizer (PowerSeries K)
      (Subalgebra.centralizer (PowerSeries K)
        (gomesDerivativeReflectionGeneratedAlgebra K c : Set (Matrix (Fin 2) (Fin 2) (PowerSeries K))) :
          Set (Matrix (Fin 2) (Fin 2) (PowerSeries K))) = ⊤ := by
  apply eq_top_iff.mpr
  intro M hM
  rw [Subalgebra.mem_centralizer_iff]
  intro N hN
  obtain ⟨F, rfl⟩ := (gomesDerivativeReflectionGeneratedAlgebra_centralizer_mem_iff K c N).mp hN
  exact (Matrix.scalar_commute F (Commute.all F) M).eq

/-- Double commutation fails to recover this exact generated algebra at every center. -/
theorem gomesDerivativeReflectionGeneratedAlgebra_ne_doubleCentralizer (c : K) :
    gomesDerivativeReflectionGeneratedAlgebra K c ≠
      Subalgebra.centralizer (PowerSeries K)
        (Subalgebra.centralizer (PowerSeries K)
          (gomesDerivativeReflectionGeneratedAlgebra K c : Set (Matrix (Fin 2) (Fin 2) (PowerSeries K))) :
            Set (Matrix (Fin 2) (Fin 2) (PowerSeries K))) := by
  rw [gomesDerivativeReflectionGeneratedAlgebra_doubleCentralizer]
  exact gomesDerivativeReflectionGeneratedAlgebra_ne_top K c

end GaloisForLFunctions.HTGeometry

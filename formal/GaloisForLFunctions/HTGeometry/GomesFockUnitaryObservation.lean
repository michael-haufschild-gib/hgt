import GaloisForLFunctions.HTGeometry.GomesDysonUnitaryCovariance

/-!
Exact internal-gauge reconstruction from actual free-Fock observations. Applying
Gomes, arXiv:2404.10461 and arXiv:2607.24901v1, the identity generator fixes the
internal metric, Dyson tensors transport every even moment, and all vector-state
observations reconstruct exactly unitary frame changes. All matrices remain
arbitrary data: unitarity is characterized by closed equivalences.
-/
open scoped Matrix BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Conjugate the input matrix data before applying the existing Fock completion. -/
def gomesFockConjugatedData {d k : ℕ} (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  fun i => gomesFockConjugate U (B i)

/-- The identity-completed generator family is covariant exactly for unitary internal frames. -/
theorem gomesFock_completion_covariance_iff {d k : ℕ} (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (∀ B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ, ∀ i,
      gomesCompletedFockGenerators (gomesFockConjugatedData U B) i =
        gomesFockConjugate U (gomesCompletedFockGenerators B i)) ↔ Uᴴ*U = 1 := by
  constructor
  · intro h
    have h0 := h 0 none
    have hh : U*Uᴴ = 1 := by
      simpa [gomesCompletedFockGenerators,gomesFockConjugate] using h0.symm
    exact mul_eq_one_comm.mp hh
  · intro hu B i
    have huh : U*Uᴴ = 1 := mul_eq_one_comm.mp hu
    cases i with
    | none => simp [gomesCompletedFockGenerators,gomesFockConjugate,huh]
    | some i =>
      simp only [gomesCompletedFockGenerators,gomesFockConjugatedData,gomesFockConjugate_adjoint]
      simp [gomesFockConjugate,Matrix.mul_add,Matrix.add_mul]

/-- The actual completed-Fock moment matrix is the even Dyson coefficient and vanishes at odd levels. -/
theorem gomesCompletedFock_moment_matrix_formula {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (n : ℕ) :
    freeFockMatrixMomentCoefficient (gomesCompletedFockGenerators B) n =
      if 2 ∣ n then matrixDysonFormalCoeff (gomesCompletedFockGenerators B) (n/2) else 0 := by
  funext i j
  simp only [freeFockMatrixMomentCoefficient,
    freeFockPower_vacuumCoefficient _ (gomesCompletedFockGenerators_hermitian B)]
  by_cases hn : 2 ∣ n <;> simp [hn]

/-- The full actual Fock matrix-moment menu is covariant exactly for unitary internal frames. -/
theorem gomesFock_matrix_conjugacy_iff {d k : ℕ} (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (∀ B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ, ∀ n,
      freeFockMatrixMomentCoefficient (gomesCompletedFockGenerators (gomesFockConjugatedData U B)) n =
        gomesFockConjugate U (freeFockMatrixMomentCoefficient (gomesCompletedFockGenerators B) n)) ↔
      Uᴴ*U = 1 := by
  constructor
  · intro h
    have h0 := h 0 0
    have hh : U*Uᴴ = 1 := by
      simpa [gomesCompletedFock_moment_matrix_formula,matrixDysonFormalCoeff,gomesFockConjugate] using h0.symm
    exact mul_eq_one_comm.mp hh
  · intro hu B n
    rw [gomesCompletedFock_moment_matrix_formula,gomesCompletedFock_moment_matrix_formula]
    have hB : gomesCompletedFockGenerators (gomesFockConjugatedData U B) =
        fun i => gomesFockConjugate U (gomesCompletedFockGenerators B i) :=
      funext (fun i => (gomesFock_completion_covariance_iff U).mpr hu B i)
    rw [hB]
    by_cases hn : 2 ∣ n
    · simp only [hn,if_pos]
      exact (gomesDyson_unitary_conjugacy_iff U).mpr hu _ _
    · simp [hn,gomesFockConjugate]

/-- Arbitrary internal changes transport quadratic observations by adjoint congruence. -/
theorem gomesFock_quadratic_transport {d : ℕ}
    (U M : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    star (U*ᵥx) ⬝ᵥ (M*ᵥ(U*ᵥx)) = star x ⬝ᵥ ((Uᴴ*M*U)*ᵥx) := by
  rw [Matrix.star_mulVec,← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]

/-- Transporting both a matrix observation and its state inserts the exact squared Gram defect. -/
theorem gomesFock_quadratic_conjugate_defect {d : ℕ}
    (U M : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    star (U*ᵥx) ⬝ᵥ (gomesFockConjugate U M*ᵥ(U*ᵥx)) =
      star x ⬝ᵥ (((Uᴴ*U)*M*(Uᴴ*U))*ᵥx) := by
  rw [gomesFock_quadratic_transport]
  simp only [gomesFockConjugate,Matrix.mul_assoc]

/-- Initial Fock mass is exactly the internal Hermitian square norm. -/
theorem gomesFockVector_mass_quadratic {d k : ℕ}
    (A : Option (Fin k) → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    (freeFockVectorMoment A x 0 : ℂ) = star x ⬝ᵥ x := by
  simp [freeFockVectorMoment_zero,dotProduct,Complex.normSq_eq_conj_mul_self ]

/-- Even the initial vector-state mass menu reconstructs exactly unitary internal changes. -/
theorem gomesFockVector_mass_isometry_iff {d k : ℕ}
    (A : Option (Fin k) → Matrix (Fin d) (Fin d) ℂ) (U : Matrix (Fin d) (Fin d) ℂ) :
    (∀ x, freeFockVectorMoment A (U*ᵥx) 0 = freeFockVectorMoment A x 0) ↔ Uᴴ*U = 1 := by
  constructor
  · intro h
    apply matrix_eq_of_quadraticForm_eq
    intro x
    have hh := congrArg (fun r : ℝ => (r : ℂ)) (h x)
    rw [gomesFockVector_mass_quadratic,gomesFockVector_mass_quadratic] at hh
    have ht := gomesFock_quadratic_transport U 1 x
    simp at ht
    simpa using ht.symm.trans hh
  · intro hu x
    apply Complex.ofReal_injective
    rw [gomesFockVector_mass_quadratic,gomesFockVector_mass_quadratic]
    have ht := gomesFock_quadratic_transport U 1 x
    simpa [hu] using ht

/-- Every actual vector-state Fock moment is gauge-invariant exactly for unitary internal frame changes. -/
theorem gomesFock_vector_gauge_iff {d k : ℕ} (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (∀ B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ, ∀ x, ∀ n,
      freeFockVectorMoment (gomesCompletedFockGenerators (gomesFockConjugatedData U B)) (U*ᵥx) n =
        freeFockVectorMoment (gomesCompletedFockGenerators B) x n) ↔ Uᴴ*U = 1 := by
  constructor
  · intro h
    apply (gomesFockVector_mass_isometry_iff (gomesCompletedFockGenerators (0 : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) U).mp
    intro x
    simpa only [freeFockVectorMoment_zero] using h 0 x 0
  · intro hu B x n
    apply Complex.ofReal_injective
    calc
      (freeFockVectorMoment (gomesCompletedFockGenerators (gomesFockConjugatedData U B)) (U*ᵥx) n : ℂ) =
          star (U*ᵥx) ⬝ᵥ (freeFockMatrixMomentCoefficient
            (gomesCompletedFockGenerators (gomesFockConjugatedData U B)) n*ᵥ(U*ᵥx)) :=
        (star_dotProduct_freeFockMatrixMomentCoefficient_mulVec _
          (gomesCompletedFockGenerators_hermitian _) _ _).symm
      _ = star x ⬝ᵥ (((Uᴴ*U)*freeFockMatrixMomentCoefficient (gomesCompletedFockGenerators B) n*(Uᴴ*U))*ᵥx) := by
        rw [(gomesFock_matrix_conjugacy_iff U).mpr hu B n]
        exact gomesFock_quadratic_conjugate_defect U _ x
      _ = (freeFockVectorMoment (gomesCompletedFockGenerators B) x n : ℂ) := by
        rw [hu,one_mul,mul_one]
        exact star_dotProduct_freeFockMatrixMomentCoefficient_mulVec _
          (gomesCompletedFockGenerators_hermitian B) x n

end GaloisForLFunctions.HTGeometry

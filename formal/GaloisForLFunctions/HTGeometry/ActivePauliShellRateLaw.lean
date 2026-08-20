import GaloisForLFunctions.HTGeometry.PauliHilbertSchmidtNorm
import GaloisForLFunctions.HTGeometry.PauliTwoLocalEmbedding
import GaloisForLFunctions.HTGeometry.ShellCoefficientMeasure
import GaloisForLFunctions.HTGeometry.PauliEnsembleCliffordCovariance

/-!
# Exact physical rate on the active Pauli shell

A unit sphere in a redundant coefficient presentation need not fix Hamiltonian rate: inactive
coordinates can carry coefficient norm while producing no Hamiltonian.  This module proves that
defect for the full Pauli presentation, then repairs it by restricting the coefficient sphere to
the nonidentity Pauli words of weight at most `q`.  Pauli orthogonality makes the corrected rate
exact at every shell point.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Indicator of the physically active nonidentity Pauli words of weight at most `q`. -/
def activePauliMask (n q : ℕ) (P : Fin n → Option (Fin 3)) : ℝ :=
  if pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n then 1 else 0

/-- A unit coordinate vector in the full Pauli coefficient space. -/
def fullPauliBasisCoefficient {n : ℕ} (P : Fin n → Option (Fin 3)) :
    (Fin n → Option (Fin 3)) → ℝ :=
  fun Q => if Q = P then 1 else 0

theorem sum_sq_fullPauliBasisCoefficient {n : ℕ} (P : Fin n → Option (Fin 3)) :
    (∑ Q, (fullPauliBasisCoefficient P Q) ^ 2) = 1 := by
  classical
  simp [fullPauliBasisCoefficient]

/-- The full coefficient shell contains a unit direction producing the zero Hamiltonian. -/
theorem pauliEnsemble_activeMask_identity_basis_eq_zero (n q : ℕ) :
    pauliEnsemble (activePauliMask n q)
      (fullPauliBasisCoefficient (pauliIdentityLabel n)) = 0 := by
  classical
  simp [pauliEnsemble, activePauliMask, fullPauliBasisCoefficient]

/-- Every active unit coordinate instead produces its Pauli Hamiltonian. -/
theorem pauliEnsemble_activeMask_active_basis {n q : ℕ} (P : PauliTracelessLabel n q) :
    pauliEnsemble (activePauliMask n q) (fullPauliBasisCoefficient P.1) =
      finitePauliMatrix P.1 := by
  classical
  simp [pauliEnsemble, activePauliMask, fullPauliBasisCoefficient, P.2]

theorem frobSq_finitePauliMatrix_exact {n : ℕ} (P : Fin n → Option (Fin 3)) :
    frobSq (finitePauliMatrix P) = 2 ^ n := by
  classical
  have h := frobSq_pauliCombination (σ := Fin n)
    (fun Q => if Q = P then (1 : ℂ) else 0)
  have hsum : (∑ Q : Fin n → Option (Fin 3),
      ‖if Q = P then (1 : ℂ) else 0‖ ^ 2) = 1 := by
    rw [Finset.sum_eq_single P]
    · simp
    · intro Q _ hQP
      simp [hQP]
    · intro hP
      exact absurd (Finset.mem_univ P) hP
  rw [hsum, mul_one] at h
  simpa [Fintype.card_fin] using h

/-- **No-go for the old full shell.** Equal unit coefficient norms can produce zero or full Pauli
rate because inactive coefficient directions lie in the ensemble map's kernel. -/
theorem fullPauliShell_has_variable_hamiltonian_rate {n q : ℕ}
    (P : PauliTracelessLabel n q) :
    frobSq (pauliEnsemble (activePauliMask n q)
        (fullPauliBasisCoefficient (pauliIdentityLabel n))) = 0 ∧
      frobSq (pauliEnsemble (activePauliMask n q) (fullPauliBasisCoefficient P.1)) = 2 ^ n := by
  rw [pauliEnsemble_activeMask_identity_basis_eq_zero,
    pauliEnsemble_activeMask_active_basis]
  exact ⟨by simp [frobSq], frobSq_finitePauliMatrix_exact P.1⟩

/-- Hamiltonian assembled only from the physically active nonidentity Pauli words of weight at
most `q`. -/
def activePauliHamiltonian {n q : ℕ} (J : PauliTracelessLabel n q → ℂ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  ∑ P : PauliTracelessLabel n q, J P • finitePauliMatrix P.1

/-- Exact Parseval law on the active `q`-local Pauli dictionary. -/
theorem frobSq_activePauliHamiltonian {n q : ℕ} (J : PauliTracelessLabel n q → ℂ) :
    frobSq (activePauliHamiltonian J) =
      2 ^ n * ∑ P : PauliTracelessLabel n q, ‖J P‖ ^ 2 := by
  classical
  have hcast : ((frobSq (activePauliHamiltonian J) : ℝ) : ℂ) =
      ((2 ^ n * ∑ P : PauliTracelessLabel n q, ‖J P‖ ^ 2 : ℝ) : ℂ) := by
    rw [activePauliHamiltonian, ofReal_frobSq_eq_trace, star_sum, Finset.sum_mul,
      Matrix.trace_sum]
    have hterm : ∀ P : PauliTracelessLabel n q,
        Matrix.trace (star (J P • finitePauliMatrix P.1) *
            ∑ Q : PauliTracelessLabel n q, J Q • finitePauliMatrix Q.1) =
          ((‖J P‖ ^ 2 : ℝ) : ℂ) * (2 : ℂ) ^ n := by
      intro P
      rw [Finset.mul_sum, Matrix.trace_sum]
      rw [Finset.sum_eq_single P]
      · rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
          Matrix.trace_smul, trace_star_finitePauliMatrix_mul P.1 P.1, if_pos rfl]
        simp only [smul_eq_mul, RCLike.star_def, Fintype.card_fin]
        rw [Complex.sq_norm, ← Complex.mul_conj]
        ring
      · intro Q _ hQP
        rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
          Matrix.trace_smul, trace_star_finitePauliMatrix_mul P.1 Q.1,
          if_neg (fun h => hQP (Subtype.ext h.symm))]
        simp
      · intro hcon
        exact absurd (Finset.mem_univ P) hcon
    rw [Finset.sum_congr rfl fun P (_ : P ∈ Finset.univ) => hterm P,
      ← Finset.sum_mul]
    push_cast
    ring
  exact_mod_cast hcast

/-- A unit active coefficient vector has exactly the prescribed Hamiltonian rate. -/
theorem frobSq_activePauliHamiltonian_of_unit {n q : ℕ}
    (J : PauliTracelessLabel n q → ℂ)
    (hJ : ∑ P : PauliTracelessLabel n q, ‖J P‖ ^ 2 = 1) :
    frobSq (activePauliHamiltonian J) = 2 ^ n := by
  rw [frobSq_activePauliHamiltonian, hJ, mul_one]

/-- The corrected fixed-shell Hamiltonian, indexed only by physically active Pauli words. -/
def activePauliShellHamiltonian {n q : ℕ}
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (PauliTracelessLabel n q)) 1) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  activePauliHamiltonian (fun P => (shellCoefficientMap (PauliTracelessLabel n q) θ P : ℂ))

/-- **Exact fixed-rate law for every point of the corrected active shell.** -/
theorem frobSq_activePauliShellHamiltonian {n q : ℕ}
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (PauliTracelessLabel n q)) 1) :
    frobSq (activePauliShellHamiltonian θ) = 2 ^ n := by
  apply frobSq_activePauliHamiltonian_of_unit
  have hnorm : ‖(θ : EuclideanSpace ℝ (PauliTracelessLabel n q))‖ = 1 := by
    simpa [dist_eq_norm] using θ.property
  have hsq := congrArg (fun x : ℝ => x ^ 2) hnorm
  rw [EuclideanSpace.norm_sq_eq] at hsq
  simpa [activePauliShellHamiltonian, shellCoefficientMap, Real.norm_eq_abs, sq_abs] using hsq

end GaloisForLFunctions.HTGeometry

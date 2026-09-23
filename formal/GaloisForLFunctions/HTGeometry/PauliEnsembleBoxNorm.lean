import GaloisForLFunctions.HTGeometry.PauliZGappedHamiltonian
import GaloisForLFunctions.HTGeometry.SelfAdjointPropagator

/-!
# The fixed-locality Pauli ensemble and its coefficient box

The ensemble Hamiltonian is the normalised sum of the nonidentity Pauli strings of weight at most
the locality budget, weighted by a coefficient vector.  At the diagonal centre — coefficient one on
every `Z` string and zero elsewhere — it is the gapped diagonal Hamiltonian.

Every Pauli string is a Hermitian involution, hence a unitary operator of norm one, so a coefficient
perturbation of size `w` moves the Hamiltonian by at most `m^{-1/2} m w` in operator norm.  At
half-width `ε²/(16m)` this is `ε²/16` times the normalisation.
-/

open scoped BigOperators
open HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n q : ℕ}

/-- The Hamiltonian of the fixed-locality Pauli ensemble at a coefficient vector. -/
def pauliEnsembleMatrix (n q : ℕ) (J : (Fin n → Option (Fin 3)) → ℝ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  ((pauliNormalization n q : ℝ) : ℂ) •
    ∑ P ∈ nonidentityPauliWords n q, ((J P : ℝ) : ℂ) • finitePauliMatrix P

/-- The ensemble Hamiltonian as an operator on the register. -/
def pauliEnsembleOp (n q : ℕ) (J : (Fin n → Option (Fin 3)) → ℝ) :
    EuclideanSpace ℂ (Fin n → Bool) →L[ℂ] EuclideanSpace ℂ (Fin n → Bool) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (pauliEnsembleMatrix n q J)

/-- The diagonal centre: coefficient one on every `Z` string, zero elsewhere. -/
def pauliEnsembleCenter (n : ℕ) : (Fin n → Option (Fin 3)) → ℝ :=
  fun P => if ∀ s, P s = none ∨ P s = some 2 then 1 else 0

/-- **The all-`Z` strings of bounded weight are exactly the centre's supports.** -/
theorem filter_allZ_nonidentityPauliWords (n q : ℕ) :
    ((nonidentityPauliWords n q).filter fun P => ∀ s, P s = none ∨ P s = some 2)
      = (zSupports n q).image pauliZSetLabel := by
  classical
  ext P
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hP, hZ⟩
    refine ⟨pauliSupport P, ?_, pauliZSetLabel_pauliSupport_of_forall hZ⟩
    rw [mem_zSupports, ← pauliWeight_eq_card_pauliSupport]
    have h := mem_nonidentityPauliWords.mp hP
    exact ⟨Finset.card_pos.mp (by rw [← pauliWeight_eq_card_pauliSupport]; exact h.1), h.2⟩
  · rintro ⟨S, hS, rfl⟩
    rw [mem_zSupports] at hS
    refine ⟨mem_nonidentityPauliWords.mpr ?_, forall_pauliZSetLabel_eq S⟩
    rw [pauliWeight_pauliZSetLabel]
    exact ⟨Finset.card_pos.mpr hS.1, hS.2⟩

/-- **At the centre the ensemble Hamiltonian is the gapped diagonal Hamiltonian.** -/
theorem pauliEnsembleOp_center (n q : ℕ) :
    pauliEnsembleOp n q (pauliEnsembleCenter n) = diagCLM (zProfile n q) := by
  classical
  rw [diagCLM_zProfile_eq, pauliEnsembleOp, pauliEnsembleMatrix]
  congr 2
  calc ∑ P ∈ nonidentityPauliWords n q,
        ((pauliEnsembleCenter n P : ℝ) : ℂ) • finitePauliMatrix P
      = ∑ P ∈ (nonidentityPauliWords n q).filter
          (fun P => ∀ s, P s = none ∨ P s = some 2), finitePauliMatrix P := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun P _ => ?_
        by_cases hP : ∀ s, P s = none ∨ P s = some 2 <;>
          simp [pauliEnsembleCenter, hP]
    _ = ∑ S ∈ zSupports n q, finitePauliMatrix (pauliZSetLabel S) := by
        rw [filter_allZ_nonidentityPauliWords,
          Finset.sum_image fun S _ T _ h => pauliZSetLabel_injective h]

/-- Every Pauli string acts as a unitary operator. -/
theorem toEuclideanCLM_finitePauliMatrix_mem_unitary (P : Fin n → Option (Fin 3)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (finitePauliMatrix P) ∈
      unitary (EuclideanSpace ℂ (Fin n → Bool) →L[ℂ] EuclideanSpace ℂ (Fin n → Bool)) := by
  have hstar : star (Matrix.toEuclideanCLM (𝕜 := ℂ) (finitePauliMatrix P))
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (finitePauliMatrix P) := by
    rw [← map_star]
    congr 1
    exact Matrix.isHermitian_iff_isSelfAdjoint.mp (finitePauliMatrix_isHermitian P)
  have hmul : Matrix.toEuclideanCLM (𝕜 := ℂ) (finitePauliMatrix P) *
      Matrix.toEuclideanCLM (𝕜 := ℂ) (finitePauliMatrix P) = 1 := by
    rw [← map_mul, finitePauliMatrix_mul_self, map_one]
  exact ⟨by rw [hstar]; exact hmul, by rw [hstar]; exact hmul⟩

theorem norm_toEuclideanCLM_finitePauliMatrix_le_one (P : Fin n → Option (Fin 3)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (finitePauliMatrix P)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [norm_apply_of_mem_unitary (toEuclideanCLM_finitePauliMatrix_mem_unitary P) x, one_mul]

theorem isHermitian_pauliEnsembleMatrix (n q : ℕ) (J : (Fin n → Option (Fin 3)) → ℝ) :
    (pauliEnsembleMatrix n q J).IsHermitian := by
  rw [pauliEnsembleMatrix, Matrix.IsHermitian, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sum]
  rw [show star ((pauliNormalization n q : ℝ) : ℂ) = ((pauliNormalization n q : ℝ) : ℂ) from
    Complex.conj_ofReal _]
  congr 1
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Matrix.conjTranspose_smul,
    show star ((J P : ℝ) : ℂ) = ((J P : ℝ) : ℂ) from Complex.conj_ofReal _]
  congr 1
  exact finitePauliMatrix_isHermitian P

theorem isSelfAdjoint_pauliEnsembleOp (n q : ℕ) (J : (Fin n → Option (Fin 3)) → ℝ) :
    IsSelfAdjoint (pauliEnsembleOp n q J) :=
  (Matrix.isHermitian_iff_isSelfAdjoint.mp (isHermitian_pauliEnsembleMatrix n q J)).map
    (Matrix.toEuclideanCLM (𝕜 := ℂ))

theorem pauliEnsembleOp_sub (n q : ℕ) (J K : (Fin n → Option (Fin 3)) → ℝ) :
    pauliEnsembleOp n q J - pauliEnsembleOp n q K
      = ((pauliNormalization n q : ℝ) : ℂ) •
        ∑ P ∈ nonidentityPauliWords n q,
          (((J P - K P : ℝ)) : ℂ) • Matrix.toEuclideanCLM (𝕜 := ℂ) (finitePauliMatrix P) := by
  rw [pauliEnsembleOp, pauliEnsembleOp, ← map_sub, pauliEnsembleMatrix, pauliEnsembleMatrix,
    ← smul_sub, ← Finset.sum_sub_distrib, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [← sub_smul, ← Complex.ofReal_sub, map_smul]

/-- **The ensemble is Lipschitz in its coefficients.**  A uniform coefficient perturbation of size
`w` moves the Hamiltonian by at most `m^{-1/2} m w`. -/
theorem norm_pauliEnsembleOp_sub_le (n q : ℕ) (J K : (Fin n → Option (Fin 3)) → ℝ)
    (w : ℝ) (h : ∀ P, |J P - K P| ≤ w) :
    ‖pauliEnsembleOp n q J - pauliEnsembleOp n q K‖
      ≤ pauliNormalization n q * (Quantum.nonidentityPauliWeightCount n q : ℝ) * w := by
  have hw : 0 ≤ w := le_trans (abs_nonneg _) (h (fun _ => none))
  have hterm : ∀ P ∈ nonidentityPauliWords n q,
      ‖(((J P - K P : ℝ)) : ℂ) • Matrix.toEuclideanCLM (𝕜 := ℂ) (finitePauliMatrix P)‖ ≤ w := by
    intro P _
    rw [norm_smul, Complex.norm_real]
    calc ‖J P - K P‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (finitePauliMatrix P)‖
        ≤ w * 1 := by
          refine mul_le_mul ?_ (norm_toEuclideanCLM_finitePauliMatrix_le_one P)
            (norm_nonneg _) hw
          rw [Real.norm_eq_abs]
          exact h P
      _ = w := mul_one w
  have hsum : ‖∑ P ∈ nonidentityPauliWords n q,
      (((J P - K P : ℝ)) : ℂ) • Matrix.toEuclideanCLM (𝕜 := ℂ) (finitePauliMatrix P)‖
      ≤ (Quantum.nonidentityPauliWeightCount n q : ℝ) * w := by
    calc ‖∑ P ∈ nonidentityPauliWords n q,
          (((J P - K P : ℝ)) : ℂ) • Matrix.toEuclideanCLM (𝕜 := ℂ) (finitePauliMatrix P)‖
        ≤ ∑ P ∈ nonidentityPauliWords n q,
            ‖(((J P - K P : ℝ)) : ℂ) • Matrix.toEuclideanCLM (𝕜 := ℂ) (finitePauliMatrix P)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _P ∈ nonidentityPauliWords n q, w := Finset.sum_le_sum hterm
      _ = ((nonidentityPauliWords n q).card : ℝ) * w := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (Quantum.nonidentityPauliWeightCount n q : ℝ) * w := by
          rw [card_nonidentityPauliWords]
  rw [pauliEnsembleOp_sub, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (pauliNormalization_nonneg n q)]
  calc pauliNormalization n q * ‖∑ P ∈ nonidentityPauliWords n q,
        (((J P - K P : ℝ)) : ℂ) • Matrix.toEuclideanCLM (𝕜 := ℂ) (finitePauliMatrix P)‖
      ≤ pauliNormalization n q * ((Quantum.nonidentityPauliWeightCount n q : ℝ) * w) :=
        mul_le_mul_of_nonneg_left hsum (pauliNormalization_nonneg n q)
    _ = pauliNormalization n q * (Quantum.nonidentityPauliWeightCount n q : ℝ) * w := by ring

/-- **The coefficient box bound.**  At half-width `ε²/(16m)` the ensemble Hamiltonian differs from
the centre by at most `ε²/(16√m)` in operator norm. -/
theorem norm_pauliEnsembleOp_sub_center_le (hn : 1 ≤ n) (hq : 1 ≤ q)
    (J : (Fin n → Option (Fin 3)) → ℝ) (ε : ℝ)
    (h : ∀ P, |J P - pauliEnsembleCenter n P|
      ≤ ε ^ (2 : ℕ) / (16 * (Quantum.nonidentityPauliWeightCount n q : ℝ))) :
    ‖pauliEnsembleOp n q J - diagCLM (zProfile n q)‖
      ≤ pauliNormalization n q * ε ^ (2 : ℕ) / 16 := by
  have hm : (0 : ℝ) < (Quantum.nonidentityPauliWeightCount n q : ℝ) := by
    exact_mod_cast Quantum.one_le_nonidentityPauliWeightCount hn hq
  have hbound := norm_pauliEnsembleOp_sub_le n q J (pauliEnsembleCenter n)
    (ε ^ (2 : ℕ) / (16 * (Quantum.nonidentityPauliWeightCount n q : ℝ))) h
  rw [pauliEnsembleOp_center] at hbound
  refine hbound.trans (le_of_eq ?_)
  field_simp

end

end GaloisForLFunctions.HTGeometry

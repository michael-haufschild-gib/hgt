/-
# The weighted Pauli ensemble reaches exactly the bounded-weight span

A support-invariant weight that is nonzero on every nonidentity label of weight at most `q` and zero
elsewhere makes the weighted Pauli ensemble a surjection of the coefficient space onto the
bounded-weight Pauli span.  So any statement that depends on a Hamiltonian only through its spectrum
transfers from "some element of the span" to "some coefficient vector of the ensemble".

Main results:
* `pauliSpan_eq_span_weighted` — the span of the weighted family is the bounded-weight span.
* `exists_pauliEnsemble_eq_of_mem_pauliSpan` — **every element of the span is an ensemble value**.
-/
import GaloisForLFunctions.HTGeometry.PauliBoundedWeightSpan
import GaloisForLFunctions.HTGeometry.PauliEnsembleCliffordCovariance

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n q : ℕ}

theorem pauliSpan_eq_span_weighted (w : (Fin n → Option (Fin 3)) → ℝ)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    (hwne : ∀ P : Fin n → Option (Fin 3),
      pauliWeight P ≤ q → P ≠ pauliIdentityLabel n → w P ≠ 0) :
    pauliSpan n q
      = Submodule.span ℝ (Set.range fun P : Fin n → Option (Fin 3) =>
          (w P : ℝ) • finitePauliMatrix P) := by
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro A ⟨P, hwt, hne, rfl⟩
    have hwP : w P ≠ 0 := hwne P hwt hne
    have hmem : (w P : ℝ) • finitePauliMatrix P ∈
        Submodule.span ℝ (Set.range fun P : Fin n → Option (Fin 3) =>
          (w P : ℝ) • finitePauliMatrix P) := Submodule.subset_span ⟨P, rfl⟩
    have := Submodule.smul_mem _ (w P)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hwP, one_smul] at this
  · refine Submodule.span_le.mpr ?_
    rintro A ⟨P, rfl⟩
    by_cases hP : pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n
    · exact Submodule.smul_mem _ _ (finitePauliMatrix_mem_pauliSpan hP.1 hP.2)
    · show w P • finitePauliMatrix P ∈ (pauliSpan n q : Set _)
      rw [hw P hP, zero_smul]
      exact Submodule.zero_mem _

/-- **Every element of the bounded-weight span is a value of the weighted ensemble.** -/
theorem exists_pauliEnsemble_eq_of_mem_pauliSpan (w : (Fin n → Option (Fin 3)) → ℝ)
    (hw : ∀ P : Fin n → Option (Fin 3),
      ¬ (pauliWeight P ≤ q ∧ P ≠ pauliIdentityLabel n) → w P = 0)
    (hwne : ∀ P : Fin n → Option (Fin 3),
      pauliWeight P ≤ q → P ≠ pauliIdentityLabel n → w P ≠ 0)
    {H : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ}
    (hH : H ∈ pauliSpan n q) :
    ∃ J : (Fin n → Option (Fin 3)) → ℝ, pauliEnsemble w J = H := by
  classical
  rw [pauliSpan_eq_span_weighted w hw hwne] at hH
  obtain ⟨J, hJ⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.mp hH
  refine ⟨J, ?_⟩
  rw [pauliEnsemble, ← hJ]
  refine Finset.sum_congr rfl fun P _ => ?_
  ext x y
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
  ring

end GaloisForLFunctions.HTGeometry

end

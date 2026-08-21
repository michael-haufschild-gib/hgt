/-
# A physical leaf extension stays in the weight-two Pauli span

The three summands of a physical leaf Hamiltonian are `H ⊗ 1`, `1 ⊗ (traceless field)` and
`(probe) ⊗ (edge)`.  Read through the snoc equivalence, the first keeps the weight of `H`, the second
is a multiple of `Z` on the new qubit, and the third raises the weight of the probe by at most one.
So a weight-`≤2` Hamiltonian with a weight-`≤1` probe extends to a weight-`≤2` Hamiltonian, and the
new probe is again weight `≤1`.

Main results:
* `trace_eq_zero_of_mem_pauliSpan` — everything in the span is traceless.
* `physicalLeaf_mem_pauliSpan` — **the leaf extension stays in the weight-two span**.
* `newProbe_mem_pauliSpan` — the new endpoint probe is weight one.
-/
import GaloisForLFunctions.HTGeometry.BoolPauliExpansion
import GaloisForLFunctions.HTGeometry.PhysicalObserverSpectralRealization

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- Everything in the bounded-weight Pauli span is traceless. -/
theorem trace_eq_zero_of_mem_pauliSpan {n q : ℕ}
    {A : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ}
    (hA : A ∈ pauliSpan n q) : A.trace = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro B ⟨P, -, hne, rfl⟩
    exact finitePauliMatrix_trace_eq_zero_of_ne_identity P hne
  · exact Matrix.trace_zero _ _
  · intro B B' _ _ hB hB'
    rw [Matrix.trace_add, hB, hB', add_zero]
  · intro c B _ hB
    rw [Matrix.trace_smul, hB, smul_zero]

theorem reindex_snocConfig_add {n : ℕ}
    (X Y : Matrix (FiniteQubitConfiguration (Fin n) × Bool)
      (FiniteQubitConfiguration (Fin n) × Bool) ℂ) :
    Matrix.reindex (snocConfig n) (snocConfig n) (X + Y)
      = Matrix.reindex (snocConfig n) (snocConfig n) X
        + Matrix.reindex (snocConfig n) (snocConfig n) Y := by
  ext x y
  rfl

/-- **A physical leaf extension of a weight-`≤2` Hamiltonian by a weight-`≤1` probe and a traceless
field stays in the weight-`≤2` Pauli span.** -/
theorem physicalLeaf_mem_pauliSpan {n : ℕ}
    {H V : Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ}
    (hH : H ∈ pauliSpan n 2) (hV : V ∈ pauliSpan n 1)
    (s : ℝ) {edge : Matrix Bool Bool ℂ} (hedge : edge.IsHermitian) :
    Matrix.reindex (snocConfig n) (snocConfig n)
        (physicalLeafHamiltonian H V (boolShift (s : ℂ)) edge)
      ∈ pauliSpan (n + 1) 2 := by
  rw [physicalLeafHamiltonian, reindex_snocConfig_add, reindex_snocConfig_add]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact couple_one_mem_pauliSpan hH
  · have hfield : Matrix.reindex (snocConfig n) (snocConfig n)
        (layerMatrixCoupling (1 : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) (Matrix.diagonal (boolShift (s : ℂ))))
        = ((s / 2 : ℝ) : ℂ) •
          coupleSnoc n (boolPauliOption (some 2))
            (1 : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) := by
      rw [show Matrix.reindex (snocConfig n) (snocConfig n)
          (layerMatrixCoupling (1 : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) (Matrix.diagonal (boolShift (s : ℂ))))
          = coupleSnoc n (Matrix.diagonal (boolShift (s : ℂ))) 1 from rfl]
      rw [diagonal_boolShift_eq, coupleSnoc_smul_right]
      norm_num
    rw [hfield]
    have hreal : (((s / 2 : ℝ)) : ℂ) • coupleSnoc n (boolPauliOption (some 2))
        (1 : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)
        = (s / 2 : ℝ) • coupleSnoc n (boolPauliOption (some 2))
          (1 : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) := by
      ext x y
      simp [Complex.real_smul]
    rw [hreal]
    exact Submodule.smul_mem _ _
      (pauliSpan_mono (by norm_num) (couple_id_mem_pauliSpan le_rfl 2))
  · exact couple_hermitian_mem_pauliSpan hV hedge

/-- The new endpoint probe of a leaf extension is a weight-one Pauli operator. -/
theorem newProbe_mem_pauliSpan {n : ℕ} {X : Matrix Bool Bool ℂ} (hX : X.IsHermitian)
    (hXtr : X.trace = 0) :
    Matrix.reindex (snocConfig n) (snocConfig n)
        (layerMatrixCoupling (1 : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) X)
      ∈ pauliSpan (n + 1) 1 := by
  classical
  obtain ⟨c, hXexp⟩ := exists_real_boolPauli_expansion hX
  have hc0 : c none = 0 := by
    have htr : X.trace = ∑ p : Option (Fin 3), (c p : ℂ) * (boolPauliOption p).trace := by
      rw [hXexp, Matrix.trace_sum]
      exact Finset.sum_congr rfl fun p _ => by rw [Matrix.trace_smul, smul_eq_mul]
    have hpt : ∀ p : Option (Fin 3), (boolPauliOption p).trace
        = if p = none then (2 : ℂ) else 0 := by
      intro p
      cases p with
      | none => simp [boolPauliOption, Matrix.trace, Matrix.diag]
      | some j =>
          fin_cases j <;>
            simp [boolPauliOption, finiteQubitPauli, Matrix.trace, Matrix.diag]
    rw [Finset.sum_congr rfl (fun p _ => by rw [hpt p]), hXtr] at htr
    simp only [mul_ite, mul_zero] at htr
    rw [Finset.sum_ite_eq' Finset.univ none (fun p => (c p : ℂ) * 2)] at htr
    rw [if_pos (Finset.mem_univ _)] at htr
    have h2 : (c none : ℝ) * 2 = 0 := by
      have : ((c none : ℝ) : ℂ) * 2 = 0 := htr.symm
      exact_mod_cast this
    linarith
  have hsum : Matrix.reindex (snocConfig n) (snocConfig n)
      (layerMatrixCoupling (1 : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) X)
      = ∑ p : Option (Fin 3), (c p : ℝ) •
        coupleSnoc n (boolPauliOption p)
          (1 : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) := by
    rw [show Matrix.reindex (snocConfig n) (snocConfig n)
        (layerMatrixCoupling (1 : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) X)
        = coupleSnoc n X 1 from rfl, hXexp]
    ext x y
    simp only [coupleSnoc_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      layerMatrixCoupling, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.real_smul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsum]
  refine Submodule.sum_mem _ fun p _ => ?_
  cases p with
  | none =>
      rw [hc0]
      simp
  | some j => exact Submodule.smul_mem _ _ (couple_id_mem_pauliSpan le_rfl j)

end GaloisForLFunctions.HTGeometry

end

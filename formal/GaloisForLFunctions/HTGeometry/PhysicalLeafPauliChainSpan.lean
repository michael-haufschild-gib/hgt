/-
# The leaf extension stays in the chain Pauli span

A physical leaf Hamiltonian `H ⊗ 1 + 1 ⊗ (field) + V ⊗ (edge)` whose old part is nearest-neighbour,
whose probe is supported at the previous endpoint and whose field is traceless is again
nearest-neighbour: the first summand keeps its support, the second is a one-site string at the new
site, and the third is supported on the new edge.

Main results:
* `couple_hermitian_mem_pauliChainSpan` — the coupling term is supported on the new edge.
* `physicalLeaf_mem_pauliChainSpan` — **the leaf extension stays nearest-neighbour**.
* `newProbe_mem_pauliSiteSpan` — the new endpoint probe is a one-site string at the new site.
-/
import GaloisForLFunctions.HTGeometry.PauliChainSpan
import GaloisForLFunctions.HTGeometry.BoolPauliExpansion
import GaloisForLFunctions.HTGeometry.PhysicalObserverSpectralRealization

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

theorem reindex_snocConfig_add' {n : ℕ}
    (X Y : Matrix (FiniteQubitConfiguration (Fin n) × Bool)
      (FiniteQubitConfiguration (Fin n) × Bool) ℂ) :
    Matrix.reindex (snocConfig n) (snocConfig n) (X + Y)
      = Matrix.reindex (snocConfig n) (snocConfig n) X
        + Matrix.reindex (snocConfig n) (snocConfig n) Y := by
  ext x y
  rfl

/-- **Coupling the previous endpoint probe to any Hermitian factor on the new site stays
nearest-neighbour.** -/
theorem couple_hermitian_mem_pauliChainSpan {m : ℕ}
    {A : Matrix (FiniteQubitConfiguration (Fin (m + 1)))
      (FiniteQubitConfiguration (Fin (m + 1))) ℂ}
    (hA : A ∈ pauliSiteSpan (m + 1) (Fin.last m))
    {B : Matrix Bool Bool ℂ} (hB : B.IsHermitian) :
    coupleSnoc (m + 1) B A ∈ pauliChainSpan (m + 2) := by
  classical
  obtain ⟨c, hBexp⟩ := exists_real_boolPauli_expansion hB
  have hsum : coupleSnoc (m + 1) B A
      = ∑ p : Option (Fin 3), (c p : ℂ) • coupleSnoc (m + 1) (boolPauliOption p) A := by
    rw [hBexp]
    ext x y
    simp only [coupleSnoc_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      layerMatrixCoupling, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsum]
  refine Submodule.sum_mem _ fun p _ => ?_
  refine Submodule.smul_mem _ _ ?_
  cases p with
  | none =>
      exact pauliSiteSpan_le_pauliChainSpan _ _ (couple_one_mem_pauliSiteSpan hA)
  | some j => exact couple_last_mem_pauliChainSpan j hA

/-- **A physical leaf extension of a nearest-neighbour Hamiltonian by an endpoint probe and a
traceless field is nearest-neighbour.** -/
theorem physicalLeaf_mem_pauliChainSpan {m : ℕ}
    {H V : Matrix (FiniteQubitConfiguration (Fin (m + 1)))
      (FiniteQubitConfiguration (Fin (m + 1))) ℂ}
    (hH : H ∈ pauliChainSpan (m + 1)) (hV : V ∈ pauliSiteSpan (m + 1) (Fin.last m))
    (s : ℝ) {edge : Matrix Bool Bool ℂ} (hedge : edge.IsHermitian) :
    Matrix.reindex (snocConfig (m + 1)) (snocConfig (m + 1))
        (physicalLeafHamiltonian H V (boolShift (s : ℂ)) edge)
      ∈ pauliChainSpan (m + 2) := by
  rw [physicalLeafHamiltonian, reindex_snocConfig_add', reindex_snocConfig_add']
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact couple_one_mem_pauliChainSpan hH
  · have hfield : Matrix.reindex (snocConfig (m + 1)) (snocConfig (m + 1))
        (layerMatrixCoupling (1 : Matrix (FiniteQubitConfiguration (Fin (m + 1)))
          (FiniteQubitConfiguration (Fin (m + 1))) ℂ) (Matrix.diagonal (boolShift (s : ℂ))))
        = ((s / 2 : ℝ) : ℂ) •
          coupleSnoc (m + 1) (boolPauliOption (some 2))
            (1 : Matrix (FiniteQubitConfiguration (Fin (m + 1)))
              (FiniteQubitConfiguration (Fin (m + 1))) ℂ) := by
      rw [show Matrix.reindex (snocConfig (m + 1)) (snocConfig (m + 1))
          (layerMatrixCoupling (1 : Matrix (FiniteQubitConfiguration (Fin (m + 1)))
            (FiniteQubitConfiguration (Fin (m + 1))) ℂ)
            (Matrix.diagonal (boolShift (s : ℂ))))
          = coupleSnoc (m + 1) (Matrix.diagonal (boolShift (s : ℂ))) 1 from rfl]
      rw [diagonal_boolShift_eq, coupleSnoc_smul_right]
      norm_num
    rw [hfield]
    have hreal : (((s / 2 : ℝ)) : ℂ) • coupleSnoc (m + 1) (boolPauliOption (some 2))
        (1 : Matrix (FiniteQubitConfiguration (Fin (m + 1)))
          (FiniteQubitConfiguration (Fin (m + 1))) ℂ)
        = (s / 2 : ℝ) • coupleSnoc (m + 1) (boolPauliOption (some 2))
          (1 : Matrix (FiniteQubitConfiguration (Fin (m + 1)))
            (FiniteQubitConfiguration (Fin (m + 1))) ℂ) := by
      ext x y
      simp [Complex.real_smul]
    rw [hreal]
    exact Submodule.smul_mem _ _
      (pauliSiteSpan_le_pauliChainSpan _ _ (couple_field_mem_pauliSiteSpan (m + 1) 2))
  · exact couple_hermitian_mem_pauliChainSpan hV hedge

/-- **The new endpoint probe of a leaf extension is a one-site string at the new site.** -/
theorem newProbe_mem_pauliSiteSpan {n : ℕ} {X : Matrix Bool Bool ℂ} (hX : X.IsHermitian)
    (hXtr : X.trace = 0) :
    Matrix.reindex (snocConfig n) (snocConfig n)
        (layerMatrixCoupling (1 : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) X)
      ∈ pauliSiteSpan (n + 1) (Fin.last n) := by
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
  | some j => exact Submodule.smul_mem _ _ (couple_field_mem_pauliSiteSpan n j)

end GaloisForLFunctions.HTGeometry

end

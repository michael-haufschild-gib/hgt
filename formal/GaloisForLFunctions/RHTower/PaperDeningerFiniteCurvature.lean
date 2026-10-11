import GaloisForLFunctions.RHTower.PaperDeningerMateOperator
import GaloisForLFunctions.HTGeometry.HilbertSchmidtFiniteRankDensity

/-! # Finite curvature traces versus the completed compact-ideal obstruction

Literal finite degree matrices have zero traces of every positive power. Their
full Hilbert-space cutoffs converge strongly, but convergence in operator norm
occurs exactly on the critical line. Every finite cutoff has zero ideal cost.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry ContinuousLinearMap Filter Topology
open scoped BigOperators

def paperDeningerFiniteModes (N : ℕ) : Finset (ℕ × Fin 2) :=
  (Finset.range N).product Finset.univ

@[simp] theorem mem_paperDeningerFiniteModes (N : ℕ) (p : ℕ × Fin 2) :
    p ∈ paperDeningerFiniteModes N ↔ p.1 < N := by
  simp [paperDeningerFiniteModes]

theorem paperDeningerFiniteModes_tendsto : Tendsto paperDeningerFiniteModes atTop atTop := by
  apply tendsto_atTop.2
  intro S
  apply S.eventually_all.2
  intro p _
  filter_upwards [eventually_ge_atTop (p.1 + 1)] with N hN
  exact (mem_paperDeningerFiniteModes N p).2 (by omega)

def paperDeningerFiniteOperator (s : ℂ) (N : ℕ) : PaperCornerSpace →L[ℂ] PaperCornerSpace :=
  hsTruncation (HilbertSchmidt.lpBasis (ℕ × Fin 2))
    (paperDeningerMateOperator s) (paperDeningerFiniteModes N)

theorem paperDeningerFiniteOperator_compact (s : ℂ) (N : ℕ) :
    IsCompactOperator (paperDeningerFiniteOperator s N) :=
  isCompactOperator_hsTruncation _ _ _

theorem paperDeningerFiniteOperator_traceCost (s : ℂ) (N : ℕ) :
    compactOperatorTraceCost PaperCornerSpace (paperDeningerFiniteOperator s N) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperDeningerFiniteOperator_compact s N)

theorem paperDeningerFiniteOperator_strong_tendsto (s : ℂ) (x : PaperCornerSpace) :
    Tendsto (fun N => paperDeningerFiniteOperator s N x) atTop
      (𝓝 (paperDeningerMateOperator s x)) := by
  have h := (hasSum_inner_smul (HilbertSchmidt.lpBasis (ℕ × Fin 2))
    (paperDeningerMateOperator s) x).comp paperDeningerFiniteModes_tendsto
  simpa only [paperDeningerFiniteOperator, hsTruncation_apply, Function.comp_def] using h

theorem paperDeningerFiniteOperator_norm_tendsto_iff (s : ℂ) :
    Tendsto (paperDeningerFiniteOperator s) atTop (𝓝 (paperDeningerMateOperator s)) ↔
      s.re = 1 / 2 := by
  constructor
  · intro h
    exact (paperDeningerMateOperator_compact_iff s).mp
      (isClosed_setOf_isCompactOperator.mem_of_tendsto h
        (Eventually.of_forall (paperDeningerFiniteOperator_compact s)))
  · intro h
    simpa [paperDeningerFiniteOperator, paperDeningerMateOperator_critical s h,
      hsTruncation] using (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => (0 : PaperCornerSpace →L[ℂ] PaperCornerSpace)) atTop (𝓝 0))

theorem paperDeningerFiniteOperator_gap (s : ℂ) (N : ℕ) :
    (if s.re = 1 / 2 then 0 else 1) ≤
      ‖paperDeningerMateOperator s - paperDeningerFiniteOperator s N‖ :=
  paperDeningerMateOperator_compact_gap s
    ⟨paperDeningerFiniteOperator s N, paperDeningerFiniteOperator_compact s N⟩

/-- The finite matrix is extracted from the actual full Hilbert-space cutoff. -/
def paperDeningerFiniteMatrix (s : ℂ) (N : ℕ) :
    Matrix (Fin N × Fin 2) (Fin N × Fin 2) ℂ := fun i j =>
  inner ℂ (HilbertSchmidt.lpBasis (ℕ × Fin 2) (i.1.val, i.2))
    (paperDeningerFiniteOperator s N (HilbertSchmidt.lpBasis (ℕ × Fin 2) (j.1.val, j.2)))

theorem paperDeningerFiniteMatrix_entry (s : ℂ) (N : ℕ) (i j : Fin N × Fin 2) :
    paperDeningerFiniteMatrix s N i j =
      if i.1 = j.1 then (paperDeningerNormalizedFrame s i.1.val i.2 j.2 : ℂ) else 0 := by
  rw [paperDeningerFiniteMatrix, paperDeningerFiniteOperator, hsTruncation_apply_basis]
  simp only [mem_paperDeningerFiniteModes, j.1.isLt, if_pos, HilbertSchmidt.lpBasis_apply,
    lp.inner_single_left, paperDeningerMateOperator_apply]
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [paperDeningerNormalizedFrame_eq, lp.single_apply, Prod.mk.injEq, Fin.val_inj]

theorem paperDeningerFiniteMatrix_sq (s : ℂ) (N : ℕ) :
    paperDeningerFiniteMatrix s N ^ 2 = 0 := by
  ext i j
  rw [pow_two, Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  rintro ⟨k, b⟩ _
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [paperDeningerFiniteMatrix_entry, paperDeningerNormalizedFrame_eq]

theorem paperDeningerFiniteMatrix_trace (s : ℂ) (N : ℕ) :
    Matrix.trace (paperDeningerFiniteMatrix s N) = 0 := by
  apply Finset.sum_eq_zero
  rintro ⟨j, b⟩ _
  fin_cases b <;> simp [paperDeningerFiniteMatrix_entry, paperDeningerNormalizedFrame_eq]

theorem paperDeningerFiniteMatrix_trace_pow (s : ℂ) (N m : ℕ) :
    Matrix.trace (paperDeningerFiniteMatrix s N ^ (m + 1)) = 0 := by
  cases m with
  | zero => simpa using paperDeningerFiniteMatrix_trace s N
  | succ m =>
    rw [show m + 1 + 1 = 2 + m by omega, pow_add, paperDeningerFiniteMatrix_sq, zero_mul]
    simp

end
end RHTower

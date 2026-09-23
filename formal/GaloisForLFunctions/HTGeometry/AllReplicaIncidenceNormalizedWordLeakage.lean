import GaloisForLFunctions.HTGeometry.LocalPauliUnitMassSynthesis

/-!
# The incidence-normalized local-word leakage law, unconditionally

Each label's unit-mass synthesis comes with its own index set; summing the index sets over the
label set and extending each coefficient family by zero off its own fibre gives one index set that
serves every label at once, with unit mass preserved.  Feeding that uniform synthesis into the
leakage budget removes the last hypothesis: for every finite replica set, every register size and
every incidence cut off the sitewise singlet sector, the weighted word-level leakage, normalized by
the label count, is at least `2D²/(D²-1)` times the dimension drop.
-/

open scoped BigOperators Matrix MatrixOrder Pointwise

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

variable (R : Type*) [Fintype R] [DecidableEq R] (n : ℕ)

/-- **One index set for every label.**  The disjoint union of the per-label word index sets
carries a unit-mass synthesis of every replicated Pauli commutator direction simultaneously. -/
theorem exists_uniformUnitMassSynthesis :
    ∃ (ι : Type) (_ : Fintype ι)
      (c : NonidentityPauliLabel n → ι → ℂ)
      (W : NonidentityPauliLabel n → ι →
        Matrix ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))
          ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n))) ℂ),
      (∀ q w, W q w ∈ twoLocalReplicaCommutatorSet R n ^ n) ∧
      (∀ q, ∑ w, ‖c q w‖ = 1) ∧
      (∀ q, finiteReplicaFullPauliCommutatorMatrix R n q = ∑ w, c q w • W q w) := by
  classical
  choose ix hix c0 W0 hmem0 hmass0 hsum0 using
    fun q : NonidentityPauliLabel n =>
      finiteReplicaFullPauliCommutatorMatrix_hasUnitMassSynthesis R n q
  letI : ∀ q : NonidentityPauliLabel n, Fintype (ix q) := hix
  refine ⟨Σ q : NonidentityPauliLabel n, ix q, inferInstance,
    fun q p => if p.1 = q then c0 p.1 p.2 else 0,
    fun q p => if p.1 = q then W0 p.1 p.2 else 1, ?_, ?_, ?_⟩
  · intro q p
    by_cases hp : p.1 = q
    · simp only [hp]
      exact hmem0 p.1 p.2
    · simp only [if_neg hp]
      exact one_mem_setPow (Set.mem_insert _ _) n
  · intro q
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single q]
    · simpa using hmass0 q
    · intro b _ hbq
      refine Finset.sum_eq_zero fun w _ => ?_
      simp only [if_neg hbq, norm_zero]
    · intro hq
      exact absurd (Finset.mem_univ q) hq
  · intro q
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single q]
    · simpa using hsum0 q
    · intro b _ hbq
      refine Finset.sum_eq_zero fun w _ => ?_
      simp only [if_neg hbq, zero_smul]
    · intro hq
      exact absurd (Finset.mem_univ q) hq

/-- **Theorem E -- the all-replica incidence-normalized local-word leakage law.** -/
theorem finiteAllReplicaFullPauli_incidenceNormalized_wordLeakage (hn : 1 ≤ n)
    {PU PV : Matrix ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))
      ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n))) ℂ}
    (hUherm : PUᴴ = PU) (hUidem : PU * PU = PU) (hVidem : PV * PV = PV)
    (hUQ : hermitianMatrixFamilyCommonKernelProjection
      (finiteReplicaFullPauliCommutatorMatrix R n) * PU = 0) :
    ∃ (ι : Type) (_ : Fintype ι)
      (c : NonidentityPauliLabel n → ι → ℂ)
      (W : NonidentityPauliLabel n → ι →
        Matrix ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n)))
          ((R → Fin (2 ^ n)) × (R → Fin (2 ^ n))) ℂ),
      (∀ q w, W q w ∈ twoLocalReplicaCommutatorSet R n ^ n) ∧
      (∀ q, ∑ w, ‖c q w‖ = 1) ∧
      (∀ q, finiteReplicaFullPauliCommutatorMatrix R n q = ∑ w, c q w • W q w) ∧
      2 * ((2 : ℝ) ^ n) ^ (2 : ℕ) * ((PU.trace).re - (PV.trace).re) / (((2 : ℝ) ^ n) ^ (2 : ℕ) - 1)
        ≤ (∑ q : NonidentityPauliLabel n, ∑ w, ‖c q w‖ * hsSqRe ((1 - PV) * W q w * PU))
            / (((2 : ℝ) ^ n) ^ (2 : ℕ) - 1) := by
  obtain ⟨ι, hι, c, W, hmem, hmass, hsyn⟩ := exists_uniformUnitMassSynthesis R n
  letI : Fintype ι := hι
  exact ⟨ι, hι, c, W, hmem, hmass, hsyn,
    finiteAllReplicaFullPauli_leakage_budget R n hn hUherm hUidem hVidem hUQ c W hmass hsyn⟩

end

end GaloisForLFunctions.HTGeometry

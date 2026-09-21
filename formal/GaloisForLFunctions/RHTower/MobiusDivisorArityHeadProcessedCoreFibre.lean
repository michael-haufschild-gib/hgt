import GaloisForLFunctions.RHTower.MobiusDivisorArityHeadCoreDiagonal

/-!
# Processed-core coordinates for the arity-head covariance

Each residual-label fibre is partitioned by the source's processed prime core.
This is the source coordinate system in which the remaining core-changing
arity-head charge is an off-diagonal finite bilinear form.
-/

noncomputable section
open Finset
namespace RHTower

/-- Literal source mass with residual label `R` and processed prime core `A`. -/
def mobiusDivisorSelectionProcessedCoreFibre
    (M : ℕ) (P A R : Finset ℕ) : ℝ :=
  ∑ d ∈ mobiusDivisorSelectionIndices M,
    if d.primeFactors \ P = R ∧ d.primeFactors ∩ P = A then
      mobiusDivisorDilationChannel M d
    else 0

/-- Every residual-label fibre is exactly the sum of its processed-core
coordinates. -/
theorem mobiusDivisorSelectionFibre_eq_sum_processedCoreFibre
    (M : ℕ) (P R : Finset ℕ) :
    mobiusDivisorSelectionFibre M P R =
      ∑ A ∈ P.powerset, mobiusDivisorSelectionProcessedCoreFibre M P A R := by
  unfold mobiusDivisorSelectionFibre subsetLabelFibre
    mobiusDivisorSelectionProcessedCoreFibre
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  by_cases hres : d.primeFactors \ P = R
  · rw [if_pos hres]
    rw [sum_eq_single (d.primeFactors ∩ P)]
    · simp [hres]
    · intro A hA hne
      have hcore : d.primeFactors ∩ P ≠ A := Ne.symm hne
      simp [hcore]
    · exact fun h => (h (mem_powerset.mpr inter_subset_right)).elim
  · simp [hres]

private lemma source_eq_processedCore_product
    {M : ℕ} {P A R : Finset ℕ} {d : ℕ}
    (hd : d ∈ mobiusDivisorSelectionIndices M)
    (hres : d.primeFactors \ P = R)
    (hcore : d.primeFactors ∩ P = A) :
    d = ∏ q ∈ A ∪ R, q := by
  have hsq : Squarefree d := (mem_filter.mp hd).2
  calc
    d = ∏ q ∈ d.primeFactors, q := (Nat.prod_primeFactors_of_squarefree hsq).symm
    _ = ∏ q ∈ (d.primeFactors \ P) ∪ (d.primeFactors ∩ P), q := by
      rw [sdiff_union_inter]
    _ = ∏ q ∈ R ∪ A, q := by rw [hres, hcore]
    _ = ∏ q ∈ A ∪ R, q := by rw [union_comm]

/-- A processed-core/residual-label coordinate contains at most one literal
squarefree source channel. -/
theorem mobiusDivisorSelectionProcessedCoreFibre_eq_singleton
    (M : ℕ) (P A R : Finset ℕ) :
    mobiusDivisorSelectionProcessedCoreFibre M P A R =
      if (∏ q ∈ A ∪ R, q) ∈ mobiusDivisorSelectionIndices M ∧
          (∏ q ∈ A ∪ R, q).primeFactors \ P = R ∧
          (∏ q ∈ A ∪ R, q).primeFactors ∩ P = A then
        mobiusDivisorDilationChannel M (∏ q ∈ A ∪ R, q)
      else 0 := by
  let n := ∏ q ∈ A ∪ R, q
  unfold mobiusDivisorSelectionProcessedCoreFibre
  by_cases hn : n ∈ mobiusDivisorSelectionIndices M ∧
      n.primeFactors \ P = R ∧ n.primeFactors ∩ P = A
  · rw [if_pos hn]
    let f : ℕ → ℝ := fun d =>
      if d.primeFactors \ P = R ∧ d.primeFactors ∩ P = A then
        mobiusDivisorDilationChannel M d
      else 0
    change (∑ d ∈ mobiusDivisorSelectionIndices M, f d) =
      mobiusDivisorDilationChannel M n
    have hpoint : f n = mobiusDivisorDilationChannel M n := by
      dsimp [f]
      rw [if_pos ⟨hn.2.1, hn.2.2⟩]
    exact (sum_eq_single n (by
      intro d hd hne
      have hzero : ¬(d.primeFactors \ P = R ∧ d.primeFactors ∩ P = A) := by
        intro hlabels
        exact hne (source_eq_processedCore_product hd hlabels.1 hlabels.2)
      dsimp [f]
      rw [if_neg hzero])
      (by intro hnot; exact (hnot hn.1).elim)).trans hpoint
  · rw [if_neg hn]
    apply sum_eq_zero
    intro d hd
    by_cases hlabels : d.primeFactors \ P = R ∧ d.primeFactors ∩ P = A
    · have heq : d = n := source_eq_processedCore_product hd hlabels.1 hlabels.2
      subst d
      exact (hn ⟨hd, hlabels⟩).elim
    · simp [hlabels]

end RHTower

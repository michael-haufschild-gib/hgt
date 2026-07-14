import GaloisForLFunctions.HTGeometry.FiniteRangeProjectiveTail
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Cofinite Gram polarization of coefficient tails

A finite family of complex coefficient functions is independent modulo finite support exactly when
every finite deletion leaves a finite square evaluation packet with strictly positive Gram matrix.
This converts the tail matroid into a deletion-robust positive geometry.

In a prime-Dirichlet application, positive weights may be inserted into the selected rows.  For
unit-phase coefficients the diagonal then consists of partial sums of the all-positive prime
carrier, while the off-diagonal entries are cross-Hadamard carriers.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The column vector obtained by evaluating one coefficient function on a square packet outside
a deleted coordinate set. -/
def cofiniteEvaluationColumn
    {J P : Type*} [Fintype J]
    (c : J → P → ℂ) (F : Set P) (points : J → {p : P // p ∉ F})
    (j : J) : EuclideanSpace ℂ J :=
  WithLp.toLp 2 fun row => c j (points row)

/-- The Hermitian Gram matrix of a square cofinite evaluation packet. -/
def cofiniteEvaluationGram
    {J P : Type*} [Fintype J]
    (c : J → P → ℂ) (F : Set P) (points : J → {p : P // p ∉ F}) :
    Matrix J J ℂ :=
  Matrix.gram ℂ (cofiniteEvaluationColumn c F points)

/-- Tail independence makes the coefficient family linearly independent after deleting any
finite coordinate set. -/
theorem TailCoefficientIndependent.linearIndependent_on_compl
    {J P : Type*} [Fintype J]
    (c : J → P → ℂ) (htail : TailCoefficientIndependent c)
    (F : Set P) (hF : F.Finite) :
    LinearIndependent ℂ
      (fun j => fun p : {p : P // p ∉ F} => c j p) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro q hq
  have hqzero : q = 0 := by
    apply htail q
    apply hF.subset
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    by_contra hpF
    have hpoint := congrFun hq ⟨p, hpF⟩
    apply hp
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hpoint
  exact fun i => congrFun hqzero i

/-- After every finite deletion, a tail-independent family admits a square strictly positive Gram
packet. -/
theorem TailCoefficientIndependent.exists_cofinite_posDef_evaluationGram
    {J P : Type*} [Fintype J] [DecidableEq J]
    (c : J → P → ℂ) (htail : TailCoefficientIndependent c)
    (F : Set P) (hF : F.Finite) :
    ∃ points : J → {p : P // p ∉ F},
      (cofiniteEvaluationGram c F points).PosDef := by
  have hlin := htail.linearIndependent_on_compl c F hF
  obtain ⟨points, hfull⟩ :=
    GaloisForLFunctions.HTGeometry.exists_fullRank_evaluation_packet
    (fun j => fun p : {p : P // p ∉ F} => c j p) hlin
  refine ⟨points, ?_⟩
  apply Matrix.posDef_gram_of_linearIndependent
  have hcols : LinearIndependent ℂ
      (Matrix.of fun row j => c j (points row) : Matrix J J ℂ).col :=
    Matrix.linearIndependent_cols_iff_isUnit.mpr hfull
  simpa [cofiniteEvaluationColumn, Matrix.col_apply] using hcols

/-- **Cofinite Gram polarization law.**  Independence modulo finite support is equivalent to
strict positive Gram realizability after every finite deletion. -/
theorem tailCoefficientIndependent_iff_cofinite_posDef_evaluationGram
    {J P : Type*} [Fintype J] [DecidableEq J]
    (c : J → P → ℂ) :
    TailCoefficientIndependent c ↔
      ∀ F : Set P, F.Finite →
        ∃ points : J → {p : P // p ∉ F},
          (cofiniteEvaluationGram c F points).PosDef := by
  constructor
  · intro htail F hF
    exact htail.exists_cofinite_posDef_evaluationGram c F hF
  · intro hgram q hsupp
    let F : Set P := {p | ∑ j, q j * c j p ≠ 0}
    obtain ⟨points, hpos⟩ := hgram F hsupp
    have hlin : LinearIndependent ℂ (cofiniteEvaluationColumn c F points) :=
      Matrix.posDef_gram_iff_linearIndependent.mp hpos
    rw [Fintype.linearIndependent_iff] at hlin
    apply funext
    apply hlin q
    funext row
    have hzero : ∑ j, q j * c j (points row) = 0 := by
      apply not_ne_iff.mp
      exact (points row).property
    simpa [cofiniteEvaluationColumn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      using hzero

/-- A unit-phase packet has constant diagonal Gram entries: each diagonal is the packet size. -/
theorem cofiniteEvaluationGram_phase_diagonal
    {J P : Type*} [Fintype J]
    (c : J → P → ℂ) (F : Set P) (points : J → {p : P // p ∉ F})
    (hphase : ∀ j p, ‖c j p‖ = 1) (j : J) :
    cofiniteEvaluationGram c F points j j = Fintype.card J := by
  rw [cofiniteEvaluationGram, Matrix.gram_apply]
  rw [PiLp.inner_apply]
  simp only [cofiniteEvaluationColumn, WithLp.ofLp_toLp, RCLike.inner_apply]
  calc
    ∑ row, star (c j (points row)) * c j (points row) =
        ∑ _row : J, (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro row _
          rw [← RCLike.normSq_eq_def]
          simp [hphase]
    _ = Fintype.card J := by simp

end

end GaloisForLFunctions.HTGeometry

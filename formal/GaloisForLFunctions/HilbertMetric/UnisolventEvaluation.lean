import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

/-!
# Unisolvent evaluation bases

A finite linearly independent family of real-valued feature functions admits exactly as many
pairwise distinct sampling nodes as features, with nonsingular evaluation matrix.  The proof is
unconditional: it derives the nodes from the spanning property of all evaluation rows rather than
assuming an interpolation certificate.

This is the finite interpolation connector used by coherent-collision arguments.  In particular,
once polynomial feature independence is supplied, moment-cancelling coefficients are obtained from
an actual invertible evaluation matrix.
-/

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {κ X : Type*} [Fintype κ]

/-- The evaluation row of a finite feature family at a sampling node. -/
def evaluationRow (φ : κ → X → ℝ) (x : X) : κ → ℝ :=
  fun j => φ j x

/-- Independent feature functions have evaluation rows spanning the full coefficient space. -/
theorem span_range_evaluationRow_eq_top (φ : κ → X → ℝ)
    (hφ : LinearIndependent ℝ φ) :
    Submodule.span ℝ (Set.range (evaluationRow φ)) = ⊤ := by
  simpa only [evaluationRow, flip] using
    (span_flip_eq_top_iff_linearIndependent (f := φ)).2 hφ

/-- An independent finite feature family has pairwise distinct nodes whose evaluation rows are
linearly independent.  No nodes or nonsingularity certificate occur among the hypotheses. -/
theorem exists_injective_evaluation_basis (φ : κ → X → ℝ)
    (hφ : LinearIndependent ℝ φ) :
    ∃ nodes : κ → X, Function.Injective nodes ∧
      LinearIndependent ℝ (fun i => evaluationRow φ (nodes i)) := by
  let s : Set (κ → ℝ) := Set.range (evaluationRow φ)
  have hs : Submodule.span ℝ s = ⊤ := span_range_evaluationRow_eq_top φ hφ
  have hdim : Module.finrank ℝ (Submodule.span ℝ s) = Fintype.card κ := by
    rw [hs]
    simp
  obtain ⟨f, hf, _hspan, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ s
  let castIndex : Fin (Fintype.card κ) → Fin (Module.finrank ℝ (Submodule.span ℝ s)) :=
    Fin.cast hdim.symm
  have hcast : Function.Injective castIndex := by
    intro i j hij
    exact Fin.ext (congrArg
      (fun z : Fin (Module.finrank ℝ (Submodule.span ℝ s)) => z.val) hij)
  have hliCast : LinearIndependent ℝ (fun i => f (castIndex i)) :=
    hli.comp _ hcast
  have hfCast : ∀ i, f (castIndex i) ∈ Set.range (evaluationRow φ) := by
    intro i
    exact hf (castIndex i)
  choose nodesFin hnodesFin using hfCast
  have hliNodesFin : LinearIndependent ℝ (fun i => evaluationRow φ (nodesFin i)) := by
    simpa only [hnodesFin] using hliCast
  let nodes : κ → X := fun i => nodesFin (Fintype.equivFin κ i)
  have hliNodes : LinearIndependent ℝ (fun i => evaluationRow φ (nodes i)) :=
    hliNodesFin.comp _ (Fintype.equivFin κ).injective
  refine ⟨nodes, ?_, hliNodes⟩
  intro i j hij
  apply (Fintype.equivFin κ).injective
  apply hliNodesFin.injective
  simp [nodes, hij]

/-- The square evaluation matrix of a feature family at a node family. -/
def evaluationMatrix (φ : κ → X → ℝ) (nodes : κ → X) : Matrix κ κ ℝ :=
  fun i j => φ j (nodes i)

variable [DecidableEq κ]

/-- Independent features admit distinct nodes together with exact dual coefficients.  Each dual
coefficient row cancels every sampled feature moment except its designated one. -/
theorem exists_injective_nodes_delta_moments (φ : κ → X → ℝ)
    (hφ : LinearIndependent ℝ φ) :
    ∃ (nodes : κ → X) (coefficient : κ → κ → ℝ), Function.Injective nodes ∧
      ∀ q r, ∑ i, coefficient q i * φ r (nodes i) = if q = r then 1 else 0 := by
  obtain ⟨nodes, hinj, hli⟩ := exists_injective_evaluation_basis φ hφ
  have hspan : ⊤ ≤ Submodule.span ℝ
      (Set.range (fun i => evaluationRow φ (nodes i))) := by
    rw [hli.span_eq_top_of_card_eq_finrank' (by simp)]
  let b : Module.Basis κ ℝ (κ → ℝ) := Module.Basis.mk hli hspan
  let coefficient : κ → κ → ℝ := fun q i => b.equivFun (Pi.single q 1) i
  refine ⟨nodes, coefficient, hinj, ?_⟩
  intro q r
  have hsum := congrFun (b.sum_equivFun (Pi.single q 1)) r
  simpa [coefficient, b, evaluationRow, Pi.smul_apply, Pi.single_apply, eq_comm] using hsum

/-- Linear independence of evaluation rows forces the literal evaluation determinant
to be nonzero. -/
theorem evaluationMatrix_det_ne_zero (φ : κ → X → ℝ) (nodes : κ → X)
    (hli : LinearIndependent ℝ (fun i => evaluationRow φ (nodes i))) :
    (evaluationMatrix φ nodes).det ≠ 0 := by
  have hrows : LinearIndependent ℝ (evaluationMatrix φ nodes).row := by
    simpa [evaluationMatrix, evaluationRow] using hli
  exact ((evaluationMatrix φ nodes).isUnit_iff_isUnit_det.mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

/-- Every finite independent feature family admits pairwise distinct nodes with a nonsingular
evaluation matrix. -/
theorem exists_injective_nodes_det_ne_zero (φ : κ → X → ℝ)
    (hφ : LinearIndependent ℝ φ) :
    ∃ nodes : κ → X, Function.Injective nodes ∧ (evaluationMatrix φ nodes).det ≠ 0 := by
  obtain ⟨nodes, hinj, hli⟩ := exists_injective_evaluation_basis φ hφ
  exact ⟨nodes, hinj, evaluationMatrix_det_ne_zero φ nodes hli⟩

end

end GaloisForLFunctions.HilbertMetric

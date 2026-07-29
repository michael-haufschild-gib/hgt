import GaloisForLFunctions.HilbertMetric.UnisolventEvaluation

/-!
# Exact reconstruction on a prescribed evaluation packet

The unisolvent theorem chooses sampling nodes from linear independence of the feature functions.
For a packet of nodes already fixed by the problem, exact coefficient reconstruction has a sharper
criterion: it exists exactly when the literal evaluation matrix is nonsingular.  The inverse
matrix supplies the dual weights; conversely the feature-isolation identities are a left inverse.
-/

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

open scoped BigOperators

variable {κ X : Type*} [Fintype κ] [DecidableEq κ]

/-- A prescribed square evaluation packet has dual weights that isolate every feature and recover
every coefficient vector from its literal sampled values. -/
def PrescribedEvaluationDualReconstruction
    (φ : κ → X → ℝ) (nodes : κ → X) : Prop :=
  ∃ dual : κ → κ → ℝ,
    (∀ q r, ∑ i, dual q i * φ r (nodes i) = if q = r then 1 else 0) ∧
    ∀ (a : κ → ℝ) q,
      ∑ i, dual q i * (∑ r, a r * φ r (nodes i)) = a q

/-- **Exact prescribed-packet reconstruction criterion.**  Dual isolation and coefficient recovery
on fixed nodes exist exactly when their square evaluation matrix has nonzero determinant. -/
theorem prescribedEvaluationDualReconstruction_iff_det_ne_zero
    (φ : κ → X → ℝ) (nodes : κ → X) :
    PrescribedEvaluationDualReconstruction φ nodes ↔
      (evaluationMatrix φ nodes).det ≠ 0 := by
  constructor
  · rintro ⟨dual, hdelta, _hrecovery⟩
    let D : Matrix κ κ ℝ := fun q i => dual q i
    have hleft : D * evaluationMatrix φ nodes = 1 := by
      ext q r
      simpa [D, Matrix.mul_apply, evaluationMatrix, Matrix.one_apply] using hdelta q r
    exact Matrix.det_ne_zero_of_left_inverse hleft
  · intro hdet
    let P : Matrix κ κ ℝ := evaluationMatrix φ nodes
    let dual : κ → κ → ℝ := fun q i => P⁻¹ q i
    have hunit : IsUnit P.det := isUnit_iff_ne_zero.mpr (by simpa [P] using hdet)
    have hdelta : ∀ q r, ∑ i, dual q i * φ r (nodes i) =
        if q = r then 1 else 0 := by
      intro q r
      have hentry := congrArg (fun M : Matrix κ κ ℝ => M q r)
        (P.nonsing_inv_mul hunit)
      simpa [dual, P, Matrix.mul_apply, evaluationMatrix, Matrix.one_apply] using hentry
    refine ⟨dual, hdelta, ?_⟩
    intro a q
    calc
      ∑ i, dual q i * (∑ r, a r * φ r (nodes i)) =
          ∑ i, ∑ r, dual q i * (a r * φ r (nodes i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ r, ∑ i, dual q i * (a r * φ r (nodes i)) :=
        Finset.sum_comm
      _ = ∑ r, a r * (∑ i, dual q i * φ r (nodes i)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ r, a r * (if q = r then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hdelta q r]
      _ = a q := by simp

/-- **Exact recovery upgrades weak evaluation geometry to strict geometry.** For an arbitrary
prescribed square packet, positive semidefiniteness together with exact dual coefficient recovery
is equivalent to positive definiteness. Reconstruction supplies exactly the missing determinant
nondegeneracy. -/
theorem evaluationMatrix_posSemidef_and_dualReconstruction_iff_posDef
    (φ : κ → X → ℝ) (nodes : κ → X) :
    (evaluationMatrix φ nodes).PosSemidef ∧
        PrescribedEvaluationDualReconstruction φ nodes ↔
      (evaluationMatrix φ nodes).PosDef := by
  constructor
  · rintro ⟨hsemidef, hreconstruct⟩
    apply hsemidef.posDef_iff_det_ne_zero.mpr
    exact
      (prescribedEvaluationDualReconstruction_iff_det_ne_zero φ nodes).mp
        hreconstruct
  · intro hpos
    exact ⟨hpos.posSemidef,
      (prescribedEvaluationDualReconstruction_iff_det_ne_zero φ nodes).mpr
        hpos.det_pos.ne'⟩

end

end GaloisForLFunctions.HilbertMetric

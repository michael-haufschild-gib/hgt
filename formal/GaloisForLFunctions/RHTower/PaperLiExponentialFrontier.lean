import GaloisForLFunctions.RHTower.PaperLiExponentialProfile
import GaloisForLFunctions.RHTower.PaperLiNegativeOperator

/-! # The Cayley growth frontier as a compact-ideal frontier

The operators use the actual negative Li magnitudes with exponential budgets.
Every rate strictly above a proposed Cayley bound is compact exactly when that
bound holds. The proven closed-ideal trace records the same frontier.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

def paperLiExponentialOperator (b : PaperLiBudget) (r : PaperLiRate) :
    PaperLiHistory →L[ℂ] PaperLiHistory :=
  lpDiagonalCLM (fun n => (paperLiExponentialWeight b r n : ℂ)) zero_le_one
    (paperLiExponentialWeight_norm_le b r)

@[simp] theorem paperLiExponentialOperator_apply (b : PaperLiBudget) (r : PaperLiRate)
    (x : PaperLiHistory) (n : ℕ) :
    paperLiExponentialOperator b r x n = (paperLiExponentialWeight b r n : ℂ) * x n := rfl

theorem paperLiExponentialOperator_norm_le (b : PaperLiBudget) (r : PaperLiRate) :
    ‖paperLiExponentialOperator b r‖ ≤ 1 := norm_lpDiagonalCLM_le _ _ _

theorem paperLiExponentialOperator_compact {R : ℝ} (hR : 1 ≤ R)
    (b : PaperLiBudget) (r : PaperLiRate) (hRr : R < r.val)
    (hroots : ∀ ρ : ℂ, xi ρ = 0 → ‖xiRootV ρ‖ ≤ R) :
    IsCompactOperator (paperLiExponentialOperator b r) := by
  apply isCompactOperator_lpDiagonalCLM
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperLiExponentialWeight_nonneg b r _)] using
    paperLiExponentialWeight_tendsto hR b r hRr hroots

theorem paperLiExponentialOperator_unit_distance (b : PaperLiBudget) (r : PaperLiRate)
    (ρ : XiDivisorSupport) (hρ : r.val < ‖xiRootV (ρ : ℂ)‖) :
    compactIdealDistance (paperLiExponentialOperator b r) = 1 := by
  apply le_antisymm
  · have h := compactIdealDistance_le (paperLiExponentialOperator b r) 0 isCompactOperator_zero
    simp only [sub_zero] at h
    exact h.trans (paperLiExponentialOperator_norm_le b r)
  · obtain ⟨j, hj, hw⟩ := paperLiExponentialWeight_escape b r ρ hρ
    simpa only [norm_one, paperLiExponentialOperator] using
      paperDiagonalCluster_le_compactIdealDistance
        (fun n => (paperLiExponentialWeight b r n : ℂ)) zero_le_one
        (paperLiExponentialWeight_norm_le b r) j hj hw

theorem paperLiExponentialOperator_unit_gap (b : PaperLiBudget) (r : PaperLiRate)
    (ρ : XiDivisorSupport) (hρ : r.val < ‖xiRootV (ρ : ℂ)‖)
    (K : compactOperatorStarAlgebra PaperLiHistory) :
    1 ≤ ‖paperLiExponentialOperator b r - K.1‖ := by
  rw [← paperLiExponentialOperator_unit_distance b r ρ hρ]
  exact compactIdealDistance_le _ _ K.2

theorem paperLiExponentialOperator_traceCost_top (b : PaperLiBudget) (r : PaperLiRate)
    (ρ : XiDivisorSupport) (hρ : r.val < ‖xiRootV (ρ : ℂ)‖) :
    compactOperatorTraceCost PaperLiHistory (paperLiExponentialOperator b r) = ∞ := by
  apply (compactOperatorTraceCost_eq_top_iff _).mpr
  intro hc
  have hd := compactIdealDistance_eq_zero_of_isCompactOperator (paperLiExponentialOperator b r) hc
  rw [paperLiExponentialOperator_unit_distance b r ρ hρ] at hd
  exact one_ne_zero hd

/-- An unconditional equivalence for every proposed bound and every positive budget. -/
theorem paperLiExponential_compact_frontier (b : PaperLiBudget) (R : PaperLiRate) :
    (∀ ρ : ℂ, xi ρ = 0 → ‖xiRootV ρ‖ ≤ R.val) ↔
      ∀ r : PaperLiRate, R.val < r.val → IsCompactOperator (paperLiExponentialOperator b r) := by
  constructor
  · intro h r hr
    exact paperLiExponentialOperator_compact R.property b r hr h
  · intro h ρ hzero
    by_contra hbound
    have hlt : R.val < ‖xiRootV ρ‖ := lt_of_not_ge hbound
    let r : PaperLiRate := ⟨(R.val + ‖xiRootV ρ‖) / 2, by linarith [R.property]⟩
    have hRr : R.val < r.val := by dsimp [r]; linarith
    have hrρ : r.val < ‖xiRootV ρ‖ := by dsimp [r]; linarith
    let q : XiDivisorSupport := ⟨ρ, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hd := compactIdealDistance_eq_zero_of_isCompactOperator
      (paperLiExponentialOperator b r) (h r hRr)
    rw [paperLiExponentialOperator_unit_distance b r q hrρ] at hd
    exact one_ne_zero hd

theorem paperLiExponential_trace_frontier (b : PaperLiBudget) (R : PaperLiRate) :
    (∀ ρ : ℂ, xi ρ = 0 → ‖xiRootV ρ‖ ≤ R.val) ↔
      ∀ r : PaperLiRate, R.val < r.val →
        compactOperatorTraceCost PaperLiHistory (paperLiExponentialOperator b r) = 0 := by
  simp only [compactOperatorTraceCost_eq_zero_iff]
  exact paperLiExponential_compact_frontier b R

theorem paperLiExponential_compact_iff_RH (b : PaperLiBudget) :
    (∀ r : PaperLiRate, 1 < r.val → IsCompactOperator (paperLiExponentialOperator b r)) ↔
      RiemannHypothesis := by
  rw [riemannHypothesis_iff_cayley_le_one]
  exact (paperLiExponential_compact_frontier b ⟨1, le_rfl⟩).symm

theorem paperLiExponential_trace_iff_RH (b : PaperLiBudget) :
    (∀ r : PaperLiRate, 1 < r.val →
      compactOperatorTraceCost PaperLiHistory (paperLiExponentialOperator b r) = 0) ↔
      RiemannHypothesis := by
  simp only [compactOperatorTraceCost_eq_zero_iff]
  exact paperLiExponential_compact_iff_RH b

theorem paperLiExponential_trace_add_compact (b : PaperLiBudget) (r : PaperLiRate)
    (K : compactOperatorStarAlgebra PaperLiHistory) :
    compactOperatorTraceCost PaperLiHistory (paperLiExponentialOperator b r + K.1) =
      compactOperatorTraceCost PaperLiHistory (paperLiExponentialOperator b r) :=
  compactOperatorTraceCost_add_compact _ K

end
end RHTower

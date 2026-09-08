import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

/-!
# QNMModalResidue

Morikawa, arXiv:2608.29806, equations (31)--(32), separates modal residues
from observed amplitudes. The rank-one residue is invariant under independent
rescalings of its left and right vectors; its norm records their conditioning.
At zero left-right pairing the totalized expression is zero, not a claim that
a simple-pole expansion remains valid.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def qnmModalResidue (x y : E) : E →L[ℂ] E :=
  (inner ℂ y x)⁻¹ • InnerProductSpace.rankOne ℂ x y

theorem qnmModalResidue_idempotent (x y : E) :
    (qnmModalResidue x y).comp (qnmModalResidue x y) = qnmModalResidue x y := by
  ext v
  simp only [qnmModalResidue, ContinuousLinearMap.comp_apply, smul_apply,
    InnerProductSpace.rankOne_apply, inner_smul_right, smul_smul]
  congr 1
  by_cases h : inner ℂ y x = 0
  · simp [h]
  · field_simp

theorem norm_qnmModalResidue (x y : E) :
    ‖qnmModalResidue x y‖ = ‖x‖ * ‖y‖ / ‖inner ℂ y x‖ := by
  simp only [qnmModalResidue, norm_smul, norm_inv, InnerProductSpace.norm_rankOne]
  ring

theorem qnmModalResidue_observed (x y source observer : E) :
    inner ℂ observer (qnmModalResidue x y source) =
      inner ℂ observer x * inner ℂ y source / inner ℂ y x := by
  simp only [qnmModalResidue, smul_apply, InnerProductSpace.rankOne_apply, inner_smul_right]
  ring

theorem qnmModalResidue_dark_source (x y source : E) :
    qnmModalResidue x y source = 0 ↔
      inner ℂ y x = 0 ∨ inner ℂ y source = 0 ∨ x = 0 := by
  simp [qnmModalResidue, smul_eq_zero]

theorem qnmModalResidue_scale_right (x y : E) (a : ℂˣ) :
    qnmModalResidue ((a : ℂ) • x) y = qnmModalResidue x y := by
  ext v
  simp only [qnmModalResidue, smul_apply, InnerProductSpace.rankOne_apply,
    inner_smul_right, smul_smul]
  congr 1
  by_cases h : inner ℂ y x = 0
  · simp [h]
  · field_simp

theorem qnmModalResidue_scale_left (x y : E) (a : ℂˣ) :
    qnmModalResidue x ((a : ℂ) • y) = qnmModalResidue x y := by
  ext v
  simp only [qnmModalResidue, smul_apply, InnerProductSpace.rankOne_apply,
    inner_smul_left, smul_smul]
  congr 1
  by_cases h : inner ℂ y x = 0
  · simp [h]
  · have ha : starRingEnd ℂ (a : ℂ) ≠ 0 := by simp
    field_simp

end GaloisForLFunctions.HilbertMetric

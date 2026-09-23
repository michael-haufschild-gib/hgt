import GaloisForLFunctions.RHTower.XiShiftedHankelFarRightPositiveDefinite
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryFlux
import GaloisForLFunctions.RHTower.XiShiftedReciprocalHankelTailCriterion

/-!
# Cofinal recession of shifted-Xi Hankel defects

For every nonnegative shift, positivity of all finite shifted-Xi moment matrices is exactly RH.
On the other hand, every fixed finite family is strictly positive definite sufficiently far along
the square-mass ray.  Combining these unconditional facts gives a sharp RH-false alternative:
at every mass some finite block fails, but the size of every failing block escapes cofinally to
infinity as the mass tends right.

This rules out any closure based on a fixed determinant order.  A successful mass-flow argument
must control the moving null polynomial uniformly in its growing degree.
-/

open Matrix Filter

namespace RHTower

noncomputable section

/-- Matrix positive semidefiniteness is exactly nonnegativity of every original shifted-Xi
Hankel quadratic at the same finite order. -/
theorem xiShiftedMomentHankelMatrix_posSemidef_iff_quadratic_nonnegative
    (y : ℝ) (n : ℕ) :
    (xiShiftedMomentHankelMatrix y n).PosSemidef ↔
      ∀ c : Fin n → ℝ, 0 ≤ xiShiftedReciprocalHankelQuadratic y c := by
  constructor
  · intro h c
    have hq := h.dotProduct_mulVec_nonneg c
    change 0 ≤ xiShiftedMomentHankelQuadratic y n c at hq
    rw [xiShiftedMomentHankelQuadratic_eq] at hq
    exact hq
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (xiShiftedMomentHankelMatrix_isHermitian y n)
    intro c
    change 0 ≤ xiShiftedMomentHankelQuadratic y n c
    rw [xiShiftedMomentHankelQuadratic_eq]
    exact h c

/-- **All-block shifted-Hankel RH law.** At every fixed nonnegative shift, all finite shifted-Xi
moment matrices are PSD exactly when RH holds. -/
theorem xiShiftedMomentHankelMatrix_forall_posSemidef_iff_riemannHypothesis
    {y : ℝ} (hy : 0 ≤ y) :
    (∀ n : ℕ, (xiShiftedMomentHankelMatrix y n).PosSemidef) ↔
      RiemannHypothesis := by
  rw [← xiShiftedReciprocalHankelTailNonnegative_iff_riemannHypothesis hy 0,
    xiShiftedReciprocalHankelTailNonnegative_zero_iff]
  constructor
  · intro h n c
    have hq := (h n).dotProduct_mulVec_nonneg c
    change 0 ≤ xiShiftedMomentHankelQuadratic y n c at hq
    rw [xiShiftedMomentHankelQuadratic_eq] at hq
    exact hq
  · intro h n
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (xiShiftedMomentHankelMatrix_isHermitian y n)
    intro c
    change 0 ≤ xiShiftedMomentHankelQuadratic y n c
    rw [xiShiftedMomentHankelQuadratic_eq]
    exact h n c

/-- Every finite family indexed directly by matrix size is eventually simultaneously positive
definite along the square-mass ray. -/
theorem xiShiftedMomentHankelMatrix_squareParam_posDef_eventually_forall_size_le
    (d : ℕ) :
    ∀ᶠ w : ℝ in atTop, ∀ n ≤ d,
      (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosDef := by
  have hstep : ∀ n ∈ Finset.Iic d, ∀ᶠ w : ℝ in atTop,
      (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosDef :=
    fun n _ => xiShiftedMomentHankelMatrix_squareParam_posDef_eventually n
  filter_upwards [(eventually_all_finset (Finset.Iic d)).mpr hstep] with w hw
  intro n hn
  exact hw n (Finset.mem_Iic.mpr hn)

/-- **Cofinal defect recession.** If RH is false, shifted-Xi Hankel failure persists at every
nonnegative mass, yet for every fixed size bound all failing blocks eventually lie beyond it. -/
theorem xiShiftedHankelDefectDegree_escapes_atTop_of_not_riemannHypothesis
    (hnot : ¬ RiemannHypothesis) (d : ℕ) :
    ∀ᶠ w : ℝ in atTop, ∃ n : ℕ, d < n ∧
      ¬ (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosSemidef := by
  filter_upwards
      [xiShiftedMomentHankelMatrix_squareParam_posDef_eventually_forall_size_le d]
      with w hfixed
  have hy : 0 ≤ w ^ (2 : ℕ) := sq_nonneg w
  have hfail : ∃ n : ℕ,
      ¬ (xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n).PosSemidef := by
    by_contra hnone
    push Not at hnone
    exact hnot
      ((xiShiftedMomentHankelMatrix_forall_posSemidef_iff_riemannHypothesis hy).mp hnone)
  obtain ⟨n, hn⟩ := hfail
  refine ⟨n, ?_, hn⟩
  by_contra hnd
  have hle : n ≤ d := Nat.le_of_not_gt hnd
  exact hn (hfixed n hle).posSemidef

end

end RHTower

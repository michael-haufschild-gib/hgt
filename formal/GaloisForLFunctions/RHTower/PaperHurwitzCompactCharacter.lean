import GaloisForLFunctions.RHTower.PaperHurwitzPowerRegularization
import GaloisForLFunctions.HTGeometry.PaperConvergentDiagonal

/-!
# Compact-ideal character of the Hurwitz power-energy resolvent

The full native energy history defines a bounded diagonal resolvent. Its compact quotient is
exactly the characteristic function of the critical line. The proven paper ideal trace is thus
infinite on the line and zero off it, independently of every compact perturbation.
-/

namespace RHTower

noncomputable section
open Filter Classical GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Topology ENNReal

/-- The Hilbert space retains every prescribed dyadic power level. -/
abbrev PaperHurwitzHistory := lp (fun _ : ℕ => ℂ) 2

/-- Literal reciprocal regularization of the complete native power-energy row. -/
def paperHurwitzResolvent (rho : ℂ) : PaperHurwitzHistory →L[ℂ] PaperHurwitzHistory :=
  paperConvergentDiagonal (fun k => (paperHurwitzRegularizer rho k : ℂ))
    (tendsto_paperHurwitzRegularizer_complex rho)

@[simp] theorem paperHurwitzResolvent_apply (rho : ℂ) (f : PaperHurwitzHistory) (k : ℕ) :
    paperHurwitzResolvent rho f k = (paperHurwitzRegularizer rho k : ℂ) * f k := rfl

theorem norm_paperHurwitzRegularizer_complex_le (rho : ℂ) (k : ℕ) :
    ‖(paperHurwitzRegularizer rho k : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (paperHurwitzRegularizer_pos rho k).le]
  exact paperHurwitzRegularizer_le_one rho k

/-- The same literal operator has the global contraction bound. -/
theorem paperHurwitzResolvent_eq_diagonal (rho : ℂ) :
    paperHurwitzResolvent rho = lpDiagonalCLM
      (fun k => (paperHurwitzRegularizer rho k : ℂ)) zero_le_one
      (norm_paperHurwitzRegularizer_complex_le rho) := by
  ext f k
  rfl

theorem norm_paperHurwitzResolvent_le (rho : ℂ) : ‖paperHurwitzResolvent rho‖ ≤ 1 := by
  rw [paperHurwitzResolvent_eq_diagonal]
  exact norm_lpDiagonalCLM_le _ _ _

theorem paperHurwitzResolvent_single (rho : ℂ) (k : ℕ) :
    paperHurwitzResolvent rho (lp.single 2 k (1 : ℂ)) =
      lp.single 2 k (paperHurwitzRegularizer rho k : ℂ) :=
  paperConvergentDiagonal_single _ _ _

/-- The unit fibre survives at norm one in every chamber. -/
theorem norm_paperHurwitzResolvent (rho : ℂ) : ‖paperHurwitzResolvent rho‖ = 1 := by
  apply le_antisymm (norm_paperHurwitzResolvent_le rho)
  have h := (paperHurwitzResolvent rho).le_opNorm (lp.single 2 0 (1 : ℂ))
  simpa only [paperHurwitzResolvent_single, paperHurwitzRegularizer_zero,
    Complex.ofReal_one, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one, mul_one] using h

/-- On the critical line, every power level has zero energy. -/
theorem paperHurwitzResolvent_of_wall {rho : ℂ} (hr : rho.re = 1 / 2) :
    paperHurwitzResolvent rho = 1 := by
  ext f k
  simp [paperHurwitzResolvent_apply, paperHurwitzRegularizer_of_wall hr]

/-- Exact compact quotient, retaining the entire depth history. -/
theorem paperHurwitzResolvent_sub_character_compact (rho : ℂ) :
    IsCompactOperator (paperHurwitzResolvent rho - paperHurwitzWallCharacter rho •
      (1 : PaperHurwitzHistory →L[ℂ] PaperHurwitzHistory)) :=
  paperConvergentDiagonal_sub_limit_compact _ _

/-- This resolvent is compact exactly away from the critical line. -/
theorem paperHurwitzResolvent_compact_iff (rho : ℂ) :
    IsCompactOperator (paperHurwitzResolvent rho) ↔ rho.re ≠ 1 / 2 := by
  rw [paperHurwitzResolvent, paperConvergentDiagonal_compact_iff]
  by_cases hr : rho.re = 1 / 2 <;> simp_all [paperHurwitzWallCharacter]

/-- The essential norm is one on the line and zero off it. -/
theorem paperHurwitzResolvent_compactIdealDistance (rho : ℂ) :
    compactIdealDistance (paperHurwitzResolvent rho) =
      if rho.re = 1 / 2 then 1 else 0 := by
  rw [paperHurwitzResolvent, paperConvergentDiagonal_compactIdealDistance]
  by_cases hr : rho.re = 1 / 2 <;> simp_all [paperHurwitzWallCharacter]

/-- Application of the proven paper compact-ideal weight to the literal native resolvent. -/
theorem paperHurwitzResolvent_traceCost (rho : ℂ) :
    compactOperatorTraceCost PaperHurwitzHistory (paperHurwitzResolvent rho) =
      if rho.re = 1 / 2 then ∞ else 0 := by
  rw [compactOperatorTraceCost_eq, paperHurwitzResolvent_compact_iff]
  by_cases hr : rho.re = 1 / 2 <;> simp [hr]

/-- Arbitrary compact corrections, including depth-mixing ones, preserve the paper cost. -/
theorem paperHurwitzResolvent_traceCost_add_compact (rho : ℂ)
    (K : compactOperatorStarAlgebra PaperHurwitzHistory) :
    compactOperatorTraceCost PaperHurwitzHistory (paperHurwitzResolvent rho + K.1) =
      if rho.re = 1 / 2 then ∞ else 0 := by
  rw [compactOperatorTraceCost_add_compact, paperHurwitzResolvent_traceCost]

/-- Two full histories agree modulo compact operators exactly when their wall statuses agree. -/
theorem paperHurwitzResolvent_compact_sub_iff (rho sigma : ℂ) :
    IsCompactOperator (paperHurwitzResolvent rho - paperHurwitzResolvent sigma) ↔
      (rho.re = 1 / 2 ↔ sigma.re = 1 / 2) := by
  rw [paperHurwitzResolvent, paperHurwitzResolvent, paperConvergentDiagonal_compact_sub_iff]
  by_cases hr : rho.re = 1 / 2 <;> by_cases hs : sigma.re = 1 / 2 <;>
    simp_all [paperHurwitzWallCharacter]

/-- The two compact-quotient classes are exactly one unit apart. -/
theorem paperHurwitzResolvent_compactIdealDistance_sub (rho sigma : ℂ) :
    compactIdealDistance (paperHurwitzResolvent rho - paperHurwitzResolvent sigma) =
      if (rho.re = 1 / 2 ↔ sigma.re = 1 / 2) then 0 else 1 := by
  rw [paperHurwitzResolvent, paperHurwitzResolvent,
    paperConvergentDiagonal_compactIdealDistance_sub]
  by_cases hr : rho.re = 1 / 2 <;> by_cases hs : sigma.re = 1 / 2 <;>
    simp_all [paperHurwitzWallCharacter]

end
end RHTower

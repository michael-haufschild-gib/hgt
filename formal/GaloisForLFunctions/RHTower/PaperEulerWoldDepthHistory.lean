import GaloisForLFunctions.HTGeometry.PaperConvergentDiagonal
import GaloisForLFunctions.RHTower.SourceHorizontalEulerWoldTransverseDefectBudgetReporter

/-!
# Source-only Euler--Wold depth histories

The endpoint third jet already defines a source quantity independently of the existence of any
Xi zero. Together with the two admitted Jordan components it defines the entire depth history
of a linear reporter. Its diagonal operator keeps every finite source clock, and its compact
quotient retains precisely the native cofinal character.
-/

namespace RHTower

noncomputable section
open Complex Filter Classical
open GaloisForLFunctions.HTGeometry
open scoped ENNReal Topology

/-- The three-channel reporter formed entirely from the native source quantities. -/
def paperEulerWoldDepthReporter (a b d : ℝ) (c : ℂ) (N : ℕ) : ℝ :=
  a * sourceHorizontalEulerWoldJordanConormalAdmission c N 0 +
    b * sourceHorizontalEulerWoldJordanConormalAdmission c N 1 +
      d * sourceHorizontalWoldBVKreinGhostEnergy c N

/-- On each actual Xi copy this is the existing reporter, at every finite clock. -/
theorem paperEulerWoldDepthReporter_eq_native (a b d : ℝ) (c : ℂ)
    (q : XiRightZeroCopy) (N : ℕ) :
    paperEulerWoldDepthReporter a b d c N =
      sourceHorizontalEulerWoldJordanConormalLinearReporter a b d c q N := by
  rw [paperEulerWoldDepthReporter, sourceHorizontalEulerWoldJordanConormalLinearReporter,
    sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse_eq_ghostEnergy]

/-- The source-only history has the native character without any divisor-existence premise. -/
theorem paperEulerWoldDepthReporter_tendsto (a b d : ℝ) (c : ℂ) :
    Tendsto (paperEulerWoldDepthReporter a b d c) atTop
      (𝓝 (sourceHorizontalEulerWoldJordanConormalCofinalCharacter a b d c)) := by
  have hneg := (tendsto_sourceHorizontalEulerWoldJordanNegativeMass.neg.mul_const
    (sourceHorizontalLiteralConormalShort c)).const_mul a
  have hpos := (tendsto_sourceHorizontalEulerWoldJordanPositiveMass.mul_const
    (sourceHorizontalLiteralConormalShort c)).const_mul b
  have hend := (tendsto_sourceHorizontalWoldBVGreenStokesEndpointThirdJet.const_mul
    (8 * Complex.normSq c)).const_mul d
  convert (hneg.add hpos).add hend using 1
  · funext N
    simp only [paperEulerWoldDepthReporter, sourceHorizontalEulerWoldJordanConormalAdmission,
      Matrix.cons_val_zero, Matrix.cons_val_one, sourceHorizontalWoldBVKreinGhostEnergy]
  · unfold sourceHorizontalEulerWoldJordanConormalCofinalCharacter
      sourceHorizontalLiteralConormalShort
    ring_nf

/-- Simultaneous record of all source depths as a bounded diagonal operator. -/
def paperEulerWoldHistoryOperator (a b d : ℝ) (c : ℂ) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  paperConvergentDiagonal (fun N => (paperEulerWoldDepthReporter a b d c N : ℂ))
    ((Complex.continuous_ofReal.tendsto _).comp (paperEulerWoldDepthReporter_tendsto a b d c))

/-- Every depth entry is the literal native source reporter, with no averaging. -/
theorem paperEulerWoldHistoryOperator_apply (a b d : ℝ) (c : ℂ)
    (f : lp (fun _ : ℕ => ℂ) 2) (N : ℕ) :
    paperEulerWoldHistoryOperator a b d c f N =
      (paperEulerWoldDepthReporter a b d c N : ℂ) * f N := rfl

/-- The full finite-depth correction to the cofinal character is compact. -/
theorem paperEulerWoldHistoryOperator_sub_character_compact (a b d : ℝ) (c : ℂ) :
    IsCompactOperator (paperEulerWoldHistoryOperator a b d c -
      (sourceHorizontalEulerWoldJordanConormalCofinalCharacter a b d c : ℂ) • 1 :
      lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) :=
  paperConvergentDiagonal_sub_limit_compact _ _

/-- Exact essential norm of the full depth history. -/
theorem paperEulerWoldHistoryOperator_compactIdealDistance (a b d : ℝ) (c : ℂ) :
    compactIdealDistance (paperEulerWoldHistoryOperator a b d c) =
      |sourceHorizontalEulerWoldJordanConormalCofinalCharacter a b d c| := by
  exact (paperConvergentDiagonal_compactIdealDistance _ _).trans
    (by rw [Complex.norm_real, Real.norm_eq_abs])

/-- Every compact correction, including mixing different depths, obeys the same sharp bound. -/
theorem paperEulerWoldHistoryOperator_character_le_sub_compact (a b d : ℝ) (c : ℂ)
    (K : compactOperatorStarAlgebra (lp (fun _ : ℕ => ℂ) 2)) :
    |sourceHorizontalEulerWoldJordanConormalCofinalCharacter a b d c| ≤
      ‖paperEulerWoldHistoryOperator a b d c - K.1‖ := by
  simpa only [paperEulerWoldHistoryOperator, Complex.norm_real, Real.norm_eq_abs] using
    paperConvergentDiagonal_limit_le_norm_sub_compact
      (fun N => (paperEulerWoldDepthReporter a b d c N : ℂ))
      ((Complex.continuous_ofReal.tendsto _).comp (paperEulerWoldDepthReporter_tendsto a b d c)) K

/-- Compact equivalence of any two source histories is equality of their cofinal characters. -/
theorem paperEulerWoldHistoryOperator_compact_sub_iff (a b d a' b' d' : ℝ) (c c' : ℂ) :
    IsCompactOperator (paperEulerWoldHistoryOperator a b d c -
      paperEulerWoldHistoryOperator a' b' d' c') ↔
    sourceHorizontalEulerWoldJordanConormalCofinalCharacter a b d c =
      sourceHorizontalEulerWoldJordanConormalCofinalCharacter a' b' d' c' := by
  rw [paperEulerWoldHistoryOperator, paperEulerWoldHistoryOperator,
    paperConvergentDiagonal_compact_sub_iff, Complex.ofReal_inj]

/-- The full quotient distance is the absolute difference of native source characters. -/
theorem paperEulerWoldHistoryOperator_compactIdealDistance_sub
    (a b d a' b' d' : ℝ) (c c' : ℂ) :
    compactIdealDistance (paperEulerWoldHistoryOperator a b d c -
      paperEulerWoldHistoryOperator a' b' d' c') =
    |sourceHorizontalEulerWoldJordanConormalCofinalCharacter a b d c -
      sourceHorizontalEulerWoldJordanConormalCofinalCharacter a' b' d' c'| := by
  rw [paperEulerWoldHistoryOperator, paperEulerWoldHistoryOperator,
    paperConvergentDiagonal_compactIdealDistance_sub, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]

end
end RHTower

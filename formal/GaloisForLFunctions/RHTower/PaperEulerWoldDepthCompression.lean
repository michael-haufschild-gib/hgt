import GaloisForLFunctions.RHTower.PaperEulerWoldCompactCharacter
import GaloisForLFunctions.HTGeometry.PaperConvergentDiagonalCompression

/-!
# Finite EWJ depth prefixes and exact norm exhaustion

Finite prefixes recover every source coordinate and converge strongly. All have zero paper
compact-ideal cost. They exhaust the history in operator norm exactly on the native blind plane
(or at the zero coefficient). The endpoint and transverse lanes retain their explicit gaps.
-/

namespace RHTower

noncomputable section
open Complex Filter Classical
open GaloisForLFunctions.HTGeometry
open scoped ENNReal Topology

/-- The finite observer keeps exactly the first `N` native reporter values. -/
theorem paperEulerWoldHistoryOperator_compression_apply (a b d : ℝ) (c : ℂ)
    (N : ℕ) (f : VecSeq ℂ) (n : ℕ) :
    paperCoordinateCompression (paperEulerWoldHistoryOperator a b d c) N f n =
      if n < N then (paperEulerWoldDepthReporter a b d c n : ℂ) * f n else 0 :=
  paperConvergentDiagonal_compression_apply _ _ _ _ _

/-- Every finite depth history has zero compact-ideal cost. -/
theorem paperEulerWoldHistoryOperator_compression_traceCost (a b d : ℝ) (c : ℂ) (N : ℕ) :
    compactOperatorTraceCost (VecSeq ℂ)
      (paperCoordinateCompression (paperEulerWoldHistoryOperator a b d c) N) = 0 :=
  compactOperatorTraceCost_paperCoordinateCompression _ N

/-- The exact finite histories converge strongly to the complete source history. -/
theorem paperEulerWoldHistoryOperator_compression_tendsto (a b d : ℝ) (c : ℂ)
    (f : VecSeq ℂ) :
    Tendsto (fun N => paperCoordinateCompression (paperEulerWoldHistoryOperator a b d c) N f)
      atTop (𝓝 (paperEulerWoldHistoryOperator a b d c f)) :=
  tendsto_paperCoordinateCompression _ f

/-- Every finite prefix remains at least the cofinal character away in operator norm. -/
theorem paperEulerWoldHistoryOperator_compression_gap (a b d : ℝ) (c : ℂ) (N : ℕ) :
    |sourceHorizontalEulerWoldJordanConormalCofinalCharacter a b d c| ≤
      ‖paperEulerWoldHistoryOperator a b d c -
        paperCoordinateCompression (paperEulerWoldHistoryOperator a b d c) N‖ :=
  paperEulerWoldHistoryOperator_character_le_sub_compact _ _ _ _
    ⟨_, isCompactOperator_paperCoordinateCompression _ N⟩

/-- Exact norm exhaustion is equivalent to the native blind-plane condition. -/
theorem paperEulerWoldHistoryOperator_norm_compression_tendsto_iff (a b d : ℝ) (c : ℂ) :
    Tendsto (fun N => ‖paperEulerWoldHistoryOperator a b d c -
      paperCoordinateCompression (paperEulerWoldHistoryOperator a b d c) (N + 1)‖)
      atTop (𝓝 0) ↔ c = 0 ∨ -a + b + 2*d = 0 := by
  rw [paperEulerWoldHistoryOperator, paperConvergentDiagonal_norm_compression_tendsto_iff,
    Complex.ofReal_eq_zero, paperEulerWold_character_eq_zero_iff]

/-- The compensated budgeted lane does admit norm exhaustion by its actual finite prefixes. -/
theorem paperEulerWoldHistoryOperator_budgeted_norm_compression_tendsto (c : ℂ) :
    Tendsto (fun N => ‖paperEulerWoldHistoryOperator 1 (-1) 1 c -
      paperCoordinateCompression (paperEulerWoldHistoryOperator 1 (-1) 1 c) (N + 1)‖)
      atTop (𝓝 0) :=
  (paperEulerWoldHistoryOperator_norm_compression_tendsto_iff _ _ _ _).mpr
    (Or.inr (by ring))

/-- The endpoint's entire orbit quantum remains beyond every finite prefix. -/
theorem paperEulerWoldHistoryOperator_endpoint_compression_gap (c : ℂ) (N : ℕ) :
    (16 / 3 : ℝ) * Complex.normSq c ≤
      ‖paperEulerWoldHistoryOperator 0 0 1 c -
        paperCoordinateCompression (paperEulerWoldHistoryOperator 0 0 1 c) N‖ := by
  rw [← paperEulerWoldHistoryOperator_endpoint_gap]
  exact compactIdealDistance_le _ _ (isCompactOperator_paperCoordinateCompression _ N)

/-- Even the source-budgeted transverse lane retains half the source budget beyond every prefix. -/
theorem paperEulerWoldHistoryOperator_transverse_compression_gap (c : ℂ) (N : ℕ) :
    sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c / 2 ≤
      ‖paperEulerWoldHistoryOperator (-1) (-1) (routePPrimitiveBaseCauchyCubicTraceBudget / 4) c -
        paperCoordinateCompression
          (paperEulerWoldHistoryOperator (-1) (-1) (routePPrimitiveBaseCauchyCubicTraceBudget / 4) c)
          N‖ := by
  rw [← paperEulerWoldHistoryOperator_transverse_gap]
  exact compactIdealDistance_le _ _ (isCompactOperator_paperCoordinateCompression _ N)

end
end RHTower

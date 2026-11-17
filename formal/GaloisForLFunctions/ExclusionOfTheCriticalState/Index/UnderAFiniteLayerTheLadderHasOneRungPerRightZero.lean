import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheCriticalStatesFormAnOrthogonalLadder
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.FiniteLayerKreinStructureAndRigidity

/-!
# Under a finite layer the critical ladder has one rung per right zero

A critical ladder is a `W₈`-orthogonal family of confined null vectors (`IsCriticalLadder`). Under a
finite layer such a family has at most as many members as there are zeros of `ζ` right of the line
(`card_orthogonalNullVectors_le_rightZeros_of_finiteOffLine`: evaluation on the upper left zeros is
injective on its real span), and the critical state starts a ladder with one rung for each of them
(`exists_criticalLadder`). Hence (`criticalLadder_iff_rightZeros`): a ladder of length `k + 1` starting
at the critical state exists iff at least `k + 1` zeros lie right of the line. The critical ratios,
each counted with the dimension of its orthogonal null space, are exactly as many as the right zeros.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- Under a finite layer a critical ladder has at most one rung per right zero. -/
theorem IsCriticalLadder.length_le_rightZeros {k : ℕ} {R : Fin (k + 1) → ℝ}
    {Φ : Fin (k + 1) → ℝ → ℝ} (hL : IsCriticalLadder k R Φ) (hfin : BacklundConverse.FiniteOffLine) :
    ((k + 1 : ℕ) : ℕ∞) ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard :=
  (card_orthogonalNullVectors_le_rightZeros_of_finiteOffLine hL.pos hL.null hL.orth hfin).2

/-- **One rung per right zero.** Under a finite layer, the critical state starts a critical ladder of
length `k + 1` iff at least `k + 1` zeros of `ζ` lie right of the critical line. -/
theorem criticalLadder_iff_rightZeros {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hfin : BacklundConverse.FiniteOffLine) (k : ℕ) :
    (∃ (R : Fin (k + 1) → ℝ) (Φ : Fin (k + 1) → ℝ → ℝ),
        IsCriticalLadder k R Φ ∧ R 0 = W₀ ∧ Φ 0 = F) ↔
      ((k + 1 : ℕ) : ℕ∞) ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard :=
  ⟨fun ⟨_, _, hL, _, _⟩ => hL.length_le_rightZeros hfin, exists_criticalLadder hW ht hF k⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState

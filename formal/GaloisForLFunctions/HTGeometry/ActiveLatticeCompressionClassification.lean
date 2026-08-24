import GaloisForLFunctions.HTGeometry.ActiveLatticeAnnihilatorDimension
import GaloisForLFunctions.HTGeometry.PhaseRankFromAutonomousEquation
import GaloisForLFunctions.HTGeometry.AutonomousMinimalOrderBudget

/-!
# Active-lattice compression classification

This module turns the cardinal-valued active lattice rank into its canonical finite natural rank.
The stabilizer tangent dimension is exactly its codimension. Whenever a same-rank autonomous
relation is available, the existing phase-rank lower bound makes that relation minimal; saved
differential order is then equivalent to a positive-dimensional phase stabilizer.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-- Natural-number rank of the active character lattice. -/
def activeLatticeNatRank (F : (d → ℂ) → ℂ) : ℕ :=
  Module.finrank ℂ
    (Submodule.span ℂ (intCharacterToComplex '' activeSupport F))

omit [DecidableEq d] in
theorem natCast_activeLatticeNatRank (F : (d → ℂ) → ℂ) :
    (activeLatticeNatRank F : Cardinal) = Module.rank ℤ (activeLattice F) := by
  exact finrank_span_intCharacterToComplex (activeSupport F)

theorem finrank_characterAnnihilator_add_activeLatticeNatRank
    (F : (d → ℂ) → ℂ) :
    Module.finrank ℂ (characterAnnihilator (activeSupport F)) +
        activeLatticeNatRank F = Fintype.card d := by
  exact finrank_characterAnnihilator_add_finrank_span (activeSupport F)

theorem activeLatticeNatRank_lt_card_iff_stabilizer_pos
    (F : (d → ℂ) → ℂ) :
    activeLatticeNatRank F < Fintype.card d ↔
      0 < Module.finrank ℂ (characterAnnihilator (activeSupport F)) := by
  have h := finrank_characterAnnihilator_add_activeLatticeNatRank F
  omega

theorem autonomousMinimalOrder_eq_activeLatticeNatRank_of_relation
    {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ))
    (hex : ∃ P : Polynomial (MvPolynomial (Fin (activeLatticeNatRank F)) ℂ),
      P ≠ 0 ∧ RealAutonomousAnnihilator
        (phaseFunction omega F) (activeLatticeNatRank F) P) :
    autonomousMinimalOrder (phaseFunction omega F) = activeLatticeNatRank F := by
  apply le_antisymm (autonomousMinimalOrder_le hex)
  have hrel := exists_realAutonomousAnnihilator_autonomousMinimalOrder hex
  have hrank := rank_activeLattice_le_of_exists_realAutonomousAnnihilator
    hρ hindep hF hrel
  rw [← natCast_activeLatticeNatRank F] at hrank
  exact Nat.cast_le.mp hrank

theorem autonomousMinimalOrder_lt_card_iff_stabilizer_pos_of_exact
    {omega : d → ℝ} {F : (d → ℂ) → ℂ}
    (hexact : autonomousMinimalOrder (phaseFunction omega F) = activeLatticeNatRank F) :
    autonomousMinimalOrder (phaseFunction omega F) < Fintype.card d ↔
      0 < Module.finrank ℂ (characterAnnihilator (activeSupport F)) := by
  rw [hexact]
  exact activeLatticeNatRank_lt_card_iff_stabilizer_pos F

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.RHTower.XiWardEdgeGramSharpLaws

/-!
# Xi Ward edge-energy phase quantization

The sharp budget criterion and the independent doubled Gram gap combine into an exact
two-phase classification: zero energy is precisely RH, while energy above `8π` is precisely
non-RH.
-/

open Real

namespace RHTower

noncomputable section

/-- The continued Xi Ward edge quadratic energy vanishes exactly in the RH phase. -/
theorem riemannHypothesis_iff_xiWardEdgeQuadEnergy_eq_zero :
    RiemannHypothesis ↔ xiWardEdgeQuadEnergy = 0 := by
  constructor
  · intro hRH
    have hle :=
      (riemannHypothesis_iff_continuedXiWardEdgeQuadEnergyLaw_sharp
        (c := 0) (le_refl 0) (by positivity : (0 : ℝ) ≤ 8 * π)).1 hRH
    unfold ContinuedXiWardEdgeQuadEnergyLaw at hle
    rw [ENNReal.ofReal_zero] at hle
    exact le_antisymm hle bot_le
  · intro hzero
    apply
      (riemannHypothesis_iff_continuedXiWardEdgeQuadEnergyLaw_sharp
        (c := 0) (le_refl 0) (by positivity : (0 : ℝ) ≤ 8 * π)).2
    unfold ContinuedXiWardEdgeQuadEnergyLaw
    change xiWardEdgeQuadEnergy ≤ ENNReal.ofReal 0
    rw [hzero, ENNReal.ofReal_zero]

/-- The strict phase above the doubled Gram threshold is exactly failure of RH. -/
theorem not_riemannHypothesis_iff_eightPi_lt_xiWardEdgeQuadEnergy :
    ¬ RiemannHypothesis ↔
      ENNReal.ofReal (8 * π) < xiWardEdgeQuadEnergy := by
  constructor
  · intro hnotRH
    rcases xiWardEdgeQuadEnergy_eq_zero_or_eightPi_lt with hzero | hhigh
    · exact False.elim
        (hnotRH (riemannHypothesis_iff_xiWardEdgeQuadEnergy_eq_zero.2 hzero))
    · exact hhigh
  · intro hhigh hRH
    have hzero := riemannHypothesis_iff_xiWardEdgeQuadEnergy_eq_zero.1 hRH
    rw [hzero] at hhigh
    exact (not_lt_of_ge bot_le) hhigh

/-- **Xi Ward edge-energy phase-quantization law.**  Every arithmetic state belongs to exactly
one labeled energy phase: RH at zero, or non-RH strictly above `8π`. -/
theorem xiWardEdgeQuadEnergy_arithmeticPhaseClassification :
    (RiemannHypothesis ∧ xiWardEdgeQuadEnergy = 0) ∨
      (¬ RiemannHypothesis ∧
        ENNReal.ofReal (8 * π) < xiWardEdgeQuadEnergy) := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl
      ⟨hRH, riemannHypothesis_iff_xiWardEdgeQuadEnergy_eq_zero.1 hRH⟩
  · exact Or.inr
      ⟨hRH, not_riemannHypothesis_iff_eightPi_lt_xiWardEdgeQuadEnergy.1 hRH⟩

end

end RHTower

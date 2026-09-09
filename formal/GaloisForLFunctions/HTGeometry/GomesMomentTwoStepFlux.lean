import GaloisForLFunctions.HTGeometry.GomesJacobiTwoStepFlux
import GaloisForLFunctions.HTGeometry.GomesArcsineFrameGeometry
import GaloisForLFunctions.HTGeometry.GomesGammaFrameGeometry
import GaloisForLFunctions.HTGeometry.GomesCompletedFockFrameGeometry

/-!
# Strict flux for actual moment systems

Application of the joint-observation Gram mechanism developed from
https://arxiv.org/abs/2509.25276 and frame geometry from
https://arxiv.org/abs/2404.10461. Arcsine moments, every positive Gamma shape,
and arbitrary completed free-Fock matrix data all have strictly positive
complex two-step flux precisely in the open upper half-plane. All recurrence
coupling signs are proved internally from the existing moment constructions.
-/

open scoped Matrix ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- Two consecutive complex steps with the actual orthogonal-moment recurrence coefficients. -/
def gomesMomentTwoStep (s : ℕ → ℝ) (n : ℕ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  gomesJacobiComplexStep (recurDiag s (n+1)) (recurOff s (n+1)) z *
    gomesJacobiComplexStep (recurDiag s n) (recurOff s n) z

/-- The actual Arcsine two-step transfer has strictly positive flux exactly in the open upper half-plane. -/
theorem gomesArcsineFrame_twoStep_flux_posDef_iff (n : ℕ) (z : ℂ) :
    ((gomesMomentTwoStep normalizedCentralBinom n z)ᴴ * gomesJacobiFlux * gomesMomentTwoStep normalizedCentralBinom n z -
      (recurOff normalizedCentralBinom (n+1)*recurOff normalizedCentralBinom n : ℂ) • gomesJacobiFlux).PosDef ↔ 0 < z.im := by
  rw [gomesMomentTwoStep,gomesJacobiTwoStep_flux_posDef_iff]
  constructor
  · exact fun h => h.1
  · intro hi
    exact ⟨hi,(gomesArcsineFrame_recurOff_pos n).ne',
      gomesArcsineFrame_recurOff_pos (n+1)⟩

/-- The actual Gamma two-step transfer has strictly positive flux exactly in the open upper half-plane. -/
theorem gomesGammaFrame_twoStep_flux_posDef_iff (r : ℝ) (n : ℕ) (z : ℂ) :
    ((gomesMomentTwoStep (gammaShapeMoment (Real.exp r)) n z)ᴴ * gomesJacobiFlux * gomesMomentTwoStep (gammaShapeMoment (Real.exp r)) n z -
      (recurOff (gammaShapeMoment (Real.exp r)) (n+1)*recurOff (gammaShapeMoment (Real.exp r)) n : ℂ) • gomesJacobiFlux).PosDef ↔ 0 < z.im := by
  rw [gomesMomentTwoStep,gomesJacobiTwoStep_flux_posDef_iff]
  constructor
  · exact fun h => h.1
  · intro hi
    exact ⟨hi,(gomesGammaFrame_recurOff_pos r n).ne',
      gomesGammaFrame_recurOff_pos r (n+1)⟩

/-- The actual CompletedFock two-step transfer has strictly positive flux exactly in the open upper half-plane. -/
theorem gomesCompletedFockFrame_twoStep_flux_posDef_iff {d k : ℕ} (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (n : ℕ) (z : ℂ) :
    ((gomesMomentTwoStep (gomesCompletedFockMoment B) n z)ᴴ * gomesJacobiFlux * gomesMomentTwoStep (gomesCompletedFockMoment B) n z -
      (recurOff (gomesCompletedFockMoment B) (n+1)*recurOff (gomesCompletedFockMoment B) n : ℂ) • gomesJacobiFlux).PosDef ↔ 0 < z.im := by
  rw [gomesMomentTwoStep,gomesJacobiTwoStep_flux_posDef_iff]
  constructor
  · exact fun h => h.1
  · intro hi
    exact ⟨hi,(gomesCompletedFockFrame_recurOff_pos B n).ne',
      gomesCompletedFockFrame_recurOff_pos B (n+1)⟩

end GaloisForLFunctions.HTGeometry

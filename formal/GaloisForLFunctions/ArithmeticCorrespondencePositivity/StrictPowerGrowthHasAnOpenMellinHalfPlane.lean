import GaloisForLFunctions.ArithmeticCorrespondencePositivity.PowerAsymptoticsHaveNoNonrealBoundaryResidues
import GaloisForLFunctions.HTGeometry.StrictNaturalPowerGrowth

/-!
# Strict power growth determines the open Mellin half-plane

An exact bound at the boundary exponent is unnecessary. Around each
interior point, choose a smaller intermediate exponent and apply the
power-majorant argument on its half-plane.
-/

noncomputable section

open Complex Set

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open TransHorizonIncidenceMechanics

/-- Every strict interior Mellin majorant is summable under strict power growth. -/
theorem summable_mellin_majorant_of_strict_power_growth
    {f : ℕ → ℝ} (hf0 : f 0 = 0) {θ σ : ℝ}
    (hf : _root_.HTGeometry.StrictNaturalPowerGrowth f θ) (hgap : θ < σ) :
    Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-σ - 1) := by
  let δ := (σ - θ) / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [hgap]
  obtain ⟨C, hC, hb⟩ := hf δ hδ
  have hb' : ∀ N : ℕ, |f N| ≤ C * (N : ℝ) ^ (θ + δ) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [hf0, abs_zero]
      positivity
    · exact hb N hN
  exact summable_mellin_majorant_of_power_bound hf0 hb'
    (by dsimp only [δ]; linarith only [hgap])

/-- Strict power growth supplies holomorphy on the entire open half-plane. -/
theorem differentiableOn_complexMellinPairing_of_strict_power_growth
    {f : ℕ → ℝ} (hf0 : f 0 = 0) {θ : ℝ} (hθ : 0 ≤ θ)
    (hf : _root_.HTGeometry.StrictNaturalPowerGrowth f θ) :
    DifferentiableOn ℂ (complexMellinPairing f) {s : ℂ | θ < s.re} := by
  intro s hs
  change θ < s.re at hs
  let δ := (s.re - θ) / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [hs]
  obtain ⟨C, hC, hb⟩ := hf δ hδ
  have hb' : ∀ N : ℕ, |f N| ≤ C * (N : ℝ) ^ (θ + δ) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [hf0, abs_zero]
      positivity
    · exact hb N hN
  have hdiff := differentiableOn_complexMellinPairing_of_power_bound hf0
    (by linarith only [hθ, hδ] : 0 ≤ θ + δ) hb'
  have hmem : s ∈ {z : ℂ | θ + δ < z.re} := by
    change θ + δ < s.re
    dsimp only [δ]
    linarith only [hs]
  exact (hdiff.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)).differentiableWithinAt

end GaloisForLFunctions.ArithmeticCorrespondencePositivity

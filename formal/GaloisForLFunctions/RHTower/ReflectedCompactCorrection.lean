import GaloisForLFunctions.RHTower.ReflectedCompactPole
import GaloisForLFunctions.RHTower.ReflectedCompactComplementStability
import GaloisForLFunctions.RHTower.SmoothAFEFullReflectedAFE

open Complex Filter Topology Set Metric
noncomputable section
namespace RHTower
open SteinhausModel

/-- The complete original correction, including reciprocal phases and the pole. -/
def steinhausCompactReflectedCorrection (z : ℂ) (N : ℝ) (ω : Omega) : ℂ :=
  steinhausCompactReflectedComplement z N ω - reflectedCompactPole z N

/-- The complete correction is holomorphic throughout the open unit strip. -/
theorem differentiableOn_steinhausCompactReflectedCorrection {N : ℝ} (hN : 0 < N)
    (ω : Omega) :
    DifferentiableOn ℂ (fun z => steinhausCompactReflectedCorrection z N ω)
      {z : ℂ | 0 < z.re ∧ z.re < 1} :=
  (differentiableOn_steinhausCompactReflectedComplement hN ω).sub
    (differentiableOn_reflectedCompactPole hN)

/-- One compact conductor bound controls the entire correction, uniformly in phase. -/
theorem exists_norm_steinhausCompactReflectedCorrection_le_disc
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 < c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ tau ∈ Icc (N : ℝ) (2 * N),
      ∀ s ∈ closedBall c r, ∀ ω : Omega,
        ‖steinhausCompactReflectedCorrection (s + (tau : ℂ) * I) N ω‖ ≤ C := by
  obtain ⟨C, hC, hcomp⟩ := exists_norm_steinhausCompactReflectedComplement_le_disc c hr hc0 hc1
  obtain ⟨D, hD, hpole⟩ := exists_norm_reflectedCompactPole_le_disc c hr hc0.le hc1
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  filter_upwards [hcomp, hpole] with N hcompN hpoleN
  intro tau htau s hs ω
  exact (norm_sub_le _ _).trans (add_le_add (hcompN tau htau s hs ω) (hpoleN tau htau s hs))

/-- The unchanged pole cancels from phase differences, so one prefix controls
the complete correction uniformly on the compact conductor family. -/
theorem exists_steinhausCompactReflectedCorrection_character_tolerance
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 < c.re - r) (hc1 : c.re + r < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ tau ∈ Icc (N : ℝ) (2 * N), ∀ s ∈ closedBall c r, ∀ ω η : Omega,
        η ∈ steinhausCharacterCell B ω δ →
          ‖steinhausCompactReflectedCorrection (s + (tau : ℂ) * I) N η -
            steinhausCompactReflectedCorrection (s + (tau : ℂ) * I) N ω‖ < ε := by
  obtain ⟨B, hB, δ, hδ, hcell⟩ :=
    exists_steinhausCompactReflectedComplement_character_tolerance c hr hc0 hc1 hε
  refine ⟨B, hB, δ, hδ, ?_⟩
  filter_upwards [hcell] with N hcellN
  intro tau htau s hs ω η hη
  have heq : steinhausCompactReflectedCorrection (s + (tau : ℂ) * I) N η -
      steinhausCompactReflectedCorrection (s + (tau : ℂ) * I) N ω =
      steinhausCompactReflectedComplement (s + (tau : ℂ) * I) N η -
      steinhausCompactReflectedComplement (s + (tau : ℂ) * I) N ω := by
    unfold steinhausCompactReflectedCorrection
    ring
  rw [heq]
  exact hcellN tau htau s hs ω η hη

/-- Exact assembly into the original full reflected AFE; no correction is omitted. -/
theorem steinhausFullReflectedAFE_eq_primal_add_compactCorrection {d : ℝ}
    (hd : 0 < d) (hdhalf : d < 1 / 2) (tau : ℝ) {N : ℕ} (hN : 0 < N) (ω : Omega) :
    steinhausFullReflectedAFE d tau N ω = steinhausFullReflectedPrimalCarrier d tau N ω +
      steinhausCompactReflectedCorrection (rightDisplacedLinePt d tau) N ω := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold steinhausFullReflectedAFE steinhausCompactReflectedCorrection
  rw [steinhausFullReflectedComplement_eq_compact hd hdhalf hNR,
    reflectedCompactPole_rightDisplacedLinePt]
  ring

end RHTower

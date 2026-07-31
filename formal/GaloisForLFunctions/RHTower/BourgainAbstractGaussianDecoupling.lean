/-
# Abstract perturbative Gaussian decoupling

This module isolates the analytic core of the exact osculating argument.
Any two finite point families that are coordinatewise close, at the natural
parabola scales, to two independent sampled parabolas satisfy the sharp
bilinear sixth-moment Gaussian estimate.  The theorem is independent of the
particular curve or coordinate map used to establish the perturbation.
-/
import GaloisForLFunctions.RHTower.BourgainIndependentParabolaNearEnergy

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Natural frequency scales for two independent sampled parabolas. -/
def bourgainIndependentParabolaNaturalScale
    (H : ℕ) : BourgainPhaseSpace :=
  ![(H : ℝ), (H : ℝ) ^ (2 : ℕ),
    (H : ℝ), (H : ℝ) ^ (2 : ℕ)]

/-- Product coefficient on a pair of triple convolutions. -/
def bourgainPairedTripleWeight
    {H : ℕ} (c₁ c₂ : Fin H → ℂ)
    (hk : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : ℂ :=
  bourgainTripleWeight c₁ hk.1 * bourgainTripleWeight c₂ hk.2

@[simp] theorem norm_bourgainPairedTripleWeight
    {H : ℕ} (c₁ c₂ : Fin H → ℂ)
    (hk : (Fin 3 → Fin H) × (Fin 3 → Fin H)) :
    ‖bourgainPairedTripleWeight c₁ c₂ hk‖ =
      ‖bourgainTripleWeight c₁ hk.1‖ *
        ‖bourgainTripleWeight c₂ hk.2‖ := by
  simp [bourgainPairedTripleWeight]

/-- A perturbation radius at most `1/24` leaves every natural parabola scale
large enough to detect its corresponding integer moment. -/
theorem bourgainPerturbedNaturalScale_detects_moments
    {H : ℕ} (hH : 0 < H) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 24) :
    let Y :=
      bourgainPerturbedSpacingScale (6 * δ)
        (bourgainIndependentParabolaNaturalScale H)
    (H : ℝ) ≤ 2 * Y 0 ∧
      (H : ℝ) ^ (2 : ℕ) ≤ 2 * Y 1 ∧
      (H : ℝ) ≤ 2 * Y 2 ∧
      (H : ℝ) ^ (2 : ℕ) ≤ 2 * Y 3 := by
  dsimp only
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hden : 0 < 1 + 4 * (6 * δ) := by positivity
  have hden_le : 1 + 4 * (6 * δ) ≤ 2 := by linarith
  have hdetect {A : ℝ} (hA : 0 < A) :
      A ≤ 2 * (A / (1 + 4 * (6 * δ))) := by
    rw [show
      2 * (A / (1 + 4 * (6 * δ))) =
        (2 * A) / (1 + 4 * (6 * δ)) by ring]
    apply (le_div_iff₀ hden).2
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [bourgainPerturbedSpacingScale,
      bourgainIndependentParabolaNaturalScale, Matrix.cons_val] using
      hdetect hHr
  · simpa [bourgainPerturbedSpacingScale,
      bourgainIndependentParabolaNaturalScale, Matrix.cons_val] using
      hdetect (sq_pos_of_pos hHr)
  · simpa [bourgainPerturbedSpacingScale,
      bourgainIndependentParabolaNaturalScale, Matrix.cons_val] using
      hdetect hHr
  · simpa [bourgainPerturbedSpacingScale,
      bourgainIndependentParabolaNaturalScale, Matrix.cons_val] using
      hdetect (sq_pos_of_pos hHr)

/-- **Abstract sharp perturbative Gaussian decoupling.**

If two finite point families are scaled perturbations of the two independent
parabola samples by at most `1/24`, their paired triple cloud has only a
subpower loss over the two coefficient `ℓ²` masses. -/
theorem integral_bourgainPairedTripleCloud_gaussian_subpower_of_perturbation
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (_hH : 0 < H)
        (p₁ p₂ : Fin H → BourgainPhaseSpace) {δ : ℝ},
      0 ≤ δ →
      δ ≤ 1 / 24 →
      (∀ (n : Fin H) (j : Fin 4),
        |bourgainIndependentParabolaNaturalScale H j *
          (p₁ n j - bourgainLeftParabolaSample (H : ℝ) n j)| ≤ δ) →
      (∀ (n : Fin H) (j : Fin 4),
        |bourgainIndependentParabolaNaturalScale H j *
          (p₂ n j - bourgainRightParabolaSample (H : ℝ) n j)| ≤ δ) →
      ∀ (c₁ c₂ : Fin H → ℂ),
        (∫ x : BourgainPhaseSpace,
          bourgainRealGaussianL2Integrand
            (bourgainIndependentParabolaNaturalScale H)
            (bourgainPairedTripleCloud p₁ p₂)
            (bourgainPairedTripleWeight c₁ c₂) x) ≤
          C * (H : ℝ) ^ ε *
            (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
            (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  obtain ⟨C₀, hC₀, hindependent⟩ :=
    bourgainIndependentParabola_nearEnergy_subpower hε
  refine ⟨331776 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro H hH p₁ p₂ δ hδ0 hsmall hleft hright c₁ c₂
  let X := bourgainIndependentParabolaNaturalScale H
  obtain ⟨hY0, hY1, hY2, hY3⟩ :=
    bourgainPerturbedNaturalScale_detects_moments hH hδ0 hsmall
  calc
    (∫ x : BourgainPhaseSpace,
        bourgainRealGaussianL2Integrand X
          (bourgainPairedTripleCloud p₁ p₂)
          (bourgainPairedTripleWeight c₁ c₂) x)
        ≤ 331776 *
          bourgainWeightedScaledNearEnergy
            (bourgainPerturbedSpacingScale (6 * δ) X)
            (bourgainPairedTripleCloud
              (bourgainLeftParabolaSample (H : ℝ))
              (bourgainRightParabolaSample (H : ℝ)))
            (fun hk => ‖bourgainPairedTripleWeight c₁ c₂ hk‖) :=
      integral_bourgainPairedTripleCloud_gaussian_le_perturbed
        hδ0 X p₁ (bourgainLeftParabolaSample (H : ℝ))
        p₂ (bourgainRightParabolaSample (H : ℝ))
        (bourgainPairedTripleWeight c₁ c₂) hleft hright
    _ = 331776 *
          bourgainWeightedScaledNearEnergy
            (bourgainPerturbedSpacingScale (6 * δ) X)
            (bourgainPairedTripleCloud
              (bourgainLeftParabolaSample (H : ℝ))
              (bourgainRightParabolaSample (H : ℝ)))
            (fun hk =>
              ‖bourgainTripleWeight c₁ hk.1‖ *
                ‖bourgainTripleWeight c₂ hk.2‖) := by
      congr 2
      funext hk
      exact norm_bourgainPairedTripleWeight c₁ c₂ hk
    _ ≤ 331776 *
        (C₀ * (H : ℝ) ^ ε *
          (∑ h : Fin 3 → Fin H,
            ‖bourgainTripleWeight c₁ h‖ ^ (2 : ℕ)) *
          (∑ k : Fin 3 → Fin H,
            ‖bourgainTripleWeight c₂ k‖ ^ (2 : ℕ))) := by
      gcongr
      exact hindependent H hH (H : ℝ)
        (by exact_mod_cast hH) _
        hY0 hY1 hY2 hY3
        (fun h => ‖bourgainTripleWeight c₁ h‖)
        (fun k => ‖bourgainTripleWeight c₂ k‖)
        (fun h => norm_nonneg _) (fun k => norm_nonneg _)
    _ = (331776 * C₀) * (H : ℝ) ^ ε *
          (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
          (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
      rw [sum_norm_bourgainTripleWeight_sq,
        sum_norm_bourgainTripleWeight_sq]
      ring

end

end RHTower

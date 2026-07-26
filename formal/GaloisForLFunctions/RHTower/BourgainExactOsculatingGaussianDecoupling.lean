/-
# Perturbation-stable exact-curve Gaussian decoupling

This is the local analytic replacement for additive Taylor comparison.
At one separated osculating scale, an explicit small-frequency condition
transfers the exact paired square-root cloud to two independent parabola
clouds.  Gaussian localization and the arithmetic fiber theorem then give
the sharp `H^ε` coefficient bound with no additive `ℓ¹` term.
-/
import GaloisForLFunctions.RHTower.BourgainOsculatingFrequencyPerturbation

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Natural frequency scales for the two independent sampled parabolas. -/
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
  simp [bourgainPairedTripleWeight, norm_mul]

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
  constructor
  · unfold bourgainPerturbedSpacingScale
      bourgainIndependentParabolaNaturalScale
    simp only [Matrix.cons_val_zero]
    rw [show
      2 * ((H : ℝ) / (1 + 4 * (6 * δ))) =
        (2 * (H : ℝ)) / (1 + 4 * (6 * δ)) by ring]
    apply (le_div_iff₀ hden).2
    nlinarith
  constructor
  · unfold bourgainPerturbedSpacingScale
      bourgainIndependentParabolaNaturalScale
    simp only [Matrix.cons_val_one]
    rw [show
      2 * ((H : ℝ) ^ (2 : ℕ) / (1 + 4 * (6 * δ))) =
        (2 * (H : ℝ) ^ (2 : ℕ)) / (1 + 4 * (6 * δ)) by ring]
    apply (le_div_iff₀ hden).2
    nlinarith [sq_pos_of_pos hHr]
  constructor
  · unfold bourgainPerturbedSpacingScale
      bourgainIndependentParabolaNaturalScale
    simp only [Matrix.cons_val_two]
    rw [show
      2 * ((H : ℝ) / (1 + 4 * (6 * δ))) =
        (2 * (H : ℝ)) / (1 + 4 * (6 * δ)) by ring]
    apply (le_div_iff₀ hden).2
    nlinarith
  · unfold bourgainPerturbedSpacingScale
      bourgainIndependentParabolaNaturalScale
    simp only [Matrix.cons_val_three]
    rw [show
      2 * ((H : ℝ) ^ (2 : ℕ) / (1 + 4 * (6 * δ))) =
        (2 * (H : ℝ) ^ (2 : ℕ)) / (1 + 4 * (6 * δ)) by ring]
    apply (le_div_iff₀ hden).2
    nlinarith [sq_pos_of_pos hHr]

/-- Sharp Gaussian decoupling for the exact paired osculating frequencies.
All Taylor dependence is confined to the explicit condition `δ ≤ 1/24`. -/
theorem integral_bourgainExactOsculatingPaired_gaussian_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ), 0 < H →
      ∀ {D a b : ℝ}, 0 < D → 0 < a → a < b →
      let hscale : (H : ℝ) / D ≠ 0 :=
        div_ne_zero (Nat.cast_ne_zero.mpr ‹0 < H›.ne') ‹0 < D›.ne'
      let E :=
        bourgainScaledOsculatingPhaseContinuousLinearEquiv
          hscale ‹0 < a› ‹a < b›
      let X := bourgainIndependentParabolaNaturalScale H
      let δ :=
        bourgainOsculatingFrequencyPerturbationSize X
          ‖(E.symm :
            BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖
          a b ((H : ℝ) / D)
      δ ≤ 1 / 24 →
      ∀ (c₁ c₂ : Fin H → ℂ),
        (∫ x : BourgainPhaseSpace,
          bourgainRealGaussianL2Integrand X
            (bourgainPairedTripleCloud
              (bourgainExactLeftOsculatingFrequency
                hscale ‹0 < a› ‹a < b› D)
              (bourgainExactRightOsculatingFrequency
                hscale ‹0 < a› ‹a < b› D))
            (bourgainPairedTripleWeight c₁ c₂) x) ≤
          C * (H : ℝ) ^ ε *
            (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
            (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  obtain ⟨C₀, hC₀, hindependent⟩ :=
    bourgainIndependentParabola_nearEnergy_subpower hε
  refine ⟨331776 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro H hH D a b hD ha hab
  dsimp only
  intro hsmall c₁ c₂
  let hscale : (H : ℝ) / D ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
  let E :=
    bourgainScaledOsculatingPhaseContinuousLinearEquiv hscale ha hab
  let X := bourgainIndependentParabolaNaturalScale H
  let δ :=
    bourgainOsculatingFrequencyPerturbationSize X
      ‖(E.symm :
        BourgainPhaseSpace →L[ℝ] BourgainPhaseSpace)‖
      a b ((H : ℝ) / D)
  have hratio : 0 < (H : ℝ) / D := by positivity
  have hδ0 : 0 ≤ δ := by
    exact bourgainOsculatingFrequencyPerturbationSize_nonneg
      X (norm_nonneg _) ha (ha.trans hab) hratio.le
  have hsample :
      ∀ n : Fin H, (bourgainIndex n : ℝ) / D ≤ (H : ℝ) / D := by
    intro n
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast bourgainIndex_le n) hD.le
  have hperturb :=
    bourgainExactOsculatingFrequencies_scaledPerturbation
      hH hD ha hab hratio hsample X
  change
    (∀ n j,
      |X j *
        (bourgainExactLeftOsculatingFrequency hscale ha hab D n j -
          bourgainLeftParabolaSample (H : ℝ) n j)| ≤ δ) ∧
    (∀ n j,
      |X j *
        (bourgainExactRightOsculatingFrequency hscale ha hab D n j -
          bourgainRightParabolaSample (H : ℝ) n j)| ≤ δ)
      at hperturb
  obtain ⟨hleft, hright⟩ := hperturb
  obtain ⟨hY0, hY1, hY2, hY3⟩ :=
    bourgainPerturbedNaturalScale_detects_moments hH hδ0 hsmall
  calc
    (∫ x : BourgainPhaseSpace,
        bourgainRealGaussianL2Integrand X
          (bourgainPairedTripleCloud
            (bourgainExactLeftOsculatingFrequency hscale ha hab D)
            (bourgainExactRightOsculatingFrequency hscale ha hab D))
          (bourgainPairedTripleWeight c₁ c₂) x)
        ≤ 331776 *
          bourgainWeightedScaledNearEnergy
            (bourgainPerturbedSpacingScale (6 * δ) X)
            (bourgainPairedTripleCloud
              (bourgainLeftParabolaSample (H : ℝ))
              (bourgainRightParabolaSample (H : ℝ)))
            (fun hk =>
              ‖bourgainPairedTripleWeight c₁ c₂ hk‖) :=
      integral_bourgainPairedTripleCloud_gaussian_le_perturbed
        hδ0 X
        (bourgainExactLeftOsculatingFrequency hscale ha hab D)
        (bourgainLeftParabolaSample (H : ℝ))
        (bourgainExactRightOsculatingFrequency hscale ha hab D)
        (bourgainRightParabolaSample (H : ℝ))
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

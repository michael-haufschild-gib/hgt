/-
# Perturbation-stable exact-curve Gaussian decoupling

This is the local analytic replacement for additive Taylor comparison.
At one separated osculating scale, an explicit small-frequency condition
transfers the exact paired square-root cloud to two independent parabola
clouds.  Gaussian localization and the arithmetic fiber theorem then give
the sharp `H^ε` coefficient bound with no additive `ℓ¹` term.
-/
import GaloisForLFunctions.RHTower.BourgainOsculatingFrequencyPerturbation
import GaloisForLFunctions.RHTower.BourgainAbstractGaussianDecoupling

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Sharp Gaussian decoupling for the exact paired osculating frequencies.
All Taylor dependence is confined to the explicit condition `δ ≤ 1/24`. -/
theorem integral_bourgainExactOsculatingPaired_gaussian_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (hH : 0 < H),
      ∀ {D a b : ℝ} (hD : 0 < D) (ha : 0 < a) (hab : a < b),
      let hscale : (H : ℝ) / D ≠ 0 :=
        div_ne_zero (Nat.cast_ne_zero.mpr hH.ne') hD.ne'
      let E :=
        bourgainScaledOsculatingPhaseContinuousLinearEquiv
          hscale ha hab
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
                hscale ha hab D)
              (bourgainExactRightOsculatingFrequency
                hscale ha hab D))
            (bourgainPairedTripleWeight c₁ c₂) x) ≤
          C * (H : ℝ) ^ ε *
            (∑ n : Fin H, ‖c₁ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) *
            (∑ n : Fin H, ‖c₂ n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  obtain ⟨C, hC, habstract⟩ :=
    integral_bourgainPairedTripleCloud_gaussian_subpower_of_perturbation
      hε
  refine ⟨C, hC, ?_⟩
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
  exact habstract H hH
    (bourgainExactLeftOsculatingFrequency hscale ha hab D)
    (bourgainExactRightOsculatingFrequency hscale ha hab D)
    hδ0 hsmall hleft hright c₁ c₂

end

end RHTower

/-
# Perturbation stability for paired triple clouds

A bilinear sixth moment is the Gaussian `L²` norm of a frequency family
indexed by two triples.  This file lifts pointwise perturbation control for
both curve pieces to that paired cloud.  Six perturbed sample points produce
the explicit scale loss `1+24δ`.
-/
import GaloisForLFunctions.RHTower.BourgainTripleNearPerturbation

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Frequency cloud obtained by adding one triple from each point family. -/
def bourgainPairedTripleCloud
    {H : ℕ} (p q : Fin H → BourgainPhaseSpace)
    (hk : (Fin 3 → Fin H) × (Fin 3 → Fin H)) :
    BourgainPhaseSpace :=
  bourgainTripleCloud p hk.1 + bourgainTripleCloud q hk.2

/-- Two pointwise perturbations of size `δ` perturb the paired triple cloud
by at most `6δ` in every scaled coordinate. -/
theorem bourgainPairedTripleCloud_scaledPerturbation
    {H : ℕ} {δ : ℝ}
    {X : BourgainPhaseSpace}
    {p₁ q₁ p₂ q₂ : Fin H → BourgainPhaseSpace}
    (hperturb₁ :
      ∀ n j, |X j * (p₁ n j - q₁ n j)| ≤ δ)
    (hperturb₂ :
      ∀ n j, |X j * (p₂ n j - q₂ n j)| ≤ δ) :
    ∀ hk j,
      |X j *
        (bourgainPairedTripleCloud p₁ p₂ hk j -
          bourgainPairedTripleCloud q₁ q₂ hk j)| ≤ 6 * δ := by
  intro hk j
  have h₁ :=
    bourgainTripleCloud_scaledPerturbation hperturb₁ hk.1 j
  have h₂ :=
    bourgainTripleCloud_scaledPerturbation hperturb₂ hk.2 j
  have hdecomp :
      X j *
        (bourgainPairedTripleCloud p₁ p₂ hk j -
          bourgainPairedTripleCloud q₁ q₂ hk j) =
        X j *
            (bourgainTripleCloud p₁ hk.1 j -
              bourgainTripleCloud q₁ hk.1 j) +
          X j *
            (bourgainTripleCloud p₂ hk.2 j -
              bourgainTripleCloud q₂ hk.2 j) := by
    simp [bourgainPairedTripleCloud]
    ring
  rw [hdecomp]
  calc
    |X j *
          (bourgainTripleCloud p₁ hk.1 j -
            bourgainTripleCloud q₁ hk.1 j) +
        X j *
          (bourgainTripleCloud p₂ hk.2 j -
            bourgainTripleCloud q₂ hk.2 j)|
        ≤ |X j *
              (bourgainTripleCloud p₁ hk.1 j -
                bourgainTripleCloud q₁ hk.1 j)| +
            |X j *
              (bourgainTripleCloud p₂ hk.2 j -
                bourgainTripleCloud q₂ hk.2 j)| :=
      abs_add_le _ _
    _ ≤ 3 * δ + 3 * δ := add_le_add h₁ h₂
    _ = 6 * δ := by ring

/-- Near energy of an exact paired cloud is controlled by that of the paired
model after the explicit perturbative scale shrink. -/
theorem bourgainPairedTripleCloud_nearEnergy_perturbation_le
    {H : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (X : BourgainPhaseSpace)
    (p₁ q₁ p₂ q₂ : Fin H → BourgainPhaseSpace)
    (a : ((Fin 3 → Fin H) × (Fin 3 → Fin H)) → ℝ)
    (ha : ∀ hk, 0 ≤ a hk)
    (hperturb₁ :
      ∀ n j, |X j * (p₁ n j - q₁ n j)| ≤ δ)
    (hperturb₂ :
      ∀ n j, |X j * (p₂ n j - q₂ n j)| ≤ δ) :
    bourgainWeightedScaledNearEnergy X
        (bourgainPairedTripleCloud p₁ p₂) a ≤
      bourgainWeightedScaledNearEnergy
        (bourgainPerturbedSpacingScale (6 * δ) X)
        (bourgainPairedTripleCloud q₁ q₂) a := by
  apply bourgainWeightedScaledNearEnergy_perturbation_le
    (mul_nonneg (by norm_num) hδ) X
    (bourgainPairedTripleCloud p₁ p₂)
    (bourgainPairedTripleCloud q₁ q₂) a ha
  exact bourgainPairedTripleCloud_scaledPerturbation
    hperturb₁ hperturb₂

/-- Gaussian localization for a paired exact cloud, transferred to its
paired quadratic model without additive error. -/
theorem integral_bourgainPairedTripleCloud_gaussian_le_perturbed
    {H : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (X : BourgainPhaseSpace)
    (p₁ q₁ p₂ q₂ : Fin H → BourgainPhaseSpace)
    (b : ((Fin 3 → Fin H) × (Fin 3 → Fin H)) → ℂ)
    (hperturb₁ :
      ∀ n j, |X j * (p₁ n j - q₁ n j)| ≤ δ)
    (hperturb₂ :
      ∀ n j, |X j * (p₂ n j - q₂ n j)| ≤ δ) :
    (∫ x : BourgainPhaseSpace,
        bourgainRealGaussianL2Integrand X
          (bourgainPairedTripleCloud p₁ p₂) b x) ≤
      331776 *
        bourgainWeightedScaledNearEnergy
          (bourgainPerturbedSpacingScale (6 * δ) X)
          (bourgainPairedTripleCloud q₁ q₂)
          (fun hk => ‖b hk‖) := by
  calc
    _ ≤ 331776 *
        bourgainWeightedScaledNearEnergy X
          (bourgainPairedTripleCloud p₁ p₂)
          (fun hk => ‖b hk‖) :=
      integral_bourgainRealGaussianL2Integrand_le_scaledNear
        X (bourgainPairedTripleCloud p₁ p₂) b
    _ ≤ _ := by
      gcongr
      exact bourgainPairedTripleCloud_nearEnergy_perturbation_le
        hδ X p₁ q₁ p₂ q₂ (fun hk => ‖b hk‖)
        (fun hk => norm_nonneg _) hperturb₁ hperturb₂

end

end RHTower

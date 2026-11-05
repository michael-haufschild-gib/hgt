import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.EffectiveReadout
import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.LocalZetaCount

/-!
# Explicit weighted moment cameras on the ζ carrier

The actual ζ count supplies the carrier geometry. One pair of windows
then reads every complex weighting of bounded absolute Lorentzian mass,
with the explicit moment-camera height and polynomial isolation error.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

/-- Starting height for a ζ carrier with arbitrary coefficients of bounded absolute mass. -/
def zetaWeightedMomentCameraHeight (J : ℕ) (lam S M K' : ℝ) : ℝ :=
  max (zetaCameraCountHeight (lam + 1 / 2))
    (cameraMomentHeight J (lam + 1 / 2) lam (zetaCameraCountConstant (lam + 1 / 2)) S M K')

/-- A single pair of windows reads all real or complex weightings of an isolated ζ cluster.
The actual local count supplies the carrier geometry; no integrality of weights is used. -/
theorem zeta_weighted_discMoment_readout_explicit (J : ℕ) {lam S M K' : ℝ}
    (hlam : 1 / 2 < lam) (hM : 0 ≤ M) (hK' : 0 ≤ K') :
    ∀ T : ℝ, zetaWeightedMomentCameraHeight J lam S M K' ≤ T →
      ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → |z₀.re - 1 / 2| ≤ 1 / 2 →
      ∀ r : ℝ, 0 ≤ r → r ≤ T ^ (-(M + slowExponent lam + 1)) →
      (∀ z ∈ zetaZeroConfig.carrier, |z.im - T| ≤ T / 2 →
        ‖z - z₀‖ ≤ r ∨ T ^ (-M) ≤ ‖z - z₀‖) →
      ∀ s : Finset ℂ, (∀ z ∈ s, ‖z - z₀‖ ≤ r) →
      (∀ z ∈ zetaZeroConfig.carrier, ‖z - z₀‖ ≤ r → z ∈ s) →
      ∃ F G : ℝ → ℂ,
        ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) F ∧
        ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) G ∧
        pointImage (localWindow z₀.im F) (localWindow z₀.im G) z₀ ≠ 0 ∧
        ∀ weights : ℂ → ℂ, (∀ z, weights z ≠ 0 → z ∈ zetaZeroConfig.carrier) →
          (Summable fun z => ‖weights z‖ / (1 + Complex.normSq (gammaOf z))) →
          (∑' z, ‖weights z‖ / (1 + Complex.normSq (gammaOf z))) ≤ S →
          ∀ j : ℕ, j ≤ J →
            ApertureWindow (lam * (Real.log (T / (2 * π)) / 2))
              (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F)) ∧
            ‖weightedImage weights (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F))
                (localWindow z₀.im G) /
                  ((-I) ^ j * pointImage (localWindow z₀.im F) (localWindow z₀.im G) z₀) -
              ∑ z ∈ s, weights z * (gammaOf z - gammaOf z₀) ^ j‖ ≤
              (∑ z ∈ s, ‖weights z‖) * r ^ (j + 1) * T ^ (M + slowExponent lam) +
                Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := by
  intro T hT z₀ hz₀T hz₀re r hr0 hr hiso s hs hcover
  have hθ : 1 < lam + 1 / 2 := by linarith only [hlam]
  have hcount := card_zeta_camera_band_le hθ ((le_max_left _ _).trans hT)
  exact weighted_discMoment_readout_rvm_explicit J
    (by linarith only [hθ] : 0 ≤ lam + 1 / 2) (by linarith only [hlam])
    (zetaCameraCountConstant_nonneg hθ) hM hK' T ((le_max_right _ _).trans hT)
    zetaZeroConfig (fun t x y hxy ht => hcount t x y hxy ht)
    z₀ hz₀T hz₀re r hr0 hr hiso s hs hcover

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_weighted_discMoment_readout_explicit

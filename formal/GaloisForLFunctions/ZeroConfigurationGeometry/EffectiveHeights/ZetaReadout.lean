import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.LocalZetaCount
import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.SpectralMass
import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.MomentReadout
import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.PointReadout

/-!
# The actual ζ camera with all analytic constants specified

Choose the density factor `θ=λ+1/2`. The explicit local count and numerical
Lorentzian mass discharge the analytic inputs at every aperture factor
`λ>1/2`; only the stated geometric isolation conditions remain.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

/-- Starting height for the actual ζ multiplicity camera at any aperture factor above one half. -/
def zetaPointCameraHeight (lam M : ℝ) : ℝ :=
  max (zetaCameraCountHeight (lam + 1 / 2))
    (cameraPointHeight (lam + 1 / 2) lam (zetaCameraCountConstant (lam + 1 / 2)) (33 / 100) M)

/-- Starting height for the actual ζ moment camera, with all analytic constants discharged. -/
def zetaMomentCameraHeight (J : ℕ) (lam M K' : ℝ) : ℝ :=
  max (zetaCameraCountHeight (lam + 1 / 2))
    (cameraMomentHeight J (lam + 1 / 2) lam (zetaCameraCountConstant (lam + 1 / 2)) (33 / 100) M K')

/-- Every polynomially isolated ζ zero is read with its integer multiplicity above a finite height. -/
theorem zeta_reads_mult_at_explicit_height {lam M : ℝ} (hlam : 1 / 2 < lam) (hM : 0 ≤ M) :
    ∀ T : ℝ, zetaPointCameraHeight lam M ≤ T →
      ∀ z₀ ∈ zetaZeroConfig.carrier, |z₀.im - T| ≤ T / 4 →
        (∀ z ∈ zetaZeroConfig.carrier, z ≠ z₀ → |z.im - T| ≤ T / 2 →
          T ^ (-M) ≤ ‖z - z₀‖) →
        ∃ F G : ℝ → ℂ,
          ApertureWindow (lam * (Real.log (T / (2 * Real.pi)) / 2)) F ∧
          ApertureWindow (lam * (Real.log (T / (2 * Real.pi)) / 2)) G ∧
          pointImage F G z₀ ≠ 0 ∧ zetaZeroConfig.W F G ≠ 0 ∧
          (∀ z ∈ zetaZeroConfig.carrier, z ≠ z₀ → |z.im - z₀.im| ≤ T / 4 →
            pointImage F G z = 0) ∧
          ‖zetaZeroConfig.W F G / pointImage F G z₀ - (zetaZeroConfig.mult z₀ : ℂ)‖ ≤ 1 / 4 := by
  intro T hT z₀ hz₀ hz₀T hiso
  have hθ : 1 < lam + 1 / 2 := by linarith only [hlam]
  have hcount := card_zeta_camera_band_le hθ ((le_max_left _ _).trans hT)
  have hmass : (∑' z : ℂ,
      ‖zetaZeroConfig.carrier.indicator (fun w => (zetaZeroConfig.mult w : ℂ)) z‖ /
        (1 + Complex.normSq (gammaOf z))) ≤ 33 / 100 := by
    simpa only [multDiff_emptyZeroConfig] using zeta_empty_lorentzian_mass_lt.le
  exact exists_window_pair_reads_mult_subspacing_explicit
    (by linarith only [hθ] : 0 ≤ lam + 1 / 2) (by linarith only [hlam])
    (zetaCameraCountConstant_nonneg hθ) (by norm_num : (0 : ℝ) ≤ 33 / 100) hM
    T ((le_max_right _ _).trans hT) zetaZeroConfig temperedConfig_zeta hmass
    (fun s x y hxy hs => hcount s x y hxy hs) z₀ hz₀ hz₀T hiso

private theorem zeta_mem_of_multDiff_empty_ne_zero {z : ℂ}
    (h : multDiff zetaZeroConfig emptyZeroConfig z ≠ 0) : z ∈ zetaZeroConfig.carrier := by
  have hcar := mem_carrier_of_multDiff_ne_zero h
  simpa only [Set.mem_union, emptyZeroConfig, Set.mem_empty_iff_false, or_false] using hcar

/-- Every finitely isolated ζ cluster has an explicit moment-readout horizon. -/
theorem zeta_discMoment_readout_explicit (J : ℕ) {lam M K' : ℝ}
    (hlam : 1 / 2 < lam) (hM : 0 ≤ M) (hK' : 0 ≤ K') :
    ∀ T : ℝ, zetaMomentCameraHeight J lam M K' ≤ T →
      ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → |z₀.re - 1 / 2| ≤ 1 / 2 →
      ∀ r : ℝ, 0 ≤ r → r ≤ T ^ (-(M + slowExponent lam + 1)) →
      (∀ z ∈ zetaZeroConfig.carrier, |z.im - T| ≤ T / 2 →
        ‖z - z₀‖ ≤ r ∨ T ^ (-M) ≤ ‖z - z₀‖) →
      ∀ s : Finset ℂ, (∀ z ∈ s, z ∈ zetaZeroConfig.carrier ∧ ‖z - z₀‖ ≤ r) →
      (∀ z ∈ zetaZeroConfig.carrier, ‖z - z₀‖ ≤ r → z ∈ s) →
      ∃ F G : ℝ → ℂ,
        ApertureWindow (lam * (Real.log (T / (2 * Real.pi)) / 2)) F ∧
        ApertureWindow (lam * (Real.log (T / (2 * Real.pi)) / 2)) G ∧
        pointImage (localWindow z₀.im F) (localWindow z₀.im G) z₀ ≠ 0 ∧
        ∀ j : ℕ, j ≤ J →
          ApertureWindow (lam * (Real.log (T / (2 * Real.pi)) / 2))
            (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F)) ∧
          ‖zetaZeroConfig.W (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F))
              (localWindow z₀.im G) /
                ((-I) ^ j * pointImage (localWindow z₀.im F) (localWindow z₀.im G) z₀) -
            ∑ z ∈ s, (zetaZeroConfig.mult z : ℂ) * (gammaOf z - gammaOf z₀) ^ j‖ ≤
            (∑ z ∈ s, (zetaZeroConfig.mult z : ℝ)) * r ^ (j + 1) * T ^ (M + slowExponent lam) +
              Real.exp (-(K' * Real.log (T / (2 * Real.pi)) ^ 3)) := by
  intro T hT z₀ hz₀T hz₀re r hr0 hr hiso s hs hcover
  have hθ : 1 < lam + 1 / 2 := by linarith only [hlam]
  have hcount := card_zeta_camera_band_le hθ ((le_max_left _ _).trans hT)
  obtain ⟨F, G, hF, hG, hP, hread⟩ := discMoment_readout_rvm_explicit J
    (by linarith only [hθ] : 0 ≤ lam + 1 / 2) (by linarith only [hlam])
    (zetaCameraCountConstant_nonneg hθ) (by norm_num : (0 : ℝ) ≤ 33 / 100) hM hK'
    T ((le_max_right _ _).trans hT) zetaZeroConfig emptyZeroConfig
    temperedConfig_zeta temperedConfig_emptyZeroConfig zeta_empty_lorentzian_mass_lt.le
    (fun a x y hxy ha => hcount a x y hxy fun z hz =>
      ⟨zeta_mem_of_multDiff_empty_ne_zero (ha z hz).1, (ha z hz).2⟩)
    z₀ hz₀T hz₀re r hr0 hr
    (fun z hcz hzT => hiso z (zeta_mem_of_multDiff_empty_ne_zero hcz) hzT)
    s (fun z hz => (hs z hz).2)
    (fun z hcz hzr => hcover z (zeta_mem_of_multDiff_empty_ne_zero hcz) hzr)
  have hm (j : ℕ) : (∑ z ∈ s, multDiff zetaZeroConfig emptyZeroConfig z *
      (gammaOf z - gammaOf z₀) ^ j) =
      ∑ z ∈ s, (zetaZeroConfig.mult z : ℂ) * (gammaOf z - gammaOf z₀) ^ j := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [multDiff_emptyZeroConfig, Set.indicator_of_mem (hs z hz).1]
  have hN : (∑ z ∈ s, ‖multDiff zetaZeroConfig emptyZeroConfig z‖) =
      ∑ z ∈ s, (zetaZeroConfig.mult z : ℝ) := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [multDiff_emptyZeroConfig, Set.indicator_of_mem (hs z hz).1, Complex.norm_natCast]
  refine ⟨F, G, hF, hG, hP, fun j hj => ?_⟩
  obtain ⟨hW, herr⟩ := hread j hj
  rw [W_emptyZeroConfig, sub_zero, hm j, hN] at herr
  exact ⟨hW, herr⟩


end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_reads_mult_at_explicit_height
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_discMoment_readout_explicit

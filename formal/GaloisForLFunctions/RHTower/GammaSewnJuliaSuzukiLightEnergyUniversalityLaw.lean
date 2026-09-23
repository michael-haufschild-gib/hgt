import GaloisForLFunctions.RHTower.GammaSewnMobiusJuliaSourceTransport
import GaloisForLFunctions.RHTower.SuzukiValuationDepthLightCoercivity

/-!
# Gamma-sewn Julia defect as the source of Suzuki light-depth mass

The Gamma-sewn Julia environment and the Suzuki valuation-depth light family use the same Möbius
aperture node.  Their exact factorizations share the same squared aperture gap.  Eliminating that
gap identifies the Suzuki endpoint and complete two-light energy directly with the Julia defect.
-/

namespace RHTower

noncomputable section

/-- Positive source scale relating the Suzuki endpoint to the Gamma-sewn Julia defect. -/
def gammaSewnJuliaSuzukiSourceScale (h : ℝ) (p : Nat.Primes) : ℝ :=
  Real.sqrt (Real.log (p : ℝ) *
      Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ))) *
    (h * Real.sqrt h)⁻¹ *
    ((p : ℝ) + 1)⁻¹

/-- Exact gain multiplying the common squared Möbius aperture gap. -/
def gammaSewnJuliaSuzukiDefectGain
    (h a : ℝ) (p : Nat.Primes) : ℝ :=
  gammaSewnMobiusValuationQuadraticDefectGain ((h / 2) * a) p *
    (1 + gammaSewnMobiusValuationContractionMultiplier ((h / 2) * a) p)

/-- The Suzuki endpoint amplitude, after multiplication by the Julia gain, is exactly the
source-scaled square of the retained Julia environment. -/
theorem suzukiEndpoint_mul_juliaGain_eq_scale_mul_juliaDefectSq
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    suzukiCriticalEntryWallEndpointAmplitude h a p 0 *
        gammaSewnJuliaSuzukiDefectGain h a p =
      gammaSewnJuliaSuzukiSourceScale h p *
        gammaSewnMobiusJuliaDefect ((h / 2) * a) p ^ (2 : ℕ) := by
  rw [suzukiCriticalEntryWallEndpointAmplitude_zero_eq_coherentWeight,
    gammaSewnMobiusJuliaDefect_sq_eq_aperture_sq_mul_gain
      (mul_nonneg (div_nonneg hh.le (by norm_num)) ha.le)]
  unfold gammaSewnJuliaSuzukiDefectGain gammaSewnJuliaSuzukiSourceScale
  ring

/-- **Gamma-sewn Julia/Suzuki light-energy universality.**  The complete two-light energy,
renormalized by the exact Julia gain, is the Julia environment fourth power over the geometric
depth denominator.  Both individual light channels remain strictly positive. -/
theorem gammaSewnJulia_suzukiLightEnergyUniversality
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (t : ℝ) (p : Nat.Primes) :
    (suzukiCriticalApertureNegativeLightDepthEnergy h a t hh ha p +
        suzukiCriticalAperturePositiveLightDepthEnergy h a t hh ha p) *
        gammaSewnJuliaSuzukiDefectGain h a p ^ (2 : ℕ) =
      (gammaSewnJuliaSuzukiSourceScale h p *
          gammaSewnMobiusJuliaDefect ((h / 2) * a) p ^ (2 : ℕ)) ^ (2 : ℕ) /
        (1 - suzukiCriticalApertureDepthFusionRadius h a p ^ (2 : ℕ)) ∧
      0 < suzukiCriticalApertureNegativeLightDepthEnergy h a t hh ha p ∧
      0 < suzukiCriticalAperturePositiveLightDepthEnergy h a t hh ha p := by
  refine ⟨?_,
    suzukiCriticalApertureNegativeLightDepthEnergy_pos hh ha t p,
    suzukiCriticalAperturePositiveLightDepthEnergy_pos hh ha t p⟩
  rw [suzukiCriticalApertureLightDepthEnergies_add hh ha]
  rw [← suzukiEndpoint_mul_juliaGain_eq_scale_mul_juliaDefectSq hh ha p]
  ring

end

end RHTower

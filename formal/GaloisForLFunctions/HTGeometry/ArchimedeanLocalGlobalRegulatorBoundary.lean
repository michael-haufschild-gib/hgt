import GaloisForLFunctions.HTGeometry.ScaledGammaBorelResidue

/-!
# Archimedean local Stokes data versus global connection constants

The Borel transform of the factorial asymptotic expansion for the exponential integral is
`1 / (1 + ξ)`: it has one simple pole at `ξ = -1` with residue `1`.  The corresponding contour jump
is therefore the universal `2πi` residue factor.  The scaled-Gamma residue infrastructure supplies
the analogous `2πi` lattice of local Gamma poles.

Local jump/difference data cannot recover a global additive connection coefficient: adding any
constant leaves every two-point difference unchanged.  The closed noninjectivity theorem below is
the exact abstract obstruction behind the valid part of the archimedean local/global distinction.
-/

open Complex Filter Set
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Borel transform of the factorial tail in the asymptotic expansion of `E₁`. -/
def exponentialIntegralBorel (ξ : ℂ) : ℂ := (1 + ξ)⁻¹

/-- Its denominator vanishes exactly at the single Borel singularity `-1`. -/
theorem exponentialIntegralBorel_denominator_eq_zero_iff (ξ : ℂ) :
    1 + ξ = 0 ↔ ξ = -1 := by
  constructor <;> intro h
  · linear_combination h
  · rw [h]
    ring

/-- The Borel singularity at `-1` is simple and has residue `1`. -/
theorem exponentialIntegralBorel_residue_at_neg_one :
    Tendsto
      (fun ξ : ℂ => (ξ - (-1)) * exponentialIntegralBorel ξ)
      (nhdsWithin (-1) ({(-1 : ℂ)}ᶜ)) (nhds 1) := by
  let denominator : ℂ → ℂ := fun ξ => ξ + 1
  let numerator : ℂ → ℂ := fun _ => 1
  have hden : HasDerivAt denominator 1 (-1) := by
    simpa [denominator] using (hasDerivAt_id (-1)).add_const (1 : ℂ)
  have hden0 : denominator (-1) = 0 := by simp [denominator]
  have hnum : ContinuousAt numerator (-1) := by fun_prop
  have hres := RHTower.tendsto_residue_of_simple_zero
    hden hden0 one_ne_zero hnum
  simpa [denominator, numerator, exponentialIntegralBorel, add_comm] using hres

/-- Local connection data retaining only differences between endpoint values. -/
def connectionDifferenceProfile (f : ℂ → ℂ) : ℂ × ℂ → ℂ :=
  fun zw => f zw.1 - f zw.2

/-- Adding a global connection constant changes no local difference data. -/
theorem connectionDifferenceProfile_add_const (f : ℂ → ℂ) (c : ℂ) :
    connectionDifferenceProfile (fun z => f z + c) = connectionDifferenceProfile f := by
  funext zw
  simp [connectionDifferenceProfile]

/-- **Global connection coefficients are not reconstructible from local jump data.** The zero and
one functions are distinct but have the same complete difference profile. -/
theorem connectionDifferenceProfile_not_injective :
    ¬ Function.Injective connectionDifferenceProfile := by
  intro h
  let f : ℂ → ℂ := fun _ => 0
  let g : ℂ → ℂ := fun _ => 1
  have hprofile : connectionDifferenceProfile f = connectionDifferenceProfile g := by
    funext zw
    simp [connectionDifferenceProfile, f, g]
  have hfg := h hprofile
  have hzero := congrFun hfg 0
  simp [f, g] at hzero

/-- Closed local/global endpoint for the exponential-integral seam. -/
theorem archimedeanLocalGlobalRegulatorBoundary :
    Tendsto
      (fun ξ : ℂ => (ξ - (-1)) * exponentialIntegralBorel ξ)
      (nhdsWithin (-1) ({(-1 : ℂ)}ᶜ)) (nhds 1) ∧
    ¬ Function.Injective connectionDifferenceProfile :=
  ⟨exponentialIntegralBorel_residue_at_neg_one,
    connectionDifferenceProfile_not_injective⟩

end
end GaloisForLFunctions.HTGeometry

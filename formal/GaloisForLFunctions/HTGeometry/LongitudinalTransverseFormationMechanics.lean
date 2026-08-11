import GaloisForLFunctions.HTGeometry.PoleUnitFormationMechanics
import GaloisForLFunctions.RHTower.CompleteResolutionBoundedBanachFusionLaw

/-!
# Longitudinal--transverse formation mechanics

This module certifies the exact split-source conservation and selection obstruction in
`longitudinal-transverse-source-fusion-mixing-defect-and-selection-gate-law.md`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Zero-longitudinal part determined by a codiagonal and a marked section. -/
def sourceSplitRadical
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (c : X →L[ℂ] ℂ) (e : ℂ →L[ℂ] X) (x : X) : X :=
  x - e (c x)

/-- Longitudinal response created when an intervention acts on the transverse radical. -/
def longitudinalMixingDefect
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (c : X →L[ℂ] ℂ) (e : ℂ →L[ℂ] X) (T : X →L[ℂ] X) (x : X) : ℂ :=
  c (T (sourceSplitRadical c e x))

/-- The marked section makes the split radical genuinely zero-longitudinal. -/
theorem sourceSplitRadical_codiagonal
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (c : X →L[ℂ] ℂ) (e : ℂ →L[ℂ] X)
    (hsection : ∀ z, c (e z) = z) (x : X) :
    c (sourceSplitRadical c e x) = 0 := by
  simp [sourceSplitRadical, hsection]

/-- Longitudinal coordinate plus split radical jointly reconstruct the source. -/
theorem sourceSplitRadical_add_section
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (c : X →L[ℂ] ℂ) (e : ℂ →L[ℂ] X) (x : X) :
    sourceSplitRadical c e x + e (c x) = x := by
  simp [sourceSplitRadical]

/-- **Exact intervention conservation.**  Every output is section response plus mixing defect. -/
theorem longitudinal_intervention_conservation
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (c : X →L[ℂ] ℂ) (e : ℂ →L[ℂ] X) (T : X →L[ℂ] X) (x : X) :
    c (T x) = longitudinalMixingDefect c e T x + c (T (e (c x))) := by
  rw [← sourceSplitRadical_add_section c e x, map_add, map_add]
  rfl

/-- Vanishing mixing defect is exactly preservation of the zero-mass radical. -/
theorem mixingDefect_zero_iff_preserves_kernel
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (c : X →L[ℂ] ℂ) (e : ℂ →L[ℂ] X)
    (hsection : ∀ z, c (e z) = z) (T : X →L[ℂ] X) :
    (∀ x, longitudinalMixingDefect c e T x = 0) ↔
      ∀ y, c y = 0 → c (T y) = 0 := by
  constructor
  · intro hmix y hy
    have h := hmix y
    simpa [longitudinalMixingDefect, sourceSplitRadical, hy] using h
  · intro hpres x
    exact hpres (sourceSplitRadical c e x)
      (sourceSplitRadical_codiagonal c e hsection x)

/-- A radical-preserving intervention with scalar section action can only rescale the
longitudinal response. -/
theorem noMixing_scalar_longitudinal_action
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (c : X →L[ℂ] ℂ) (e : ℂ →L[ℂ] X) (T : X →L[ℂ] X) (a : ℂ)
    (hmix : ∀ x, longitudinalMixingDefect c e T x = 0)
    (hsectionAction : ∀ z, c (T (e z)) = a * z) (x : X) :
    c (T x) = a * c x := by
  rw [longitudinal_intervention_conservation c e T x, hmix, zero_add,
    hsectionAction]

open RHTower

/-- Literal complete-shell source with scalar longitudinal factor `U`. -/
def completeResolutionFormedSource
    (K : ℕ) (U : ℂ → ℂ) (z : ℂ) (hz : 0 < z.re) :
    CompleteResolutionSourceSpace :=
  U z • completeResolutionSourceVector K z hz

/-- Complete-shell codiagonal fusion lands exactly on the scalar longitudinal factor. -/
theorem sourceFusionCodiagonal_completeResolutionFormedSource
    (K : ℕ) (U : ℂ → ℂ) (z : ℂ) (hz : 0 < z.re) :
    sourceFusionCodiagonal (completeResolutionFormedSource K U z hz) = U z := by
  rw [completeResolutionFormedSource, map_smul]
  have hmass := (completeResolution_banachHilbert_sourceFusion_dichotomy K z hz).2.1
  rw [hmass, smul_eq_mul, mul_one]

/-- **Three-organ fusion.**  Shell resolution and bounded codiagonal fusion land on the exact
pole-unit scale response. -/
theorem completeResolutionFormedSource_scaleResponse
    (K : ℕ) (U : ℂ → ℂ) (ε w : ℂ)
    (hε : 0 < ε.re) (hεw : 0 < (ε * w).re) :
    sourceFusionCodiagonal
          (completeResolutionFormedSource K U (ε * w) hεw) /
        sourceFusionCodiagonal (completeResolutionFormedSource K U ε hε) =
      correctedScaleResponse U ε w := by
  rw [sourceFusionCodiagonal_completeResolutionFormedSource,
    sourceFusionCodiagonal_completeResolutionFormedSource]
  rfl

/-- A transverse perturbation is erased by codiagonal fusion. -/
theorem sourceFusionCodiagonal_transverse_perturbation
    (K : ℕ) (U : ℂ → ℂ) (z : ℂ) (hz : 0 < z.re)
    (q : CompleteResolutionSourceSpace) (hq : sourceFusionCodiagonal q = 0) :
    sourceFusionCodiagonal (completeResolutionFormedSource K U z hz + q) = U z := by
  rw [map_add, sourceFusionCodiagonal_completeResolutionFormedSource, hq, add_zero]

/-- Even endpoint-dependent transverse perturbations leave the fused pole-unit response
unchanged. -/
theorem completeResolution_scaleResponse_transverse_blind
    (K : ℕ) (U : ℂ → ℂ) (ε w : ℂ)
    (hε : 0 < ε.re) (hεw : 0 < (ε * w).re)
    (qε qεw : CompleteResolutionSourceSpace)
    (hqε : sourceFusionCodiagonal qε = 0)
    (hqεw : sourceFusionCodiagonal qεw = 0) :
    sourceFusionCodiagonal
          (completeResolutionFormedSource K U (ε * w) hεw + qεw) /
        sourceFusionCodiagonal
          (completeResolutionFormedSource K U ε hε + qε) =
      correctedScaleResponse U ε w := by
  rw [sourceFusionCodiagonal_transverse_perturbation,
    sourceFusionCodiagonal_transverse_perturbation]
  rfl

end

end GaloisForLFunctions.HTGeometry

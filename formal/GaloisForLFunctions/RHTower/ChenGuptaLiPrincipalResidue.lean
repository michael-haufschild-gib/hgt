/-
# Chen--Gupta--Li principal-character detector residue

When the Dirichlet character is principal, shifting the detector Mellin line
crosses the additional pole `w = 1 - ρ` of `L(ρ+w,χ)`.  This module packages
that branch as certified data and derives the exact residue of the full finite
detector integrand from mathlib's trivial-character L-function residue.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiZeroResidue
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

open Complex LSeries DirichletCharacter Filter MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A certified critical-strip zero of the principal Dirichlet character. -/
structure CGLPrincipalCriticalStripLZero (q : ℕ) extends CGLCriticalStripLZero q where
  character_eq_one : character = 1

/-- The location of the principal-character pole in the shifted Mellin variable. -/
def cglPrincipalPole (z : CGLPrincipalCriticalStripLZero q) : ℂ := 1 - z.point

/-- The exact residue of the trivial Dirichlet character L-function at one. -/
def cglPrincipalLFunctionResidue (q : ℕ) : ℂ :=
  ∏ p ∈ (q + 1).primeFactors, (1 - (p : ℂ)⁻¹)

/-- Translation by the certified zero carries the principal Mellin pole to
the L-function pole at one. -/
theorem cglPrincipalPole_shift_eq_one (z : CGLPrincipalCriticalStripLZero q) :
    z.point + cglPrincipalPole z = 1 := by
  unfold cglPrincipalPole
  ring

/-- The principal Mellin pole lies strictly in the positive real half-plane. -/
theorem cglPrincipalPole_re_pos (z : CGLPrincipalCriticalStripLZero q) :
    0 < (cglPrincipalPole z).re := by
  unfold cglPrincipalPole
  rw [Complex.sub_re]
  norm_num
  linarith [z.lt_one]

/-- The affine translation maps the punctured neighbourhood of the principal
Mellin pole to the punctured neighbourhood of one. -/
theorem cglTendsto_shift_to_principalPole (z : CGLPrincipalCriticalStripLZero q) :
    Tendsto (fun w : ℂ => z.point + w)
      (nhdsWithin (cglPrincipalPole z) ({cglPrincipalPole z}ᶜ : Set ℂ))
      (nhdsWithin 1 ({1}ᶜ : Set ℂ)) := by
  change Filter.map (fun w : ℂ => z.point + w)
    (nhdsWithin (cglPrincipalPole z) ({cglPrincipalPole z}ᶜ : Set ℂ)) ≤
      nhdsWithin 1 ({1}ᶜ : Set ℂ)
  simpa only [Homeomorph.coe_addLeft, cglPrincipalPole_shift_eq_one] using
    ((Homeomorph.addLeft z.point).map_punctured_nhds_eq (cglPrincipalPole z)).le

/-- The affine translation also converges to one along the full neighbourhood,
for composing ordinary continuity statements. -/
theorem cglTendsto_shift_to_one (z : CGLPrincipalCriticalStripLZero q) :
    Tendsto (fun w : ℂ => z.point + w)
      (nhdsWithin (cglPrincipalPole z) ({cglPrincipalPole z}ᶜ : Set ℂ)) (nhds 1) := by
  have hid : Tendsto (fun w : ℂ => w)
      (nhdsWithin (cglPrincipalPole z) ({cglPrincipalPole z}ᶜ : Set ℂ))
      (nhds (cglPrincipalPole z)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa only [cglPrincipalPole_shift_eq_one] using
    (tendsto_const_nhds.add hid : Tendsto (fun w : ℂ => z.point + w)
      (nhdsWithin (cglPrincipalPole z) ({cglPrincipalPole z}ᶜ : Set ℂ))
      (nhds (z.point + cglPrincipalPole z)))

/-- Exact simple-pole limit of the translated principal Dirichlet L-function. -/
theorem cglPrincipalLFunction_poleLimit (q : ℕ)
    (z : CGLPrincipalCriticalStripLZero q) :
    Tendsto (fun w : ℂ => (w - cglPrincipalPole z) *
      DirichletCharacter.LFunction z.character (z.point + w))
      (nhdsWithin (cglPrincipalPole z) ({cglPrincipalPole z}ᶜ : Set ℂ))
      (nhds (cglPrincipalLFunctionResidue q)) := by
  have h := (DirichletCharacter.LFunctionTrivChar_residue_one (N := q + 1)).comp
    (cglTendsto_shift_to_principalPole z)
  change Tendsto (fun w : ℂ => ((z.point + w) - 1) *
    DirichletCharacter.LFunctionTrivChar (q + 1) (z.point + w))
    (nhdsWithin (cglPrincipalPole z) ({cglPrincipalPole z}ᶜ : Set ℂ))
    (nhds (∏ p ∈ (q + 1).primeFactors, (1 - (p : ℂ)⁻¹))) at h
  change Tendsto (fun w : ℂ => (w - cglPrincipalPole z) *
    DirichletCharacter.LFunction z.character (z.point + w))
      (nhdsWithin (cglPrincipalPole z) ({cglPrincipalPole z}ᶜ : Set ℂ))
      (nhds (∏ p ∈ (q + 1).primeFactors, (1 - (p : ℂ)⁻¹)))
  rw [z.character_eq_one]
  convert h using 1
  funext w
  have hscalar : w - cglPrincipalPole z = (z.point + w) - 1 := by
    unfold cglPrincipalPole
    ring
  rw [hscalar]

/-- Exact simple-pole limit of the full finite detector Mellin integrand in
the principal-character branch. -/
theorem cglPrincipalDetectorMellinIntegrand_poleLimit (X q : ℕ)
    (z : CGLPrincipalCriticalStripLZero q) :
    Tendsto (fun w : ℂ => (w - cglPrincipalPole z) *
      cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero w)
      (nhdsWithin (cglPrincipalPole z) ({cglPrincipalPole z}ᶜ : Set ℂ))
      (nhds (Complex.Gamma (cglPrincipalPole z) *
        zeroDetectionMobiusPolynomial X (q + 1) z.character 1 * cglPrincipalLFunctionResidue q)) := by
  have hgamma : Tendsto Complex.Gamma
      (nhdsWithin (cglPrincipalPole z) ({cglPrincipalPole z}ᶜ : Set ℂ))
      (nhds (Complex.Gamma (cglPrincipalPole z))) :=
    (HTGeometry.analyticAt_Gamma_of_re_pos (cglPrincipalPole_re_pos z)).continuousAt.tendsto
      |>.mono_left nhdsWithin_le_nhds
  have hpoly : Tendsto (fun w : ℂ =>
      zeroDetectionMobiusPolynomial X (q + 1) z.character (z.point + w))
      (nhdsWithin (cglPrincipalPole z) ({cglPrincipalPole z}ᶜ : Set ℂ))
      (nhds (zeroDetectionMobiusPolynomial X (q + 1) z.character 1)) := by
    have hcont := (continuousAt_zeroDetectionMobiusPolynomial X (q + 1) z.character 1).tendsto
    exact hcont.comp (cglTendsto_shift_to_one z)
  have hfront := hgamma.mul hpoly
  have hL := cglPrincipalLFunction_poleLimit q z
  have h := hfront.mul hL
  convert h using 1
  funext w
  unfold cglDetectorMellinIntegrand
  ring

end RHTower

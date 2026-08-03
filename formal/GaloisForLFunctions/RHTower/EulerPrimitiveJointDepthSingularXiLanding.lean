import GaloisForLFunctions.RHTower.EulerPrimitiveJointDepthBiorthogonalCommonTest
import GaloisForLFunctions.RHTower.CriticalMellinFourCoordinateCollapseUniversalityLaw
import GaloisForLFunctions.RHTower.InverseTiltedPrimeGammaCentralSource

/-!
# Singular joint-depth source landing in the Xi resolvent

The literal primitive/reciprocal joint-depth pairing initially exists only in its positive
Laplace chamber.  Subtracting it from the two forced polar Cauchy channels gives exactly the
pole-filled critical-Mellin defect.  That regularized defect continues through the balanced
Euler wall and, after adding the fixed Gamma connection and changing to the centered coordinate,
lands in the Xi relative resolvent.

No Xi-zero coordinate enters the source definition.  The final equality is stated on the regular
resolvent locus because Lean's totalized logarithmic derivative does not encode meromorphic pole
values at a zero.  No Riemann-hypothesis or zero-location assumption is used.
-/

open Complex Function Set Topology
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Polar-renormalized literal joint-depth pairing on its Laplace chamber. -/
def xiGammaEulerPrimitiveJointDepthLaplaceDefect (w v : ℂ) : ℂ :=
  let u := w + star v
  1 / u + 1 / (u + 1) -
    xiGammaEulerPrimitiveJointDepthPairedCodiagonal w v

/-- The literal biorthogonal joint-depth source, after the two source-forced polar counterterms,
is exactly the pole-filled critical-Mellin defect. -/
theorem xiGammaEulerPrimitiveJointDepthLaplaceDefect_eq_regularized
    {w v : ℂ} (h : 0 < w.re + v.re) :
    xiGammaEulerPrimitiveJointDepthLaplaceDefect w v =
      regularizedCriticalMellinDefect (w + star v) := by
  have hu : 0 < (w + star v).re := by
    change 0 < w.re + v.re
    exact h
  rw [xiGammaEulerPrimitiveJointDepthLaplaceDefect,
    xiGammaEulerPrimitiveJointDepthPairedCodiagonal_eq h]
  change 1 / (w + star v) + 1 / (w + star v + 1) -
      vonMangoldtPrimeLaplaceChannelComplex (w + star v) = _
  rw [← continuousPolarLaplaceChannelComplex_eq hu]
  change criticalMellinDefectLaplaceChannelComplex (w + star v) = _
  exact (criticalMellin_fourCoordinateCollapse hu).1.trans
    ((criticalMellin_fourCoordinateCollapse hu).2.1.trans
      (criticalMellin_fourCoordinateCollapse hu).2.2)

/-- Coordinate inverse from critical-Mellin displacement `u=s-1` to centered Xi coordinate. -/
def criticalMellinToCenteredXi (u : ℂ) : ℂ :=
  -I * (u + 1 / 2)

theorem criticalMellinToCenteredXi_mul_I (u : ℂ) :
    1 / 2 + criticalMellinToCenteredXi u * I = u + 1 := by
  rw [criticalMellinToCenteredXi]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem xiCriticalMellinCoordinate_criticalMellinToCenteredXi (u : ℂ) :
    xiCriticalMellinCoordinate (criticalMellinToCenteredXi u) = u := by
  rw [xiCriticalMellinCoordinate, criticalMellinToCenteredXi]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Pole-filled joint-depth source continuation completed by the fixed Gamma connection. -/
def xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace (u : ℂ) : ℂ :=
  I * (regularizedCriticalMellinDefect u +
    gammaRealLogConnection (u + 1))

/-- **Unconditional source-to-Xi landing theorem.** On every regular point right of the completed
Gamma boundary, the pole-filled continuation of the literal joint prime/depth source equals the
canonical Xi relative resolvent after the exact centered coordinate change. -/
theorem xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace_eq_xiRelativeResolventTrace
    {u : ℂ} (hu : -1 < u.re) (hu0 : u ≠ 0)
    (hzeta : riemannZeta (u + 1) ≠ 0) :
    xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace u =
      xiRelativeResolventTrace (criticalMellinToCenteredXi u) := by
  let z := criticalMellinToCenteredXi u
  have hspos : 0 < (1 / 2 + z * I).re := by
    rw [show 1 / 2 + z * I = u + 1 by
      exact criticalMellinToCenteredXi_mul_I u]
    rw [Complex.add_re]
    norm_num
    linarith
  have hs1 : 1 / 2 + z * I ≠ 1 := by
    rw [show 1 / 2 + z * I = u + 1 by
      exact criticalMellinToCenteredXi_mul_I u]
    intro h
    apply hu0
    linear_combination h
  have hzeta' : riemannZeta (1 / 2 + z * I) ≠ 0 := by
    rwa [show 1 / 2 + z * I = u + 1 by
      exact criticalMellinToCenteredXi_mul_I u]
  have hreg : regularizedCriticalMellinDefect u =
      continuedCriticalMellinDefect u :=
    regularizedCriticalMellinDefect_eq_continued_of_ne_zero hu0 hzeta
  have hsource := continuedPrimeArchSourceRelativeTrace_eq_continuedMellinGamma
    hspos (by
      intro hzero
      have := hspos
      rw [hzero] at this
      norm_num at this) hs1
  have hxi := continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    hspos hs1 hzeta'
  rw [← hxi, hsource]
  rw [xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace,
    continuedMellinGammaSourceTrace, hreg]
  rw [xiCriticalMellinCoordinate_criticalMellinToCenteredXi]
  rw [criticalMellinToCenteredXi_mul_I]

end

end RHTower

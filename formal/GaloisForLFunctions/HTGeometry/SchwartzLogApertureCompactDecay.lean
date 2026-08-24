import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import GaloisForLFunctions.HTGeometry.L1MellinBoundedTilt

/-!
# Fixed-aperture Schwartz tests and compact remote-quartet decay

The logarithmic-coordinate image of `C_c^∞([e⁻ᴬ,eᴬ])` is the subtype of Schwartz functions
supported in `[-A,A]`, with the inherited Schwartz topology. Mathlib's continuous map
`Schwartz → L¹` therefore sends compact test families to compact `L¹` profile families.

This file proves the exact transport needed by compact-detector arguments and pulls the bounded
positive/negative Mellin-tilt quartet defect back to the original fixed-aperture test space.
-/

open MeasureTheory Filter Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Fixed-aperture smooth logarithmic tests, equipped with the inherited Schwartz topology. -/
abbrev LogApertureSchwartz (A : ℝ) :=
  {f : SchwartzMap ℝ ℂ // Function.support f ⊆ Set.Icc (-A) A}

/-- Continuous passage from a fixed-aperture Schwartz test to its `L¹` class. -/
def logApertureSchwartzToL1 {A : ℝ} (f : LogApertureSchwartz A) : LogMellinL1 :=
  f.1.toLp 1 volume

theorem continuous_logApertureSchwartzToL1 (A : ℝ) :
    Continuous (logApertureSchwartzToL1 (A := A)) := by
  exact SchwartzMap.continuous_toLp.comp continuous_subtype_val

/-- The `L¹` class retains the fixed aperture almost everywhere. -/
theorem supported_logApertureSchwartzToL1 {A : ℝ} (f : LogApertureSchwartz A) :
    SupportedInLogAperture A (logApertureSchwartzToL1 f) := by
  have hcoe := SchwartzMap.coeFn_toLp f.1 1 volume
  filter_upwards [hcoe] with x hx
  intro hnot
  change ((f.1.toLp 1 volume : LogMellinL1) : ℝ → ℂ) x = 0
  rw [hx]
  by_contra hne
  exact hnot (f.2 (Function.mem_support.mpr hne))

/-- Compact fixed-aperture test families have uniformly vanishing remote-quartet defect after the
two opposite Mellin tilts. -/
theorem compact_logApertureSchwartz_quartetDefect_uniformVanishes
    (A δ : ℝ) {K : Set (LogApertureSchwartz A)} (hK : IsCompact K) :
    UniformlyVanishesAlong (cocompact ℝ) K
      (fun t f =>
        (4 * (logMellinL1Fourier
            (logMellinBoundedTilt A δ (logApertureSchwartzToL1 f)) t *
          logMellinL1Fourier
            (logMellinBoundedTilt A (-δ) (logApertureSchwartzToL1 f)) t).re : ℝ)) := by
  have himage : IsCompact (logApertureSchwartzToL1 '' K) :=
    hK.image (continuous_logApertureSchwartzToL1 A)
  have hbase := compact_logMellinBoundedTilt_quartetDefect_uniformVanishes A δ himage
  intro ε hε
  filter_upwards [hbase ε hε] with t ht
  intro f hf
  exact ht (logApertureSchwartzToL1 f) ⟨f, hf, rfl⟩

end

end GaloisForLFunctions.HTGeometry

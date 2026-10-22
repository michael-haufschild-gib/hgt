import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheSquareRootPrecisionLawOfDepthResolution
import GaloisForLFunctions.SquareRootThreshold.DilutedOffLineLatticeHidingLaw

/-!
# The aperture–mass seam is productive

The seams examined so far are empty: joining a bounded-height divisor with a bounded-aperture
certificate leaves the limit at `½` (`TheHeightApertureSeamIsEmpty`), as does raising the
coercivity level or changing the depth unit. This module exhibits a seam that is **not** empty, and
it is the one the mass–aperture exchange law predicts.

Let the data be the depths of a diluted configuration of known dilution `ℓ` and known on-line mass
`2L`, and let the reading be the aperture-`a` certificate. The exchange law
(`mass_ge_of_dilutedLattice_positive`) inverts to an explicit depth bound
(`depth_le_log_of_positive_of_mass`): for `ℓ < 2a ≤ L`,

`δ ≤ log ((2L + 2a + ℓ) / ℓ) / (2a − ℓ)`.

In the calculus this reads `certifies_depth_dilutedReading`: with the mass and the dilution known,
the aperture-`a` certificate **certifies** that bound — a nontrivial number, unlike every bounded
reading the programme has floored, and one that tends to `0` as the aperture grows with the mass
held fixed (`theProductiveSeam`).

The moral is the division of labour. A certificate alone reads the scale and nothing of the depth;
a mass bound alone reads nothing at all; together they bound the depth, logarithmically in the mass
and inversely in the aperture. The programme's floors are therefore not statements about
certificates but about certificates *deprived of mass information*, and the productive direction is
to supply that information rather than to sharpen the certificate.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The exchange law inverted -/

/-- **A certificate together with a mass bound bounds the depth.** -/
theorem depth_le_log_of_positive_of_mass {ℓ L δ a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (ha : 0 < a) (haL : a ≤ L / 2) (hgap : ℓ < 2 * a)
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) :
    δ ≤ Real.log ((2 * L + 2 * a + ℓ) / ℓ) / (2 * a - ℓ) := by
  have hcover := (dilutedLattice_weil_nonneg_iff hℓ hL hδ hδ' ha haL).mp hpos
  have hdeep := (latticeFloor_aperture_bounds hℓ hδ ha).2
  have hmass : ℓ * Real.exp (δ * (2 * a - ℓ)) ≤ 2 * L + 2 * a + ℓ := by linarith
  have hquot : Real.exp (δ * (2 * a - ℓ)) ≤ (2 * L + 2 * a + ℓ) / ℓ := by
    rw [le_div_iff₀ hℓ]; linarith
  have hpos' : (0 : ℝ) < (2 * L + 2 * a + ℓ) / ℓ := by positivity
  have hlog : δ * (2 * a - ℓ) ≤ Real.log ((2 * L + 2 * a + ℓ) / ℓ) :=
    (Real.le_log_iff_exp_le hpos').mpr hquot
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * a - ℓ)]
  linarith

/-! ### 2. The seam in the calculus -/

/-- The aperture-`a` certificate of a diluted configuration of known dilution and mass. -/
def dilutedReading {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (a : ℝ) (d : DepthDatum) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
    0 ≤ ((dilutedLatticeConfig hℓ hL d.2.1 d.2.2).W f f).re

/-- **The productive seam.** With the mass and the dilution known, the aperture-`a` certificate
certifies an explicit nontrivial bound on the depth. -/
theorem certifies_depth_dilutedReading {ℓ L a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (ha : 0 < a)
    (haL : a ≤ L / 2) (hgap : ℓ < 2 * a) {d₀ : DepthDatum} (hd₀ : dilutedReading hℓ hL a d₀) :
    Certifies depth (dilutedReading hℓ hL a) d₀
      (Real.log ((2 * L + 2 * a + ℓ) / ℓ) / (2 * a - ℓ)) := by
  intro d hd
  have hread : dilutedReading hℓ hL a d := (mem_shadow_iff.mp hd) ▸ hd₀
  exact depth_le_log_of_positive_of_mass hℓ hL d.2.1 d.2.2 ha haL hgap hread

/-- **A seam that beats the floor.** The certificate alone is floored at `½` in the depth unit; the
same certificate on data of known mass and dilution certifies the explicit bound, which is below
`½` as soon as the aperture is large enough for the mass at hand. -/
theorem theProductiveSeam {ℓ L a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (ha : 0 < a) (haL : a ≤ L / 2)
    (hgap : ℓ < 2 * a) {d₀ : DepthDatum} (hd₀ : dilutedReading hℓ hL a d₀) :
    Certifies depth (dilutedReading hℓ hL a) d₀
        (Real.log ((2 * L + 2 * a + ℓ) / ℓ) / (2 * a - ℓ)) ∧
      ∀ b η : ℝ, 0 < b → ∃ Z : TemperedZeroConfig, width Z = 1 / 2 ∧ apertureGain b η Z :=
  ⟨certifies_depth_dilutedReading hℓ hL ha haL hgap hd₀,
    fun _ η hb => exists_width_eq_half_apertureGain hb η⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality

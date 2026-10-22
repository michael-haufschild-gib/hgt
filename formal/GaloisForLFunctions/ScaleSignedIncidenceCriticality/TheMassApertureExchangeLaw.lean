import GaloisForLFunctions.ScaleSignedIncidenceCriticality.CoercivityAtABoundedApertureIsStillBlind
import GaloisForLFunctions.SquareRootThreshold.DilutedOffLineLatticeHidingLaw

/-!
# The mass–aperture exchange law

A single off-line pair in an on-line background is caught at an aperture logarithmic in the local
on-line mass, while a pure off-line lattice hides up to its own Nyquist aperture. Between the two
sits the diluted lattice: an off-line sub-lattice of spacing parameter `ℓ` inside an on-line
background of mass `2L`. This module computes the exchange rate between the two, and it is
exponential.

Positivity of the diluted configuration at aperture `a` holds exactly when the off-line ground
energy at scale `ℓ` is covered by the on-line mass
(`SquareRootThreshold.dilutedLattice_weil_nonneg_iff`), and the ground energy is bounded below by an
exponential (`SquareRootThreshold.latticeFloor_aperture_bounds`). Hence
(`mass_ge_of_dilutedLattice_positive`):

`ℓ · e^{δ(2a − ℓ)} ≤ 2L + 2a + ℓ`.

So hiding a depth-`δ` off-line sub-lattice from the certificates up to aperture `a` costs on-line
mass exponential in `δa`, whatever the dilution — and therefore
(`aperture_le_of_mass_bound`) a mass budget converts directly into an aperture ceiling:

`e^{δ(2a − ℓ)} ≤ (2L + 2a + ℓ)/ℓ`.

Two consequences for the programme. The trivial floors of the bounded-aperture face need witnesses
whose on-line mass grows exponentially with the aperture
(`theFloorsNeedExponentialMass`), so the on-line zeros are not neutral bystanders but the detector:
mass is what exposes depth. And a mechanism that knows an upper bound for the local on-line mass of
its data already knows an aperture beyond which no off-line sub-lattice can hide.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. Positivity of a diluted lattice forces exponential mass -/

/-- **The exchange law.** If the diluted configuration — an off-line sub-lattice of spacing
parameter `ℓ` and depth `δ` inside an on-line background of mass `2L` — is Weil-positive at
aperture `a`, then the mass is at least exponential in `δa`. -/
theorem mass_ge_of_dilutedLattice_positive {ℓ L δ a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (ha : 0 < a) (haL : a ≤ L / 2)
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) :
    ℓ * Real.exp (δ * (2 * a - ℓ)) ≤ 2 * L + 2 * a + ℓ := by
  have hcover := (dilutedLattice_weil_nonneg_iff hℓ hL hδ hδ' ha haL).mp hpos
  have hdeep := (latticeFloor_aperture_bounds hℓ hδ ha).2
  linarith

/-- **A mass budget caps the aperture at which an off-line sub-lattice can hide.** -/
theorem aperture_le_of_mass_bound {ℓ L δ a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (ha : 0 < a) (haL : a ≤ L / 2)
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) :
    Real.exp (δ * (2 * a - ℓ)) ≤ (2 * L + 2 * a + ℓ) / ℓ := by
  rw [le_div_iff₀ hℓ]
  have := mass_ge_of_dilutedLattice_positive hℓ hL hδ hδ' ha haL hpos
  linarith

/-! ### 2. The floors need exponential mass -/

/-- **The floors need exponentially growing mass.** At every aperture and level there is a
width-`½` configuration passing the certificate; but any such witness built as a diluted lattice
must carry on-line mass exponential in the aperture, so the trivial floors are mass-dominated
phenomena and the on-line zeros of a configuration act as a detector of its off-line ones. -/
theorem theFloorsNeedExponentialMass {a η : ℝ} (ha : 0 < a) :
    (∃ Z : TemperedZeroConfig, width Z = 1 / 2 ∧ apertureGain a η Z) ∧
      ∀ (ℓ L δ : ℝ) (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2), a ≤ L / 2 →
        (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
          0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) →
        ℓ * Real.exp (δ * (2 * a - ℓ)) ≤ 2 * L + 2 * a + ℓ :=
  ⟨exists_width_eq_half_apertureGain ha η,
    fun _ _ _ hℓ hL hδ hδ' haL hpos =>
      mass_ge_of_dilutedLattice_positive hℓ hL hδ hδ' ha haL hpos⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality

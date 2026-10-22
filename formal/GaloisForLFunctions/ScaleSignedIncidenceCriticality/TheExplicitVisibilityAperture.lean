import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheReachLawOfAStructuredCounterexample

/-!
# The explicit visibility aperture

The reach law bounds how far a structured off-line set can hide. Read in the other direction it
names the aperture at which the set becomes **visible**, and the name is explicit.

For the diluted configuration — off-line sub-lattice of spacing parameter `ℓ` and depth `δ` inside
an on-line background of mass `2L` — every aperture `a` with

`log ((3L + ℓ)/ℓ) / (2δ) + ℓ/2 < a ≤ L/2`

admits a test on which the Weil form is negative (`visible_of_reach_lt`). Past that aperture the
certificate is unavailable, so by `refutes_of_not_aperturePositivity` it refutes: the configuration
is caught, not merely unconfirmed.

`theVisibilityAperture` states the dichotomy with both thresholds explicit: free hiding up to
`min (ℓ/2) (L/2)`, visibility past `log((3L+ℓ)/ℓ)/(2δ) + ℓ/2`. The gap between the two thresholds is
exactly the logarithm of the mass-to-dilution ratio divided by twice the depth — the price of the
mass mechanism, and the only part of the reach that is not fixed by the off-line structure itself.

This is the form in which the field's walls become a design specification. A mechanism that wants to
exclude an off-line sub-lattice of spacing parameter `ℓ` and depth `δ` inside a background of mass
`2L` must reach aperture `ℓ/2 + log((3L+ℓ)/ℓ)/(2δ)` and no further; a mechanism that stops short of
`min (ℓ/2) (L/2)` cannot exclude anything at all.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. Visibility past the reach -/

/-- **Past the reach the configuration is visible.** -/
theorem visible_of_reach_lt {ℓ L δ a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (ha : 0 < a) (haL : a ≤ L / 2)
    (hreach : Real.log ((3 * L + ℓ) / ℓ) / (2 * δ) + ℓ / 2 < a) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re < 0 := by
  by_contra hcon
  push Not at hcon
  have hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re := by
    intro f hf hfs
    exact hcon f hf hfs
  exact absurd (reach_upper hℓ hL hδ hδ' ha haL hpos) (not_le.mpr hreach)

/-! ### 2. The two thresholds -/

/-- **The visibility aperture.** Free hiding up to `min (ℓ/2) (L/2)`; visibility past
`log((3L+ℓ)/ℓ)/(2δ) + ℓ/2`. The gap between the two is the price of the mass mechanism. -/
theorem theVisibilityAperture {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) :
    (∀ a : ℝ, 0 < a → a ≤ ℓ / 2 → a ≤ L / 2 → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
        tsupport f ⊆ Icc (-a) a → 0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) ∧
      ∀ a : ℝ, 0 < a → a ≤ L / 2 →
        Real.log ((3 * L + ℓ) / ℓ) / (2 * δ) + ℓ / 2 < a →
        ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
          ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re < 0 :=
  ⟨fun _ ha haℓ haL _ hf hfs => reach_lower hℓ hL hδ hδ' ha haℓ haL hf hfs,
    fun _ ha haL hreach => visible_of_reach_lt hℓ hL hδ hδ' ha haL hreach⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality

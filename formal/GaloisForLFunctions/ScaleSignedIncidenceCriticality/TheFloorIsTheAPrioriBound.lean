import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionIntervalIsTheWholeRange

/-!
# The floor is whatever the a priori bound is

The floors of this programme are stated as `½`, the width of a configuration with a zero on the edge
of the strip. No such configuration is `ζ`'s: an a priori zero-free region already bounds its width
away from `½`. So the natural question is whether a finite-aperture certificate is worth more once
an a priori bound is in hand. It is worth exactly the bound and nothing more.

On the class of configurations of width at most `θ`, with `0 < θ ≤ ½`, the depth-`θ` off-line
lattice of spacing `2π/(2a)` is a member, and it is Weil-positive at aperture `a` because its
Nyquist aperture is exactly `a`. Hence

`resolutionLimit (restrictedWidth θ) (restrictedAperture θ a) = θ`
(`resolutionLimit_restrictedWidth_restrictedAperture`),

and a certificate certifies the bound `β` exactly when `β ≥ θ`
(`certifies_restrictedWidth_iff`): **a finite-aperture certificate never improves an a priori
bound, by any amount**. The same holds for an arbitrary bounded family of apertures
(`resolutionLimit_restrictedWidth_restrictedFamily`).

This is the relativised form of the trans-Nyquist wall and the usable one. It says the floors of
the programme are not the number `½` but the identity map on a priori information: whatever is
known before the certificate is what is known after it. Progress cannot come from sharpening a
bounded certificate against a better zero-free region, since the two do not interact; it must come
from the unbounded direction, where the limit is `0`.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The class cut out by an a priori bound -/

/-- The configurations an a priori zero-free region admits: width at most `θ`. -/
def WidthAtMost (θ : ℝ) : Type := {Z : TemperedZeroConfig // width Z ≤ θ}

/-- The invariant on the restricted class. -/
noncomputable def restrictedWidth (θ : ℝ) (Z : WidthAtMost θ) : ℝ := width Z.1

/-- The aperture-`a` certificate on the restricted class. -/
def restrictedAperture (θ a : ℝ) (Z : WidthAtMost θ) : Prop := aperturePositivity a Z.1

/-- A bounded family of certificates on the restricted class. -/
def restrictedFamily {ι : Type*} (θ : ℝ) (a : ι → ℝ) (Z : WidthAtMost θ) : Prop :=
  ∀ i : ι, aperturePositivity (a i) Z.1

theorem bddAbove_restrictedWidth_image {θ : ℝ} (s : Set (WidthAtMost θ)) :
    BddAbove (restrictedWidth θ '' s) :=
  ⟨θ, by rintro x ⟨Z, -, rfl⟩; exact Z.2⟩

/-- The depth-`θ` lattice at the Nyquist aperture `a` is a member of the class. -/
noncomputable def extremalMember {θ a : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2) (ha : 0 < a) :
    WidthAtMost θ :=
  ⟨offLineLattice (by linarith : (0 : ℝ) < 2 * a) hθ hθ',
    le_of_eq (width_offLineLattice (by linarith) hθ hθ')⟩

theorem restrictedWidth_extremalMember {θ a : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2) (ha : 0 < a) :
    restrictedWidth θ (extremalMember hθ hθ' ha) = θ :=
  width_offLineLattice (by linarith) hθ hθ'

theorem aperturePositivity_extremalMember {θ a : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2) (ha : 0 < a) :
    aperturePositivity a (extremalMember hθ hθ' ha).1 :=
  (offLineLattice_weil_positive_iff (by linarith) hθ hθ' a).mpr (by linarith)

/-! ### 2. The certificate is worth exactly the a priori bound -/

/-- **The relativised floor.** On the class of width at most `θ`, the aperture-`a` certificate has
resolution limit exactly `θ`. -/
theorem resolutionLimit_restrictedWidth_restrictedAperture {θ a : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 1 / 2) (ha : 0 < a) {Z : WidthAtMost θ} (hZ : restrictedAperture θ a Z) :
    resolutionLimit (restrictedWidth θ) (restrictedAperture θ a) Z = θ := by
  refine le_antisymm
    (csSup_le (shadow_image_nonempty (restrictedWidth θ) (restrictedAperture θ a) Z) ?_) ?_
  · rintro x ⟨W, -, rfl⟩
    exact W.2
  · have hmem : extremalMember hθ hθ' ha ∈ shadow (restrictedAperture θ a) Z :=
      propext (iff_of_true (aperturePositivity_extremalMember hθ hθ' ha) hZ)
    have hle := le_csSup (bddAbove_restrictedWidth_image
      (shadow (restrictedAperture θ a) Z)) ⟨_, hmem, rfl⟩
    rwa [restrictedWidth_extremalMember hθ hθ' ha] at hle

/-- **A certificate never improves an a priori bound.** -/
theorem certifies_restrictedWidth_iff {θ a : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2) (ha : 0 < a)
    {Z : WidthAtMost θ} (hZ : restrictedAperture θ a Z) {β : ℝ} :
    Certifies (restrictedWidth θ) (restrictedAperture θ a) Z β ↔ θ ≤ β := by
  rw [certifies_iff_resolutionLimit_le (bddAbove_restrictedWidth_image _),
    resolutionLimit_restrictedWidth_restrictedAperture hθ hθ' ha hZ]

/-- The same for an arbitrary family of apertures bounded by `A`. -/
theorem resolutionLimit_restrictedWidth_restrictedFamily {ι : Type*} {θ A : ℝ} (a : ι → ℝ)
    (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2) (hA : 0 < A) (hbd : ∀ i : ι, a i ≤ A)
    {Z : WidthAtMost θ} (hZ : restrictedFamily θ a Z) :
    resolutionLimit (restrictedWidth θ) (restrictedFamily θ a) Z = θ := by
  refine le_antisymm
    (csSup_le (shadow_image_nonempty (restrictedWidth θ) (restrictedFamily θ a) Z) ?_) ?_
  · rintro x ⟨W, -, rfl⟩
    exact W.2
  · have hfam : restrictedFamily θ a (extremalMember hθ hθ' hA) := fun i =>
      aperturePositivity_mono (hbd i) (aperturePositivity_extremalMember hθ hθ' hA)
    have hmem : extremalMember hθ hθ' hA ∈ shadow (restrictedFamily θ a) Z :=
      propext (iff_of_true hfam hZ)
    have hle := le_csSup (bddAbove_restrictedWidth_image
      (shadow (restrictedFamily θ a) Z)) ⟨_, hmem, rfl⟩
    rwa [restrictedWidth_extremalMember hθ hθ' hA] at hle

/-- **The floor is the a priori bound.** For every a priori width bound `θ`, every aperture and
every bounded family of apertures, the certificate's limit is exactly `θ`: the admissibility layer
returns the information it was given. -/
theorem theFloorIsTheAPrioriBound {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2) :
    ∀ a : ℝ, 0 < a → ∀ Z : WidthAtMost θ, restrictedAperture θ a Z →
      resolutionLimit (restrictedWidth θ) (restrictedAperture θ a) Z = θ ∧
        ∀ β : ℝ, Certifies (restrictedWidth θ) (restrictedAperture θ a) Z β ↔ θ ≤ β :=
  fun _ ha _ hZ =>
    ⟨resolutionLimit_restrictedWidth_restrictedAperture hθ hθ' ha hZ,
      fun _ => certifies_restrictedWidth_iff hθ hθ' ha hZ⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality

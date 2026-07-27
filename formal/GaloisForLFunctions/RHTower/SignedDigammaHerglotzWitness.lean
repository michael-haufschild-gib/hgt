import GaloisForLFunctions.RHTower.DigammaOrientationVerticalRigidityUniversalityLaw

/-!
# The Herglotz orientation exists, and is the only one

`SignedDigammaBooleanHerglotz` is consumed as a hypothesis by the vertical-rigidity layer but is
exhibited nowhere: the classification
`signedDigammaBooleanCompletion_nonneg_iff_allPositive` characterizes it as `ε = fun _ => false`, and
a characterization transfers the property without producing it.  The all-positive orientation is the
witness, so the layer's conclusions hold on an actual object and, by the same classification, on the
*only* object.

* **`signedDigammaBooleanHerglotz_allPositive`** — the witness;
* `signedDigammaBooleanHerglotz_iff_allPositive` — it is the unique one;
* **`verticalHeightMonotone_allPositive`**, `completion_eq_source_allPositive` — the layer's
  conclusions, premise-free.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- **The all-positive orientation is Herglotz.** -/
theorem signedDigammaBooleanHerglotz_allPositive :
    SignedDigammaBooleanHerglotz (fun _ => false) :=
  (signedDigammaBooleanCompletion_nonneg_iff_allPositive _).mpr rfl

/-- The Herglotz orientation is unique: it is exactly the all-positive one. -/
theorem signedDigammaBooleanHerglotz_iff_allPositive (ε : ℕ → Bool) :
    SignedDigammaBooleanHerglotz ε ↔ ε = fun _ => false :=
  signedDigammaBooleanCompletion_nonneg_iff_allPositive ε

/-- **Vertical height monotonicity, with no Herglotz premise.** -/
theorem verticalHeightMonotone_allPositive :
    SignedDigammaBooleanVerticalHeightMonotone (fun _ => false) :=
  signedDigammaBooleanCompletion_verticalHeightMonotone_of_herglotz
    signedDigammaBooleanHerglotz_allPositive

/-- **The exact closed form, with no Herglotz premise.** -/
theorem completion_eq_source_allPositive {w : ℂ}
    (hw : ∀ n : ℕ, w + (1 / 2 : ℂ) ≠ -(n : ℂ)) :
    signedDigammaBooleanCompletion (fun _ => false) w = explicitDigammaHerglotzSource w :=
  signedDigammaBooleanCompletion_eq_source_of_herglotz
    signedDigammaBooleanHerglotz_allPositive hw

/-- The universality law on the orientation that realizes it. -/
theorem digammaOrientation_verticalRigidityUniversality_allPositive :
    (fun _ => false) = (fun _ => false : ℕ → Bool) ∧
      (∀ w : ℂ, (∀ n : ℕ, w + (1 / 2 : ℂ) ≠ -(n : ℂ)) →
        signedDigammaBooleanCompletion (fun _ => false) w = explicitDigammaHerglotzSource w) ∧
      SignedDigammaBooleanVerticalHeightMonotone (fun _ => false) :=
  (digammaOrientation_verticalRigidityUniversality _).mp signedDigammaBooleanHerglotz_allPositive

end GaloisForLFunctions.RHTower

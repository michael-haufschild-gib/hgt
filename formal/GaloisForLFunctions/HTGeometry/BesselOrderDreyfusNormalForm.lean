import GaloisForLFunctions.HTGeometry.BesselOrderDreyfusSeam

/-!
# The Bessel order function is outside the Dreyfus normal form, on every progression

The classification theorem for differentially algebraic solutions of a rational linear shift
equation outputs a finite rational-exponential representation on *some* positive integer
progression.  This file packages the growth contradiction into exactly that shape: neither the
real-order Schlaefli carrier nor its reflected intensity admits such a representation on *any*
progression, so neither can be the differentially algebraic solution the classification describes.

Everything here is unconditional.  The single arrow that is not — differential algebraicity implies
the normal form — is the classification theorem itself, and it is isolated as one hypothesis in the
final statement.
-/

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

/-- The output shape of the classification theorem: on some positive integer progression starting
beyond a threshold, the function has a finite rational-exponential representation. -/
def DreyfusProgressionNormalForm (x₀ : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, x₀ ≤ x → ∃ ell : ℕ, 1 ≤ ell ∧
    HasRationalExponentialProgressionRepresentation
      (fun n : ℕ => ((f (x + (ell * n : ℕ)) : ℝ) : ℂ))

/-- **The Bessel order carrier is outside the normal form.** -/
theorem not_dreyfusProgressionNormalForm_realModifiedBesselKOrder {s : ℝ} (hs : 0 < s) :
    ¬ DreyfusProgressionNormalForm 1 (realModifiedBesselKOrder s) := by
  intro h
  obtain ⟨ell, hell, hrep⟩ := h 1 le_rfl
  exact realModifiedBesselKOrder_not_rationalExponentialPeriodicProgression hs le_rfl hell hrep

/-- **The reflected intensity is outside the normal form.** -/
theorem not_dreyfusProgressionNormalForm_realModifiedBesselOrderIntensity {s : ℝ} (hs : 0 < s) :
    ¬ DreyfusProgressionNormalForm 3
      (fun y => realModifiedBesselKOrder s y * realModifiedBesselKOrder s (y - 2)) := by
  intro h
  obtain ⟨ell, hell, hrep⟩ := h 3 le_rfl
  refine realModifiedBesselOrderIntensity_not_rationalExponentialPeriodicProgression
    (x := 3) hs le_rfl hell ?_
  refine hrep.imp fun m hm => ?_
  exact hm

/-- **The reduction.**  Whatever notion of differential algebraicity the classification theorem is
stated for, once it delivers the normal form the Bessel order carrier is not differentially
algebraic. -/
theorem not_differentiallyAlgebraic_realModifiedBesselKOrder_of_classification
    {s : ℝ} (hs : 0 < s) {DA : (ℝ → ℝ) → Prop}
    (hclass : ∀ f : ℝ → ℝ, DA f → DreyfusProgressionNormalForm 1 f) :
    ¬ DA (realModifiedBesselKOrder s) :=
  fun hda => not_dreyfusProgressionNormalForm_realModifiedBesselKOrder hs
    (hclass _ hda)

/-- The same reduction for the reflected intensity. -/
theorem not_differentiallyAlgebraic_realModifiedBesselOrderIntensity_of_classification
    {s : ℝ} (hs : 0 < s) {DA : (ℝ → ℝ) → Prop}
    (hclass : ∀ f : ℝ → ℝ, DA f → DreyfusProgressionNormalForm 3 f) :
    ¬ DA (fun y => realModifiedBesselKOrder s y * realModifiedBesselKOrder s (y - 2)) :=
  fun hda => not_dreyfusProgressionNormalForm_realModifiedBesselOrderIntensity hs
    (hclass _ hda)

end

end HTGeometry

end GaloisForLFunctions

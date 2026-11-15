import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovFiniteFrames
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Volume and relative intersections of polynomial frames

Every coordinate realization of the centered degree-bounded polynomial
frame preserves Lebesgue measure. Intersections of two framed sets therefore
reduce exactly to intersections with the frame of parameter differences.
This is the change-of-variables step for Parsell–Vinogradov covering boxes.
-/

open MeasureTheory

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section
variable {ι κ : Type*} [Fintype ι] {d : ℕ}

/-- Finite coordinates always exist; no choice of a special monomial ordering is needed. -/
def jetCoordinates (ι : Type*) [Fintype ι] (d : ℕ) :
    Jet ι d ≃ₗ[ℝ] (Fin (Module.finrank ℝ (Jet ι d)) → ℝ) :=
  (Module.finBasis ℝ (Jet ι d)).equivFun

/-- The polynomial frame expressed in any finite system of linear coordinates. -/
def coordinateFrame (e : Jet ι d ≃ₗ[ℝ] (κ → ℝ)) (θ : ι → ℝ) (t : ℝ) :
    (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ) :=
  (e.symm.trans (frameEquiv θ t d)).trans e

@[simp] theorem coordinateFrame_apply (e : Jet ι d ≃ₗ[ℝ] (κ → ℝ))
    (θ : ι → ℝ) (t : ℝ) (x : κ → ℝ) :
    coordinateFrame e θ t x = e (frame θ t d (e.symm x)) := rfl

/-- Coordinate changes leave the unit determinant unchanged. -/
theorem det_coordinateFrame (e : Jet ι d ≃ₗ[ℝ] (κ → ℝ)) (θ : ι → ℝ) (t : ℝ) :
    (coordinateFrame e θ t).toLinearMap.det = 1 := by
  change ((e : Jet ι d →ₗ[ℝ] (κ → ℝ)).comp
    ((frame θ t d).comp (e.symm : (κ → ℝ) →ₗ[ℝ] Jet ι d))).det = 1
  rw [LinearMap.det_conj, det_frame]

/-- Every set has the same volume in every polynomial frame. -/
theorem volume_coordinateFrame_image [Fintype κ] (e : Jet ι d ≃ₗ[ℝ] (κ → ℝ))
    (θ : ι → ℝ) (t : ℝ) (S : Set (κ → ℝ)) :
    volume (coordinateFrame e θ t '' S) = volume S := by
  have h := Measure.addHaar_image_linearMap volume (coordinateFrame e θ t).toLinearMap S
  simpa only [LinearEquiv.coe_coe, det_coordinateFrame, abs_one, ENNReal.ofReal_one, one_mul] using h

/-- Polynomial frames preserve the full measure, including nonmeasurable-set outer volumes. -/
theorem volume_coordinateFrame_preimage [Fintype κ] (e : Jet ι d ≃ₗ[ℝ] (κ → ℝ))
    (θ : ι → ℝ) (t : ℝ) (S : Set (κ → ℝ)) :
    volume (coordinateFrame e θ t ⁻¹' S) = volume S := by
  have hd : (coordinateFrame e θ t).toLinearMap.det ≠ 0 := by
    rw [det_coordinateFrame]
    exact one_ne_zero
  have h := Measure.addHaar_preimage_linearMap volume hd S
  simpa only [LinearEquiv.coe_coe, det_coordinateFrame, inv_one, abs_one,
    ENNReal.ofReal_one, one_mul] using h

/-- Frame composition adds both parameters after any coordinate choice. -/
theorem coordinateFrame_comp (e : Jet ι d ≃ₗ[ℝ] (κ → ℝ))
    (θ φ : ι → ℝ) (t s : ℝ) (x : κ → ℝ) :
    coordinateFrame e θ t (coordinateFrame e φ s x) =
      coordinateFrame e (θ + φ) (t + s) x := by
  simp only [coordinateFrame_apply, LinearEquiv.symm_apply_apply]
  exact congrArg e (DFunLike.congr_fun (frame_comp θ φ t s d) (e.symm x))

private theorem image_relative_intersection {X : Type*} (f g h : X → X)
    (hf : Function.Injective f) (hc : ∀ x, f (h x) = g x) (S T : Set X) :
    f '' (S ∩ h '' T) = f '' S ∩ g '' T := by
  rw [Set.image_inter hf, Set.image_image]
  have he : (fun x => f (h x)) = g := funext hc
  rw [he]

/-- Overlap volume depends only on the relative shear and translation parameters. -/
theorem volume_frame_intersection [Fintype κ] (e : Jet ι d ≃ₗ[ℝ] (κ → ℝ))
    (θ φ : ι → ℝ) (t s : ℝ) (S T : Set (κ → ℝ)) :
    volume (coordinateFrame e θ t '' S ∩ coordinateFrame e φ s '' T) =
      volume (S ∩ coordinateFrame e (φ - θ) (s - t) '' T) := by
  have hset : coordinateFrame e θ t '' (S ∩ coordinateFrame e (φ - θ) (s - t) '' T) =
      coordinateFrame e θ t '' S ∩ coordinateFrame e φ s '' T := by
    apply image_relative_intersection _ _ _ (coordinateFrame e θ t).injective
    intro x
    rw [coordinateFrame_comp, show θ + (φ - θ) = φ by abel,
      show t + (s - t) = s by ring]
  rw [← hset, volume_coordinateFrame_image]

#print axioms det_coordinateFrame
#print axioms volume_coordinateFrame_image
#print axioms volume_coordinateFrame_preimage
#print axioms volume_frame_intersection

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
